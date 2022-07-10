use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error;
use std::fs;
use std::io;
use std::ops::{Deref, DerefMut};
use std::process;
use std::time::{Duration, Instant};
use thiserror::Error;

#[derive(Error, Debug, Clone)]
enum CliError {
    #[error("Invalid number of args")]
    InvalidArgs,
    #[error("Invalid Transaction Type: {0}")]
    InvalidTransactionType(String),
}

const FIXED_MULTIPLIER: f64 = 10_000.0; // 4 decimal places

type ClientIndex = u16;
type TxIndex = u32;
type FixedAmount = u64;
type Transactions = HashMap<TxIndex, Transaction>;

struct Accounts(Vec<Option<Account>>);

impl Accounts {
    fn new() -> Self {
        let accounts = std::iter::repeat_with(|| None::<Account>)
            .take(ClientIndex::MAX as usize)
            .collect::<Vec<_>>();
        Self(accounts)
    }

    fn output_csv(self) -> Result<(), Box<dyn error::Error>> {
        let mut writer = csv::Writer::from_writer(io::stdout());
        for (inx, maybe_account) in self.0.into_iter().enumerate() {
            if let Some(account) = maybe_account {
                let o = OutputRecord {
                    client: inx as ClientIndex,
                    available: format_fixed(account.available),
                    held: format_fixed(account.held),
                    total: format_fixed(account.held.checked_add(account.available).unwrap()),
                    locked: account.locked,
                };
                writer.serialize(o)?;
            }
        }
        writer.flush()?;
        Ok(())
    }
}

impl Deref for Accounts {
    type Target = Vec<Option<Account>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Accounts {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

enum AccountEvent {
    Deposit(TxIndex, FixedAmount),

    // we don't need the transaction id or client id for withdrawl
    Withdrawal(TxIndex, FixedAmount),

    // These events do not include amounts
    Resolve(TxIndex),
    Dispute(TxIndex),
    Chargeback(TxIndex),
}

#[derive(Clone, Debug, Deserialize)]
struct InputRecord {
    #[serde(rename = "type")]
    tx_type: String,
    client: ClientIndex,
    tx: TxIndex,
    amount: f64,
}

impl InputRecord {
    fn into_event(self) -> Result<AccountEvent, CliError> {
        match self.tx_type.as_str() {
            "withdrawal" => Ok(AccountEvent::Withdrawal(self.tx, to_fixed(self.amount))),
            "deposit" => Ok(AccountEvent::Deposit(self.tx, to_fixed(self.amount))),
            "dispute" => Ok(AccountEvent::Dispute(self.tx)),
            "resolve" => Ok(AccountEvent::Resolve(self.tx)),
            "chargeback" => Ok(AccountEvent::Chargeback(self.tx)),
            _ => Err(CliError::InvalidTransactionType(self.tx_type.into())),
        }
    }
}

#[derive(Debug, PartialEq)]
enum TransactionType {
    Deposit,
    Withdrawal,
}

#[derive(Debug, PartialEq)]
enum DisputeStatus {
    Disputed,
    Normal,
}

#[derive(Debug)]
struct Transaction {
    tx_type: TransactionType,
    status: DisputeStatus,
    client: ClientIndex,
    amount: FixedAmount,
}
impl Transaction {
    fn new(tx_type: TransactionType, client: ClientIndex, amount: FixedAmount) -> Self {
        Self {
            tx_type,
            status: DisputeStatus::Normal,
            client,
            amount,
        }
    }
}

// Because client id is u16, we have 2^16 possible clients
// Each Account is about 2*4+1=9 bytes in size
// Total potential memory requirements of 13*2^16=576kB
// This grows to 36GB for u32
#[derive(Debug)]
struct Account {
    available: FixedAmount,
    held: FixedAmount,
    locked: bool,
}
impl Account {
    fn new() -> Self {
        Self {
            available: 0,
            held: 0,
            locked: false,
        }
    }
}

#[derive(Debug, PartialEq)]
enum TransactionResult {
    AccountUpdated,
    NSF,
    Locked,
    AlreadyDisputed,
    NotDisputed,
    Invalid,
    InvalidTransaction,
    InvalidClient,
    InvalidDisputeOfWithdrawal,
    DuplicateTransaction,
    InternalError,
}

#[derive(Debug, Serialize)]
struct OutputRecord {
    #[serde(rename = "client")]
    client: ClientIndex,
    available: String,
    held: String,
    total: String,
    locked: bool,
}

fn format_fixed(u: FixedAmount) -> String {
    format!("{:.4}", u as f64 / FIXED_MULTIPLIER)
}

fn to_fixed(f: f64) -> FixedAmount {
    (f * FIXED_MULTIPLIER).round() as FixedAmount
}

fn transaction(
    record: InputRecord,
    accounts: &mut Accounts,
    txs: &mut Transactions,
) -> TransactionResult {
    let client_id = record.client;
    let client_inx = record.client as usize;
    match record.into_event() {
        Ok(event) => {
            // load account record, it must exist because we pre-allocated it
            let maybe_account = accounts.get_mut(client_inx).unwrap();
            match maybe_account {
                Some(account) => process_event(account, event, client_id, txs),
                None => {
                    // if the account doesn't exist, then we create it
                    let mut account = Account::new();
                    let result = process_event(&mut account, event, client_id, txs);
                    maybe_account.replace(account);
                    result
                }
            }
        }
        Err(err) => {
            // Invalid event
            log::error!("{}", err);
            TransactionResult::Invalid
        }
    }
}

fn process_event(
    account: &mut Account,
    event: AccountEvent,
    client: ClientIndex,
    txs: &mut Transactions,
) -> TransactionResult {
    match event {
        AccountEvent::Deposit(tx_id, fixed) => {
            // save the transaction, if it doesn't already exist
            if txs.contains_key(&tx_id) {
                TransactionResult::DuplicateTransaction
            } else {
                txs.insert(
                    tx_id,
                    Transaction::new(TransactionType::Deposit, client, fixed),
                );
                // we allow a deposit, even if it's locked
                account.available = account.available.checked_add(fixed).unwrap();
                TransactionResult::AccountUpdated
            }
        }

        AccountEvent::Withdrawal(tx_id, fixed) => {
            if txs.contains_key(&tx_id) {
                return TransactionResult::DuplicateTransaction;
            }

            if account.locked {
                return TransactionResult::Locked;
            }

            if account.available < fixed {
                return TransactionResult::NSF;
            }

            account.available = account.available.checked_sub(fixed).unwrap();
            txs.insert(
                tx_id,
                Transaction::new(TransactionType::Withdrawal, client, fixed),
            );
            TransactionResult::AccountUpdated
        }

        AccountEvent::Dispute(tx_id) => {
            match txs.get_mut(&tx_id) {
                Some(tx) => {
                    if tx.tx_type != TransactionType::Deposit {
                        return TransactionResult::InvalidDisputeOfWithdrawal;
                    }

                    // ensure client matches
                    if tx.client != client {
                        return TransactionResult::InvalidClient;
                    }

                    // ensure not already disputed
                    if tx.status != DisputeStatus::Normal {
                        return TransactionResult::AlreadyDisputed;
                    }

                    // update by the transaction amount
                    account.available = account.available.checked_sub(tx.amount).unwrap();
                    account.held = account.held.checked_add(tx.amount).unwrap();
                    tx.status = DisputeStatus::Disputed;
                    TransactionResult::AccountUpdated
                }
                None => TransactionResult::InvalidTransaction,
            }
        }

        AccountEvent::Chargeback(tx_id) => {
            match txs.get(&tx_id) {
                Some(tx) => {
                    if tx.tx_type != TransactionType::Deposit {
                        return TransactionResult::InvalidDisputeOfWithdrawal;
                    }

                    // ensure client matches
                    if tx.client != client {
                        return TransactionResult::InvalidClient;
                    }

                    // ensure disputed
                    if tx.status != DisputeStatus::Disputed {
                        return TransactionResult::NotDisputed;
                    }

                    // ensure sufficient funds
                    if account.held < tx.amount {
                        // This should never happen
                        log::error!("not enough held");
                        return TransactionResult::InternalError;
                    }

                    // tx must exist
                    account.held = account.held.checked_sub(tx.amount).unwrap();
                    // account is immediately frozen
                    account.locked = true;
                    // only remove when we have properly validated
                    txs.remove(&tx_id).unwrap();
                    TransactionResult::AccountUpdated
                }
                None => TransactionResult::InvalidTransaction,
            }
        }

        AccountEvent::Resolve(tx_id) => {
            match txs.get(&tx_id) {
                Some(tx) => {
                    if tx.tx_type != TransactionType::Deposit {
                        return TransactionResult::InvalidDisputeOfWithdrawal;
                    }

                    // ensure client matches
                    if tx.client != client {
                        return TransactionResult::InvalidClient;
                    }

                    // ensure disputed
                    if tx.status != DisputeStatus::Disputed {
                        return TransactionResult::NotDisputed;
                    }

                    // ensure sufficient funds
                    if account.held < tx.amount {
                        // This should never happen
                        log::error!("not enough held");
                        return TransactionResult::InternalError;
                    }

                    account.held = account.held.checked_sub(tx.amount).unwrap();
                    account.available = account.available.checked_add(tx.amount).unwrap();
                    // tx must exist
                    txs.remove(&tx_id).unwrap();
                    TransactionResult::AccountUpdated
                }
                None => TransactionResult::InvalidTransaction,
            }
        }
    }
}

fn run() -> Result<(), Box<dyn error::Error>> {
    let start = Instant::now();

    let filename = std::env::args().nth(1).ok_or(CliError::InvalidArgs)?;
    log::info!("Processing {}", filename);
    let f = fs::File::open(filename)?;
    let reader = io::BufReader::new(f);
    let mut csv_reader = csv::ReaderBuilder::new()
        .trim(csv::Trim::All)
        .from_reader(reader);

    let mut txs = Transactions::new();

    let mut accounts = Accounts::new();

    let mut count: usize = 0;
    for result in csv_reader.deserialize() {
        transaction(result?, &mut accounts, &mut txs);
        count += 1;
    }

    accounts.output_csv()?;
    log::info!(
        "Transactions per second: {}",
        (count as f64) / start.elapsed().as_secs_f64()
    );
    Ok(())
}

fn main() {
    env_logger::init();
    if let Err(err) = run() {
        log::error!("{}", err);
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deposit(client: ClientIndex, tx: TxIndex, amount: f64) -> InputRecord {
        InputRecord {
            tx_type: "deposit".into(),
            client,
            tx,
            amount,
        }
    }

    fn withdrawal(client: ClientIndex, tx: TxIndex, amount: f64) -> InputRecord {
        InputRecord {
            tx_type: "withdrawal".into(),
            client,
            tx,
            amount,
        }
    }

    fn dispute(client: ClientIndex, tx: TxIndex) -> InputRecord {
        InputRecord {
            tx_type: "dispute".into(),
            client,
            tx,
            amount: 0.,
        }
    }

    fn resolve(client: ClientIndex, tx: TxIndex) -> InputRecord {
        InputRecord {
            tx_type: "resolve".into(),
            client,
            tx,
            amount: 0.,
        }
    }

    fn chargeback(client: ClientIndex, tx: TxIndex) -> InputRecord {
        InputRecord {
            tx_type: "chargeback".into(),
            client,
            tx,
            amount: 0.,
        }
    }

    fn get_account(client: ClientIndex, accounts: &Accounts) -> Option<&Account> {
        accounts.get(client as usize).unwrap().as_ref()
    }

    #[test]
    fn nsf() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);
        assert_eq!(
            TransactionResult::NSF,
            transaction(withdrawal(1, 2, 2.1), &mut accounts, &mut txs)
        );
        // no change
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);
    }

    #[test]
    fn test_withdrawal() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(withdrawal(1, 2, 1.0), &mut accounts, &mut txs)
        );
        assert_eq!(1000, get_account(1, &accounts).unwrap().available);

        // try to dispute a withdrawal
        assert_eq!(
            TransactionResult::InvalidDisputeOfWithdrawal,
            transaction(dispute(1, 2), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidDisputeOfWithdrawal,
            transaction(chargeback(1, 2), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidDisputeOfWithdrawal,
            transaction(resolve(1, 2), &mut accounts, &mut txs)
        );
    }

    #[test]
    fn invalid_tx() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::InvalidTransaction,
            transaction(dispute(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidTransaction,
            transaction(chargeback(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidTransaction,
            transaction(resolve(1, 1), &mut accounts, &mut txs)
        );
    }

    #[test]
    fn duplicate_deposit() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::DuplicateTransaction,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::DuplicateTransaction,
            transaction(withdrawal(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);
    }

    #[test]
    fn test_resolve() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();

        // two deposits for two customers
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(2, 2, 2.2), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);

        // dispute the first
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(dispute(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().held);

        // try to dispute again
        assert_eq!(
            TransactionResult::AlreadyDisputed,
            transaction(dispute(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().held);

        // now dispute the second transaction with the first client
        // make sure nothing changes
        assert_eq!(
            TransactionResult::InvalidClient,
            transaction(dispute(2, 1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidClient,
            transaction(chargeback(2, 1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::InvalidClient,
            transaction(resolve(2, 1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().held);
        assert_eq!(22000, get_account(2, &accounts).unwrap().available);

        // finally do the resolve
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(resolve(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);
        assert_eq!(0, get_account(1, &accounts).unwrap().held);
    }

    #[test]
    fn test_chargeback() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().available);

        // try to chargeback before disputing, won't work
        assert_eq!(
            TransactionResult::NotDisputed,
            transaction(chargeback(1, 1), &mut accounts, &mut txs)
        );

        // try to resolve before disputing, won't work
        assert_eq!(
            TransactionResult::NotDisputed,
            transaction(resolve(1, 1), &mut accounts, &mut txs)
        );

        // dispute it now
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(dispute(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(11000, get_account(1, &accounts).unwrap().held);
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 2, 2.1), &mut accounts, &mut txs)
        );
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(chargeback(1, 1), &mut accounts, &mut txs)
        );
        assert_eq!(0, get_account(1, &accounts).unwrap().held);
        assert_eq!(21000, get_account(1, &accounts).unwrap().available);
        assert!(get_account(1, &accounts).unwrap().locked);

        // locked and no change to available
        assert_eq!(
            TransactionResult::Locked,
            transaction(withdrawal(1, 3, 1.1), &mut accounts, &mut txs)
        );
        assert_eq!(21000, get_account(1, &accounts).unwrap().available);
    }

    #[test]
    fn test_output() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        assert_eq!(
            TransactionResult::AccountUpdated,
            transaction(deposit(1, 1, 1.1), &mut accounts, &mut txs)
        );
        accounts.output_csv().unwrap();
    }

    #[test]
    fn invalid_record() {
        let mut txs = Transactions::new();
        let mut accounts = Accounts::new();
        let r = InputRecord {
            tx_type: "invalid".into(),
            client: 1,
            tx: 1,
            amount: 0.,
        };
        assert!(r.clone().into_event().is_err());
        assert_eq!(
            TransactionResult::Invalid,
            transaction(r, &mut accounts, &mut txs)
        );
    }
}
