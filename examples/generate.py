import csv

def run(filename):
    N = 1000000
    with open(filename,'w') as fp:
        w = csv.writer(fp)
        w.writerow(['type', 'client', 'tx', 'amount'])
        for i in range(0, N):
            w.writerow(["deposit", "1", i, 2.0])
        for i in range(0, N):
            w.writerow(["deposit", "2", i, 2.0])
        for i in range(0, N):
            w.writerow(["withdrawal", "1", i, 2.0])


if __name__ == '__main__':
    import sys
    run(sys.argv[1])


