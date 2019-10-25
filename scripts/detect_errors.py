import itertools
import sys

for line in sys.stdin:
    sys.stderr.write(line)
    if 'error' in line:
        for line in itertools.islice(sys.stdin, 20):
            sys.stderr.write(line)
        sys.exit(1)
