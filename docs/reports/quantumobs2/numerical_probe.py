"""Formula identity and deliberate-mutation controls; samples are not a proof."""
import cmath
import json
import math
import sys


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def entropy(x):
    return -sum(t * math.log(t) for t in x if t > 0)


mutate = '--mutate' in sys.argv
rows = []
for n in (2, 3, 4):
    for basis in ('identity', 'fourier'):
        u = [[complex(i == j) if basis == 'identity' else
              cmath.exp(2j * math.pi * i * j / n) / math.sqrt(n)
              for j in range(n)] for i in range(n)]
        for kind in ('pure', 'uniform', 'distinct'):
            x = ([float(j == 0) for j in range(n)] if kind == 'pure' else
                 [1/n] * n if kind == 'uniform' else
                 [(j+1)/(n*(n+1)/2) for j in range(n)])
            d = [[x[i] if i == j else 0 for j in range(n)] for i in range(n)]
            adj = [[u[j][i].conjugate() for j in range(n)] for i in range(n)]
            a = matmul(matmul(u, d), adj)
            p = [sum(abs(u[i][j])**2 * x[j] for j in range(n)) for i in range(n)]
            # Identity control: same source diagonal formula, same x,U, indices 0..n-1.
            identity_error = max(abs(a[i][i] - p[i]) for i in range(n))
            assert identity_error < 1e-12
            diagonal = all(abs(a[i][j]) < 1e-12 for i in range(n) for j in range(n) if i != j)
            gain = entropy(p) - entropy(x)
            equal = abs(gain) < 1e-12
            claim = equal == ((not diagonal) if mutate else diagonal)
            rows.append(dict(n=n, basis=basis, spectrum=kind, identity_error=identity_error,
                             entropy_gain=gain, diagonal=diagonal, passed=claim))
print(json.dumps(dict(index_offset=0, source='observer-quantum-v1 atom 7cf7cc560a5780a2a4caff1e3e7e9f36a495738063c78159f71d871d15e9b29b',
                      identity_control='diagonal of U diag(x) U* equals norm-square weighted spectrum',
                      source_data_table=False, mutation=mutate, cases=rows), indent=2))
sys.exit(0 if all(r['passed'] for r in rows) else 1)
