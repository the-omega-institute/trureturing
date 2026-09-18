"""Independent literal recurrence and formal-series long division, issue #8627."""
from fractions import Fraction as F
from itertools import product
from random import Random
import json
from pathlib import Path

TERMS = 48

def recurrence(m, a):
    row = [F(1), *a]  # source time -1
    out = [row]
    for _ in range(TERMS - 1):
        row = [row[-1], *(row[j] + m[j] * row[-1] for j in range(len(m)))]
        out.append(row)
    return out

def divide(num, den):
    out = []
    for n in range(TERMS):
        out.append((num.get(n, F(0)) - sum(den.get(i, F(0)) * out[n-i]
                    for i in range(1, min(n, max(den)) + 1))) / den[0])
    return out

def check(m, a):
    d = len(m)
    den = {0: F(1), d+1: F(-1)}
    p, q = {0: F(1)}, {d: F(1)}
    for j in range(d):
        den[d-j] = -m[j]
        p[d-j] = a[j] - m[j]
        q[d-1-j] = a[j]
    rows = recurrence(m, a)
    for label, actual, expected in [('R_0', [r[0] for r in rows], divide(p, den)),
                                    ('R_last', [r[-1] for r in rows], divide(q, den))]:
        for n, (x, y) in enumerate(zip(actual, expected)):
            if x != y:
                return dict(d=d, m=list(map(str,m)), a=list(map(str,a)), identity=label,
                            coefficient=n, actual=str(x), expected=str(y))
    if d == 2:
        # Source p.12 independently printed, proved middle-coordinate formula.
        k, mm = m
        aa, b = a
        middle = {0: aa, 1: 1+k*b-mm*aa, 2: b-mm}
        assert [r[1] for r in rows] == divide(middle, den)
    return None

rng = Random(862720260918)
counts, failures = {}, []
for d in range(1, 9):
    cases = []
    if d <= 3:
        cases += [(list(map(F, v[:d])), list(map(F, v[d:])))
                  for v in product((-1,0,1), repeat=2*d)]
    for _ in range(256):
        cases.append(([F(rng.randint(-8,8),rng.randint(1,7)) for _ in range(d)],
                      [F(rng.randint(-8,8),rng.randint(1,7)) for _ in range(d)]))
    for m, a in cases:
        failure = check(m,a)
        if failure:
            failures.append(failure)
    counts[d] = len(cases)
assert check([],[]) is None
result = dict(range='d=1..8; exhaustive {-1,0,1}^(2d) for d=1..3; 256 rational cases/d, numerators -8..8, denominators 1..7; coefficients 0..47; seed 862720260918',
              cases=sum(counts.values()), per_d=counts, failures=failures,
              coefficient_equalities=2*TERMS*sum(counts.values()),
              controls='d=2: printed R_2 formula checked for all 337 cases; d=0: both identities checked separately')
Path('probe/python-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
assert not failures
