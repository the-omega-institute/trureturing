from fractions import Fraction
from hashlib import sha256
from importlib.metadata import version
from itertools import product
import json
import platform
from flint import arb, ctx

assert version('python-flint') == '0.8.0'
ctx.prec = 256


def ball(q):
    q = Fraction(q)
    return arb(q.numerator) / arb(q.denominator)


def f(x):
    return (1 - (-x).exp()).log()


rows = [(Fraction(99, 10), Fraction(101, 10)),
        (Fraction(249, 25), Fraction(507, 50)),
        (Fraction(249, 25), Fraction(507, 50))]
q0, q1 = Fraction(29999997, 1000000), Fraction(30)
mu0, mu = q0 / 3, q1 / 3
assert mu0 == Fraction(9999999, 1000000) and mu == 10
assert all(0 < c < mu0 < mu < d for c, d in rows)
distances = [min(mu0 - c, d - mu) for c, d in rows]
assert distances == [Fraction(99999, 10**6),
                     Fraction(39999, 10**6), Fraction(39999, 10**6)]
v0 = sum(d*d for d in distances)
assert v0 == Fraction(13199640003, 10**12) and 0 < v0 < 6*mu*mu

inventory = []
feasible = []
for bits in product((0, 1), repeat=3):
    xs = tuple(rows[i][bits[i]] for i in range(3))
    total = sum(xs)
    inside = q0 <= total <= q1
    inventory.append({'bits': ''.join(map(str, bits)),
                      'coordinates': list(map(str, xs)),
                      'sum': str(total), 'slab_feasible': inside})
    if inside:
        feasible.append(xs)
expected_sums = [Fraction(1491, 50), Fraction(30), Fraction(30),
                 Fraction(1509, 50), Fraction(1501, 50), Fraction(151, 5),
                 Fraction(151, 5), Fraction(1519, 50)]
assert [Fraction(row['sum']) for row in inventory] == expected_sums
assert len(inventory) == 8
assert feasible == [(rows[0][0], rows[1][0], rows[2][1]),
                    (rows[0][0], rows[1][1], rows[2][0])]

widths = [d-c for c, d in rows]
base_sum = sum(c for c, d in rows)
budget = q1-base_sum
theta = budget/widths[0]
assert widths == [Fraction(1, 5), Fraction(9, 50), Fraction(9, 50)]
assert budget == Fraction(9, 50) and theta == Fraction(9, 10)
support_sums = [base_sum, base_sum+widths[0]]
assert support_sums == [Fraction(1491, 50), Fraction(1501, 50)]
assert all(not (q0 <= total <= q1) for total in support_sums)
assert (1-theta)*support_sums[0]+theta*support_sums[1] == q1
means = [rows[0][0]+theta*widths[0], rows[1][0], rows[2][0]]
assert means == [Fraction(252, 25), Fraction(249, 25), Fraction(249, 25)]
assert sum(means) == 3*mu
vbar = sum((y-mu)**2 for y in means)
assert vbar == Fraction(6, 625) and vbar < v0
assert distances[0]**2 > Fraction(2, 3)*v0

fc = [f(ball(c)) for c, d in rows]
fd = [f(ball(d)) for c, d in rows]
slopes = [(fd[i]-fc[i])/ball(widths[i]) for i in range(3)]
lam = 5*(fd[0]-fc[0])
assert lam > 0 and slopes[1] < lam and slopes[2] < lam
# Row 1 ties by definition; the other rows uniquely select their lower ends.
price_value = lam*ball(q1) + sum((fc[i]-lam*ball(rows[i][0])
                                for i in range(3)), arb(0))
dual = ball(1-theta)*fc[0]+ball(theta)*fd[0]+fc[1]+fc[2]
r = (ball(v0)/6).sqrt()
lower, upper = ball(mu)-r, ball(mu)+2*r
assert lower > 0
psi = f(upper)+2*f(lower)

scale = 10**18
claimed = {'variance_bound': (-136498016563252, -136498016563251),
           'optimal_dual': (-136497658176917, -136497658176916),
           'gap': (358386335, 358386336)}
values = {'variance_bound': psi, 'optimal_dual': dual, 'gap': dual-psi}
bounds = {name: (Fraction(lo, scale), Fraction(hi, scale))
          for name, (lo, hi) in claimed.items()}
for name, value in values.items():
    lo, hi = bounds[name]
    assert lo < hi
    assert ball(lo) < value and value < ball(hi), name
# Supplemental enclosure of the analytically equal price expression.
lo, hi = bounds['optimal_dual']
assert ball(lo) < price_value and price_value < ball(hi)
assert bounds['variance_bound'][1] < bounds['optimal_dual'][0]
assert bounds['gap'][0] > 0 and dual > psi
classification = json.dumps(inventory, sort_keys=True, separators=(',', ':'))
print(json.dumps({
    'status': 'pass', 'scope': 'one fixed artificial positive real grid',
    'python': platform.python_version(), 'python_flint': version('python-flint'),
    'arb_precision_bits': ctx.prec,
    'configurations_verified': len(inventory), 'feasible_count': len(feasible),
    'inventory': inventory,
    'classification_sha256': sha256(classification.encode('utf-8')).hexdigest(),
    'V0': str(v0), 'Vbar': str(vbar), 'theta': str(theta),
    'support_sums': list(map(str, support_sums)), 'expected_sum': str(q1),
    'strict_slope_comparisons': ['rho_2 < lambda', 'rho_3 < lambda'],
    'row_1_tie': 'algebraic: lambda*(d1-c1) = f(d1)-f(c1)',
    'lp_equality': 'analytical matching primal mixture and price certificate',
    'strict_enclosures_denominator': str(scale),
    'strict_enclosures_numerators': claimed,
    'strict_order': 'variance_bound < optimal_dual',
    'prime_domain_result': 'OPEN', 'candidate_search': False
}, indent=2))
