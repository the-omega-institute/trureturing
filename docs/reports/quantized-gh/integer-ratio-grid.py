from fractions import Fraction as Q
from hashlib import sha256
from importlib.metadata import version
from itertools import product
import json
from pathlib import Path
from flint import arb, ctx

assert version("python-flint") == "0.8.0"
ctx.prec = 256


def b(q):
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


def f(x):
    return (1 - (-x).exp()).log()


scale = Q(10, 11211)
rows = [(11100*scale, 11322*scale),
        (11165*scale, 11368*scale),
        (11165*scale, 11368*scale)]
assert [c/(d-c) for c, d in rows] == [50, 55, 55]
m1 = Q(30)
m0 = m1 - Q(3, 10**6)
mu0, mu = m0/3, m1/3
inventory = []
for bits in product((0, 1), repeat=3):
    xs = [row[bit] for row, bit in zip(rows, bits)]
    total = sum(xs)
    inventory.append({"bits": "".join(map(str, bits)),
                      "sum": str(total), "feasible": m0 <= total <= m1})
assert [x["bits"] for x in inventory if x["feasible"]] == ["001", "010"]
assert all(0 < c < mu0 < mu < d for c, d in rows)
v0 = sum(min(mu0-c, d-mu)**2 for c, d in rows)
widths = [d-c for c, d in rows]
theta = (m1-sum(c for c, d in rows))/widths[0]
assert theta == Q(203, 222)
slopes = [(f(b(d))-f(b(c)))/b(d-c) for c, d in rows]
assert slopes[0] > slopes[1] and slopes[0] > slopes[2]
dual = (b(1-theta)*f(b(rows[0][0])) + b(theta)*f(b(rows[0][1]))
        + f(b(rows[1][0])) + f(b(rows[2][0])))
r = (b(v0)/6).sqrt()
psi = f(b(mu)+2*r) + 2*f(b(mu)-r)
gap = dual-psi
assert gap > 0
assert b(Q(1, 10**10)) < gap < b(Q(1, 10**9))
result = {
    "status": "pass", "scope": "one hand-derived integer-ratio real grid",
    "candidate_search": False, "configurations_verified": 8,
    "python_flint": version("python-flint"), "arb_precision_bits": ctx.prec,
    "rows": [[str(c), str(d)] for c, d in rows],
    "coordinate_sum_slab": [str(m0), str(m1)],
    "integer_lower_endpoint_ratios": [50, 55, 55],
    "theta": str(theta), "V0": str(v0), "inventory": inventory,
    "classification_sha256": sha256(json.dumps(inventory, sort_keys=True,
                                               separators=(",", ":")).encode()).hexdigest(),
    "strict_gap_bounds": ["1/10000000000", "1/1000000000"],
    "gap_approximation_not_certificate": str(gap),
    "optimality": "row-1 secant, other slopes strictly smaller, matching mixture",
    "prime_grid": False,
    "limitations": "Widths are rational, not certified log primes; rows 2 and 3 coincide.",
    "program_sha256": sha256(Path(__file__).read_bytes()).hexdigest()
}
print(json.dumps(result, indent=2))

