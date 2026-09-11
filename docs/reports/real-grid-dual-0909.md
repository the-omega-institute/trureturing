# Artificial real grid: exact dual and bounded Arb verification

Date: 2026-09-09. Scope: one supplied three-row positive real grid,
all eight fixed configurations, exactly two slab-feasible configurations.
This is bounded verification, with no candidate generation or search.
It supports sections 18-21 of
[ARITHMETIC_BOUNDARY_QUANTIZATION.md](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md).
The grid is not a prime-exponent ladder and gives no Robin certificate,
prime-domain counterexample, RH progress, infinite coverage or Lean freezing.

Provenance: caller-supplied completed browser-PRO task
`84963abe-485a-4093-901b-03acf69dc52e`, conversation `conv_fc5fcce44d2bc103`,
`company-chatgpt-pro` browser Work, actual returned model `GPT-6 Astra`,
completed `2026-09-08T15:45:56.133+00:00`. These identifiers differ from the
earlier task returned as `chatgpt-5.5-pro`. The two failed earlier tasks remain
failed. The caller's `consensus-rnd:sshx` implementation worker audited the
supplied argument and ran the persisted block below; it is repo-prior-exposed,
not an independent review seat. No sterile-prior or model-family diversity
claim is made. No opaque primary log or oracle transcript was opened.
Source base: `fa198bc9a4e5da392e3f2a6f826f73f2ea672c3c`.

The supporting caller program was read, not rerun:
`/tmp/qgh-boundaries-0908/caller-artificial-grid-check.py`, SHA256
`0f10208db13e24cf200762cbd33a7c49db20d1c047e088eebc86a2d339593f50`.
Its overlapping-ball assertion checks consistency only. The equality and
optimality certificate here is analytical; the program uses the known
maximizing endpoints and certifies the two strict slope comparisons.

## Exact Grid and Certificate

All logarithms are natural. Let `f(x)=log(1-exp(-x))` for `x>0`,
`C1={99/10,101/10}`, and `C2=C3={249/25,507/50}`. The coordinate-sum slab is
`[Q0,Q1]=[29999997/1000000,30]`. Its mean interval is
`I=[9999999/1000000,10]`, with upper mean `mu=10`.
The distances to the three two-point sets are
`(99999,39999,39999)/1000000`, so `V0=13199640003/10^12`.
Variance here means a sum of squared deviations, not their average.

For bits in row order, 0 selects the lower and 1 the upper endpoint:

| Bits | Coordinates | Exact Sum | Slab Feasible |
|---|---|---:|---|
| 000 | (99/10,249/25,249/25) | 1491/50 | no |
| 001 | (99/10,249/25,507/50) | 30 | yes |
| 010 | (99/10,507/50,249/25) | 30 | yes |
| 011 | (99/10,507/50,507/50) | 1509/50 | no |
| 100 | (101/10,249/25,249/25) | 1501/50 | no |
| 101 | (101/10,249/25,507/50) | 151/5 | no |
| 110 | (101/10,507/50,249/25) | 151/5 | no |
| 111 | (101/10,507/50,507/50) | 1519/50 | no |

The objective is `sum_i f(x_i)` with budget `sum_i x_i<=30`. Define the
discrete separable price dual by

\[
U_{\rm dual}=\inf_{\lambda\ge0}
\left\{30\lambda+\sum_{i=1}^3\max_{x\in C_i}[f(x)-\lambda x]\right\}.
\]

Take
`lambda=5*(f(101/10)-f(99/10))>0`. Row 1 ties algebraically:
`f(d1)-f(c1)-lambda*(d1-c1)=0` since `d1-c1=1/5`.
For rows 2 and 3, write the secant slope as
`integral_0^1 f'(c_i+t*(d_i-c_i)) dt`. Their arguments exceed the first row's
by `3/50-t/50>0` for every `0<=t<=1`. Since `f'(x)=1/(exp(x)-1)` is strictly
decreasing, both slopes are strictly smaller than `lambda`.
Thus their price maxima uniquely select the lower endpoints; either endpoint
maximizes the first row.

Mix 000 and 100 with probabilities `1/10` and `9/10`. The exact expected sum
is 30, but the support sums 29.82 and 30.02 are both outside the slab.
The matching price value is the identity

```text
lambda*30 + sum_i (f(c_i)-lambda*c_i)
  = sum_i f(c_i) + lambda*(9/50)
  = (1/10)*f(99/10) + (9/10)*f(101/10) + 2*f(249/25).
```

For every mixture with expected budget at most 30, the price expression is an
upper bound by weak duality. This particular mixture attains it, proving both
the LP maximum and the minimum price dual equal the displayed value `U_dual`.
No equality is inferred from ball overlap or numerical agreement.
The expectation constraint does not assert feasibility of each support point.

The mean vector is `(252/25,249/25,249/25)` and `Vbar=6/625<V0`.
The first row's squared distance is greater than `2*V0/3`.
Put `r=sqrt(V0/6)`, `L=10-r`, `H=10+2*r`; then `L>0` and
`Psi=f(H)+2*f(L)`. This is the variance envelope for this coordinate-sum slab.
In the prime setting, the coordinate sum would instead be
`T+sum_p log(p)` and the objective would include `log(E_S)`.
Neither arithmetic normalization is transferred to this artificial grid.
The three sufficient dominance conditions apply to positive real grids with
this normalization, but none of them holds for this example.

## Exact Enclosures

For each row below the true value lies strictly between the given numerators
divided by the exact integer `10^18`. These are the original supplied
enclosures, with no endpoint correction.

| Quantity | Lower Numerator | Upper Numerator |
|---|---:|---:|
| Psi | -136498016563252 | -136498016563251 |
| U_dual | -136497658176917 | -136497658176916 |
| U_dual-Psi | 358386335 | 358386336 |

The program uses `Fraction` for every input, configuration sum, distance,
probability and claimed endpoint. Arb evaluates exp, log and sqrt at 256 bits.
Strict ball comparisons certify the exact rational enclosures; the rational
endpoints also strictly separate `Psi` and `U_dual`. No approximate printed
ball is parsed. The primary conclusion described a separate rational Taylor
method; that method is not claimed as executed here. This report's numerical
trust includes Python, Python-FLINT and FLINT/Arb directed ball arithmetic.
The general proofs are paper arguments, not consequences of eight checks.

## Reproducible Calculation

Run this standalone block from any directory with `uv` available. It has no
repository or caller-file input. Python-FLINT is pinned to 0.8.0; precision is
256 bits. The classification digest hashes UTF-8 compact JSON with sorted
object keys over the eight inventory records, in lexicographic bit order.

```sh
uv run --no-project --python 3.12 --with python-flint==0.8.0 python - <<'PY'
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
PY
```

## Execution Record

The implementation worker executed this exact persisted shell block once,
starting `2026-09-08T16:22:23Z` and finishing `2026-09-08T16:22:24Z`
(2026-09-09 in Asia/Singapore), with exit code 0 and empty stderr.
Environment: Python 3.12.13, Python-FLINT 0.8.0, Arb 256 bits,
uv 0.10.12 (Homebrew 2026-03-19 aarch64-apple-darwin).

The Python program identity covers the exact bytes after the shell heredoc
header through the last Python newline, excluding the `PY` terminator.
The shell identity covers the full fenced block contents, including its final
newline, excluding the Markdown fences. Both are UTF-8 with LF newlines.

| Artifact | Bytes | SHA256 |
|---|---:|---|
| Python program | 4902 | `3853878433a4e33dcc070caca371d97c910599faa8530ad54feab6ec2897a3d2` |
| Shell block | 4982 | `d6f01558aa713a8447d810bc33679952412e0930594aab10cbabd0228eeaae58` |

Observed output: `status=pass`, `configurations_verified=8`, `feasible_count=2`,
feasible bits exactly `001,010`, with all coordinates and sums as inventoried
above; `V0=13199640003/1000000000000`, `Vbar=6/625`, `theta=9/10`, expected sum
30, and support sums `1491/50,1501/50`. Both strict slope checks passed, all
three original enclosures passed, and `variance_bound < optimal_dual`.
The full classification SHA256 was
`a34b04a4923192132448880159fd0b75818a3cc3ff81bceee9fdbfcf7e30429b`.

This bounds generic geometric arguments using only positive two-point grids
and two slab-feasible points. Universal comparison on the specified distinct
prime labels and adjacent exponent ladders remains **OPEN**. No xi or 5040
experiment, GPU run, large suite or Lean rebuild was performed. Independent
review, repository gates and merge remain caller obligations; this finite
implementation does not complete the standing research goal.
