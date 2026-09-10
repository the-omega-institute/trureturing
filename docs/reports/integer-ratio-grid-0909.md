# Integer-ratio real grid: fixed certificate and verifier

Date: 2026-09-09. This report supports section 25 of
[ARITHMETIC_BOUNDARY_QUANTIZATION.md](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md).
It preserves the one supplied witness and the exact supplied bounded program
and result. No candidate search occurred. There are eight fixed corners and
two feasible corners; no primes were generated or sampled.

This is supporting numerical evidence and a paper optimality certificate,
not independent mathematical approval, a prime-grid counterexample, a Robin
certificate, RH progress, a novelty claim, or Lean freezing. The repeated
rows and rational widths do not constitute distinct-prime logarithmic grids.

The caller-supplied inputs are
`/tmp/qgh-boundaries-0908/caller-integer-ratio-grid-check-0909.py`
(2512 bytes, SHA256
`7372b2a91cd150f342c1c253fc3ed3dc05c93d8ae812d1ac1f71c1b0480ebce9`)
and `caller-integer-ratio-grid-result-0909.json` (1840 bytes, SHA256
`3a978b81ceb7c1803f9aad9ff1b3993eeb87f9e178d649e551d1605fd53a5c3e`).
The delimited blocks below preserve their bytes, including final LF.
They are data in the existing `docs/reports/**` FILEMAP location,
not a new repository tool.

## Exact mathematical certificate

Use natural logarithms and \(f(x)=\log(1-e^{-x})\) for \(x>0\).
The rows are
\((1000/101,1020/101)\), twice \((111650/11211,113680/11211)\).
Their widths are \(h_1=20/101\), \(h_2=h_3=2030/11211\);
the lower-endpoint/width ratios are exactly \((50,55,55)\).
The coordinate-sum slab is
\([M_0,M_1]=[29999997/1000000,30]\), and
\(I=[10-10^{-6},10]\).
The full exact classification is in the preserved JSON below:
only 001 and 010 are feasible, both of sum 30.

For \(\rho_i=[f(d_i)-f(c_i)]/h_i\), the identity
\(\rho_i=\int_0^1 f'(c_i+th_i)\,dt\), strict decrease of
\(f'(x)=1/(e^x-1)\), and strict endpoint ordering imply
\(\rho_1>\rho_2=\rho_3>0\). Let
\(\theta=203/222\), \(\alpha=19/222\), \(\lambda=\rho_1\).
The 000/100 mixture with upper weight \(\theta\) has expected sum 30.
Row 1 ties at this price, while rows 2 and 3 uniquely choose their lower
endpoints. Thus the price and feasible-mixture values agree algebraically:

\[
D(30)=30\lambda+\sum_i[f(c_i)-\lambda c_i]
=\alpha f(c_1)+\theta f(d_1)+2f(c_2).
\]

For every mixture of expected sum at most 30, rowwise price maximization
gives a weak-duality upper bound; equality here proves optimality.
The two mixture support corners are outside the actual slab.
Numerical ball overlap is not used to prove equality or optimality.

Each row straddles \(I\), with nearest lower endpoints and distances
\(10/101-10^{-6}\), twice \(460/11211-10^{-6}\). Consequently

\[
V_0=\frac{1655254483717059563}{125686521000000000000},
\quad r=\sqrt{V_0/6},\quad L=10-r>0,\quad H=10+2r.
\]

The program uses exact fractions for the combinatorial and moment
identities, then Python-FLINT 0.8.0 / Arb at 256 bits for outward balls and
strict comparisons with exact rational bounds. It certifies

\[
10^{-10}<D(30)-[f(H)+2f(L)]<10^{-9}.
\]

The printed midpoint and radius are a display, not the certificate.
Classification hashing uses UTF-8 JSON with sorted keys and separators
`(',', ':')`, giving
`f9eca670c4f6417b6247d2a35067bec1b3851204b7a06607a9755b8bc720abf0`.

## Preserved supplied verifier

<!-- BEGIN SUPPLIED VERIFIER -->
```python
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

```
<!-- END SUPPLIED VERIFIER -->

## Preserved supplied certificate

<!-- BEGIN SUPPLIED CERTIFICATE -->
```json
{
  "status": "pass",
  "scope": "one hand-derived integer-ratio real grid",
  "candidate_search": false,
  "configurations_verified": 8,
  "python_flint": "0.8.0",
  "arb_precision_bits": 256,
  "rows": [
    [
      "1000/101",
      "1020/101"
    ],
    [
      "111650/11211",
      "113680/11211"
    ],
    [
      "111650/11211",
      "113680/11211"
    ]
  ],
  "coordinate_sum_slab": [
    "29999997/1000000",
    "30"
  ],
  "integer_lower_endpoint_ratios": [
    50,
    55,
    55
  ],
  "theta": "203/222",
  "V0": "1655254483717059563/125686521000000000000",
  "inventory": [
    {
      "bits": "000",
      "sum": "334300/11211",
      "feasible": false
    },
    {
      "bits": "001",
      "sum": "30",
      "feasible": true
    },
    {
      "bits": "010",
      "sum": "30",
      "feasible": true
    },
    {
      "bits": "011",
      "sum": "338360/11211",
      "feasible": false
    },
    {
      "bits": "100",
      "sum": "336520/11211",
      "feasible": false
    },
    {
      "bits": "101",
      "sum": "3050/101",
      "feasible": false
    },
    {
      "bits": "110",
      "sum": "3050/101",
      "feasible": false
    },
    {
      "bits": "111",
      "sum": "340580/11211",
      "feasible": false
    }
  ],
  "classification_sha256": "f9eca670c4f6417b6247d2a35067bec1b3851204b7a06607a9755b8bc720abf0",
  "strict_gap_bounds": [
    "1/10000000000",
    "1/1000000000"
  ],
  "gap_approximation_not_certificate": "[3.366686556042778282400921890250120016861849146400451607619698303077e-10 +/- 9.12e-77]",
  "optimality": "row-1 secant, other slopes strictly smaller, matching mixture",
  "prime_grid": false,
  "limitations": "Widths are rational, not certified log primes; rows 2 and 3 coincide.",
  "program_sha256": "7372b2a91cd150f342c1c253fc3ed3dc05c93d8ae812d1ac1f71c1b0480ebce9"
}
```
<!-- END SUPPLIED CERTIFICATE -->

## Reproduction and this implementation's verification

From the repository root, extract the verifier verbatim:

```sh
python3 - <<'PY'
from hashlib import sha256
from pathlib import Path
report = Path("docs/reports/integer-ratio-grid-0909.md").read_bytes()
start = b"<!-- BEGIN SUPPLIED VERIFIER -->\n" + b"```python\n"
end = b"```\n<!-- END SUPPLIED VERIFIER -->"
program = report.split(start, 1)[1].split(end, 1)[0]
assert len(program) == 2512
assert sha256(program).hexdigest() == "7372b2a91cd150f342c1c253fc3ed3dc05c93d8ae812d1ac1f71c1b0480ebce9"
Path("/tmp/qgh-integer-ratio-grid-check-0909.py").write_bytes(program)
PY
uv run --python 3.12 --with python-flint==0.8.0 python /tmp/qgh-integer-ratio-grid-check-0909.py
```

The I8 implementation executed the original supplied program once with:

```sh
uv run --python 3.12 --with python-flint==0.8.0 python /tmp/qgh-boundaries-0908/caller-integer-ratio-grid-check-0909.py
```

Exit code was 0. Its output parsed as exactly the preserved caller result,
including the classification and program hashes. This checks one fixed
witness; it does not create another candidate, test a prime tuple, or replay
the older real-grid, xi, or 5040 reports. The implementation envelope records
the command and output identity.

## Separately reported primary rational interval

The completed primary task
`c9caf71c-5b42-4d07-8de0-98540288eb7e`,
conversation `conv_515ce9ddd365db68`, returned model
`GPT-6 Astra`, also reports the following dyadic gap certificate.
This is the primary's supporting computation, not another review vote:

\[
\frac{N_-}{2^{384}}\le D-\Psi_3\le\frac{N_+}{2^{384}},
\]

```text
N_minus = 13265420454251553898483355164462982515249671011576421601599511022052158996428218127319287483843042314008878
N_plus  = 13265420454251553898483355164462982515249671011576421601599511022052158996428218127319287483843042314009126
```

Both rational endpoints strictly lie between \(10^{-10}\) and \(10^{-9}\).
The primary reports Python 3.12.13 Fraction/integer arithmetic, outward
rounding on \(2^{-384}\mathbb Z\), and integer-isqrt square-root bounds.
For each argument it sets \(z=x/16\in(0,1)\), uses alternating sums
\(S_{99}(z)\le e^{-z}\le S_{100}(z)\), then four outward squarings.
The 40-term series for \(-\log(1-y)\) uses tail bound
\(y^{41}/[41(1-y)]\). Its reported scope is eight corners, six distinct
function arguments, eleven function evaluations including repeats, and
fourteen fixed rational proof inequalities. The primary's self-reported
verification source SHA256 is
`caaaefd10d9050f33e1f2d17ddb3f971307fb783327d23b92d617832f95f2816`.
That primary program is not supplied as an inspectable file in this
increment, and this report does not claim to archive or rerun it.
The complete executable verifier preserved above is the caller's Arb
program with its separate, checked identity.

## Provenance and limits

This was a caller-owned `consensus-rnd:sshx` implementation flight,
I8, using completed primary mathematics and bounded caller verification.
Codex performed the source append and local checks; it is
`repo-prior-exposed`. There are no independent review votes
in these computations and no claim of sterile priors or demonstrated
model-family diversity. No opaque log reference or worker log was opened.

The primary envelope is
`pro-prime-bridge-retry-envelope-0909.json`, SHA256
`1c8f5ae65d521ad567538a39a9623fcbbcdd6816f814307492682adada7cb515`;
its invocation metadata are separately recorded in section 25.17.
The source/ingest base is
`c6bf5faaf36deb301317ef393195be039e410656`.
Independent mathematical review, CI and MERGED delivery remain open.
