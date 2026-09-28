# Finite Robin and atomic-relation bounds

These standard-library Python programs reproduce the finite arithmetic in
[FIBONACCI_ATOMIC_RELATION_GENERATION.md, §§83–89](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
They use exact integers, rational numbers, or outward integer intervals. Decimal
strings are display values; no sign decision uses floating point. These are
experimental arithmetic certificates with paper justifications, not Lean proofs.

Run with Python 3.9 or newer, without `-O` or `PYTHONOPTIMIZE` (the verifiers use
assertions). No third-party Python packages are required. From the repository
root, these are complete commands:

```sh
python3 docs/reports/fib-robin-boundary/price_band.py --out /tmp/fib_atomic_delivery/validation/price_band
python3 docs/reports/fib-robin-boundary/finite_reserve.py --out /tmp/fib_atomic_delivery/validation/finite_reserve
python3 docs/reports/fib-robin-boundary/adaptive_boundary.py --out /tmp/fib_atomic_delivery/validation/adaptive_boundary
```

Replace each `--out` with a directory of your choice. For another working
directory, give the script's absolute path. Keep `finite_reserve.py` beside
`price_band.py`; the former imports the latter by its own source location and
disables bytecode writes. Each program writes only inside its required `--out`
and prints its result to stdout (failures may also print diagnostics to stderr).
Reusing an output directory overwrites the program's result files there.

| Program | Mathematical scope | Checked result |
|---|---|---|
| `price_band.py` | Entire price interval `[10^-6, 1/25]`, with endpoint ties and a starting integer patch | 9,592 primes, 8,665 active layers at the lower price, 8,657 switches, 8,658 cells; witness gaps exceed `123/500000`; 2,959 starting integers checked |
| `finite_reserve.py` | All real `x` in `[144,121393]`, using event-free interval bounds and continuity | 11,425 primes, 11,539 prime-power events, 11,493 cells; `Phi+B > 13/100000` and `Phi >= -1/(2 sqrt(x) log(x))` |
| `adaptive_boundary.py` | Every positive `R < 46189` coprime to 210, and common-source modular regressions | 10,558 residuals; exact maxima `3024/2431` for `R<=4181` and `33516/26741` for `R<46189`; 42,875 CRT tuple checks and 5,831 multiplication cases |

`price_band.py` and `finite_reserve.py` also generate `cells.json.gz`. These full
certificates are reproducible runtime output and are not retained here. The
`wire` endpoints are signed integers divided by `2^128`; they are authoritative.
Nearest-rounded decimal displays are not substitute interval endpoints.
`certificate_sha256` hashes the uncompressed compact JSON. The reserve result
also reports the compressed byte hash. The retained small files
[`price_band.json`](price_band.json), [`finite_reserve.json`](finite_reserve.json),
and [`adaptive_boundary.json`](adaptive_boundary.json) are actual outputs of the
commands above, with final script hashes and source paths relative to this
directory. The reserve output also identifies and hashes its imported engine.

The reserve minimum lower-expression endpoint is approximately
`0.0001387077093931118879802602466` on `[120539,120551]`; this is a certified lower
bound, not the exact minimum of the actual function. Its barrier lower-expression
endpoint is approximately `0.0001234545027142578218122253261`. The price verifier's
minimum noninitial witness lower endpoint is approximately
`0.0002461836616312356422357908016`. The programs check signs using the exact
endpoints and fail if comparisons are unresolved.

The pressure characterization and analytic transfer in §85 give Robin's
inequality for every integer `5040 < n <= 10^30000` from the price certificate.
The program alone does not prove the logarithm series, Euler-constant bounds,
calculus, or that mathematical transfer inside a proof assistant. It checks no
price below `10^-6`. The continuous reserve claim additionally uses §88's global
cell minimum with `Psi>1`, an eligible-prime subset valid throughout each cell,
and cancellation of the simultaneous jumps in `P` and `Psi`.

The rough maxima are bounds over unresolved fibers; the maximizing residual is
not asserted to be the actual input. The modular entropy formulas require one
uniform common source. Neither a finite modular regression nor support size
alone certifies entropy for an arbitrary law. The general-scale bound on `Phi`
remains open. No RH conclusion or advance beyond published finite Robin ranges
is claimed.

Existing mathematical sources reused by the theory include
`D5.S3.Arith.ExponentExchange.IntegerSwap.prime_exponent_swap`,
`D5.S3.Arith.GoldenResource.GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum`,
`D5.S3.Arith.GoldenResourceOptimalInteger.golden_resource_unique_optimum`, and
`D5.S3.Arith.Robin.SevenSmooth.robin_seven_smooth`.
The finite `Phi=I_psi` and `R=D_disc` identities already appear in
[ZECKENDORF_EULER_5040.md](../../develop/theory/ZECKENDORF_EULER_5040.md), in
“定理 1.1：尾积分的有限算式” and “定理 1.2：压力余量的精确二分解”, immediately
following “两个有限素数幂求和”. The additional result is termwise finite
nonnegativity and the explicit positive sub-reserve.

The five-direction stopping conditions are applications of
[Axler, Theorem 3](https://link.springer.com/article/10.1007/s11139-022-00683-0)
and [Hertlein, Theorem 2](https://arxiv.org/pdf/1612.05186v2), always for `n>5040`.
A stopping label applies to the current task and does not replace modular state
for future Add/Mul operations. These literature conditions are not newly proved
by the programs.
