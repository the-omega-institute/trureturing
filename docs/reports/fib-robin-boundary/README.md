# Finite Robin and atomic-relation bounds

These standard-library Python programs reproduce the finite arithmetic in
[FIBONACCI_ATOMIC_RELATION_GENERATION.md, §§83–102](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
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

## Exact finite maxima and independent checkers

The rough and mandatory-core producers emit complete Bellman DAGs. Their
checkers do not import the producers: they reconstruct consecutive primes,
every exponent branch, exact budget transitions, upper bounds and attaining
witnesses. The core checker also reconstructs each integer remaining-core
prune and distinguishes infeasibility from an allowed empty suffix. The
canonical normalization theorems in §§90–91 are external to these Python
checkers. They require, respectively, unrestricted rough integers or a
nonincreasing mandatory lower-exponent profile on a consecutive prime prefix.

```sh
python3 -B docs/reports/fib-robin-boundary/rough_max_regression.py --out /tmp/fib_atomic_delivery/validation/rough-max
python3 -B docs/reports/fib-robin-boundary/rough_max_check.py /tmp/fib_atomic_delivery/validation/rough-max/certificate-y7-B1000000000000.json --out /tmp/fib_atomic_delivery/validation/rough-max/standalone-check.json
python3 -B docs/reports/fib-robin-boundary/core_max_regression.py --out /tmp/fib_atomic_delivery/validation/core-max
python3 -B docs/reports/fib-robin-boundary/core_max_check.py /tmp/fib_atomic_delivery/validation/core-max/certificate-core-times-1000.json --out /tmp/fib_atomic_delivery/validation/core-max/standalone-check.json
```

For another finite input, the producer interfaces are:

```sh
python3 -B docs/reports/fib-robin-boundary/rough_max.py --y 7 --bound 4181 --out /tmp/rough-certificate.json
python3 -B docs/reports/fib-robin-boundary/core_max.py --profile 4,2,1,1 --bound 10080 --out /tmp/core-certificate.json
```

Each checker takes a certificate file and requires an `--out` **report file**.
Producers require an `--out` **certificate file**; suites require an `--out`
**directory**. Existing selected output files are overwritten. All new scripts
disable bytecode writes, and local imports resolve beside their source files.
Keep each producer/checker/suite trio together. No files are written beside
sources unless the caller explicitly selects that output location.

| Retained result | Reproducible checks |
|---|---|
| [rough-max/results.json](rough-max/results.json) and its six relative certificate files | Six exact examples; all budgets 1–256 at `y=1,2,7,13` (1,024 direct sigma comparisons); eight corruptions rejected |
| [core-max/results.json](core-max/results.json) and its four relative certificate files | 3,600 direct sigma comparisons, including 1,802 infeasible cases; six corruptions rejected; four all-multiple enumerations; the eight-multiple nonmonotone counterexample |

At `y=7,B=10^12`, the exact maximum is `30888345600/20458175309`, attained
at `388705330871`, with 134 states and 140 branches. At `y=1,B=5040`, it is
`403/105`, attained at 5040, with 63 states and 66 branches. The six complete
values are in §90 and the result JSON. Additional history or congruence
constraints turn the rough result into an upper relaxation; the maximizing
witness need not satisfy those constraints. The checkers certify attainment,
not a claim that the witness is the smallest among all ties.

The mandatory core is `M=2^21*3^13*5^9*7^7*11^6`. Budgets `M,2M,10M,1000M`
attain multipliers `1,2,6,884`. The suite factors multipliers and merges total
prime exponents; it never substitutes `Z(M)*Z(t)` for `Z(M*t)`. A nonmonotone
profile is rejected: at `M=150,B=1200`, the canonical restriction loses
`31/450`. A one-value maximum of `Z` does not maximize the full Robin ratio.
For all `n` in `[A,B]`, a valid sufficient comparison uses
`U_M(B) < exp(gamma)*log(log(A))`, or a joint `(n,Z(n))` frontier.

The joint frontier tools make that last distinction executable on finite rough
fibers:

```sh
python3 -B docs/reports/fib-robin-boundary/robin_frontier.py \
  --y 7 --bound 100000 --out /tmp/fib_atomic_delivery/validation/robin-frontier.json
python3 -B docs/reports/fib-robin-boundary/robin_frontier_check.py \
  /tmp/fib_atomic_delivery/validation/robin-frontier.json \
  --out /tmp/fib_atomic_delivery/validation/robin-frontier-check.json
python3 -B docs/reports/fib-robin-boundary/robin_frontier_regression.py \
  --out /tmp/fib_atomic_delivery/validation/robin-frontier-regression.json
python3 -B docs/reports/fib-robin-boundary/robin_frontier_margin.py \
  /tmp/fib_atomic_delivery/validation/robin-frontier.json --core 10080 \
  --out /tmp/fib_atomic_delivery/validation/robin-frontier-margin.json
```

The producer and checker retain exact `(suffix integer, sigma/suffix)` pairs
and remove only points dominated by a smaller suffix with at least as large a
weight. The producer, independent checker and normalization part of the
regression evaluate no logarithm and make no Robin sign claim. The transfer
to a fixed common core is the mathematical content of §§156 and 159.
The margin tool first checks the entire certificate, then applies the existing
rational logarithm and Euler-constant lower bounds to the finite frontier.
It requires a core at least 5040 whose prime factors are at most the rough
cutoff, and binds its result to the checked certificate bytes by SHA-256.
A positive result is scoped to that core, rough cutoff and finite suffix bound.
The bound 100000 above gives eight frontier points; §157 uses bound 1000 and
four points. Both scans with core 10080 have positive lower bounds.

The scan includes suffix 1. With core 5040 this retains the boundary integer
5040 and reports `OPEN`, even though Robin's target excludes that integer.
`OPEN` means a lower bound did not certify positivity, not that a counterexample
was found. §159 explains the separate target-domain argument. The regression
also exercises the margin CLI on both core values and rejects altered weights,
missing recurrence states, empty frontiers and invalid cores.

## Sharper joint stopping and sufficient prime resolution

[Axler's totient estimate](../../../Library/notes/axler2023robin.md), retained
inside his proof, gives the stronger joint cutoff
`1000000000000/1000000315367`. The rational overlap certificate and complete
five-direction partition can be reproduced with:

```sh
python3 -B docs/reports/fib-robin-boundary/axler_cutoff.py \
  --out /tmp/axler-cutoff.json
python3 -B docs/reports/fib-robin-boundary/valuation_slices.py \
  --primes 2 3 5 7 11 --lower 21 13 9 7 6 --caps 31 21 13 11 9 \
  --threshold 1000000000000/1000000315367 --out /tmp/valuation-slices-axler.json
```

Keep `axler_cutoff.py` beside `kernel_tail.py`; it imports the rational log
enclosures. The actual outputs are [`axler_cutoff.json`](axler_cutoff.json)
and [`valuation_slices_axler.json`](valuation_slices_axler.json). The latter
has 9,900 cells, including their unbounded tails: 1,144 certified, 8,756
outside the condition, zero ambiguous, and 42 minimal outside profiles.
The caps are coordinatewise minimal for deciding this sufficient condition
by clipped valuations, not for deciding Robin itself. The cutoff certificate
also checks the joint `(v13,v23) <= (5,4)` condition with both primes present.
Together with the cited Fibonacci rank formulas, the note gives 84 necessary
index-divisibility regions for authenticated sources `n=5040*F_j`.

The published analytic inequalities and original large finite verification
remain literature inputs. These programs do not prove them, establish RH,
or add Lean results. The earlier Hertlein calculation below remains a valid,
weaker partition. Comparing the two counts is not a natural-number density
comparison because the caps and cell sizes differ.

## Joint valuation stopping from the literature

[Hertlein's totient bound and finite-range coverage](../../../Library/notes/hertlein2018robin.md)
give a stronger stopping test than checking each small-prime direction alone.
For primes actually dividing the same integer, the product of their local
factors `1 - p^(-v_p(n)-1)` may already be at most `1771560/1771561`, even
when none of the separate valuation rules applies.

This literature application covers every `n=M*t` with the exact core
`M=2^21*3^13*5^9*7^7*11^6` and all prime factors of `t` greater than 11,
with no bound on the tail support or exponents. The earlier finite support
certificates are weaker for that exact-core family. Multiplying `M` by small
primes changes its valuations, so this does not cover all multiples of `M`.

```sh
python3 -B docs/reports/fib-robin-boundary/valuation_slices.py \
  --primes 2 3 5 7 11 --lower 21 13 9 7 6 --caps 25 15 11 9 7 \
  --threshold 1771560/1771561 --out /tmp/valuation-slices.json
```

[valuation_slices.json](valuation_slices.json) records 270 cells: 17 pass the
product condition, 253 fail it, and none is ambiguous. A coordinate at its cap
represents all larger exponents, with its factor bounded above by 1. Thus this
is an exact classification of the unbounded exponent orthant for that
condition. The report gives 12 minimal profiles that fail the condition and
8 maximal regions that pass. General input caps may instead give `OPEN`
with explicitly listed ambiguous cells.

Together with the existing five separate stopping rules, a hypothetical
Robin counterexample must be divisible by at least one of those 12 profiles'
cores: `M*r` with `r` in `{6,14,15,16,20,21,35,44,50,99,110,539}`.
For the authenticated family `5040*F_j`, the existing rank/lifting formulas
transport this to `D*r | j`, with `D` as in the index stopping section below.
Failing this sufficient test does not establish a counterexample.
The Python program certifies rational factors and the finite partition; the
analytic Robin implication relies on the cited literature. No new Lean
theorem, global verification range or proof of RH is claimed.

## Recursive reserve, index stopping and gluing

```sh
python3 -B docs/reports/fib-robin-boundary/recursive_reserve.py --out /tmp/fib_atomic_delivery/validation/recursive-reserve
python3 -B docs/reports/fib-robin-boundary/recursive_reserve_check.py --input /tmp/fib_atomic_delivery/validation/recursive-reserve --out /tmp/fib_atomic_delivery/validation/recursive-reserve/readback_results.json
python3 -B docs/reports/fib-robin-boundary/index_stopping.py --out /tmp/fib_atomic_delivery/validation/index-stopping
python3 -B docs/reports/fib-robin-boundary/relational_gluing.py --out /tmp/fib_atomic_delivery/validation/relational-gluing
```

`recursive_reserve.py` imports the unchanged same-directory `price_band.py`
interval engine. It writes `results.json` and runtime-only `certificate.json.gz`
under `--out`. The serialized checker requires that output directory as
`--input` and writes only its explicit report file. It checks saved tree
structure, coverage, stop decisions and six decimal rounding cells; it does
not independently recompute transcendental enclosures. Reproduction of those
enclosures runs the producer and its engine. The compact JSON SHA-256 in the
result identifies the uncompressed certificate.

The retained [recursive_reserve.json](recursive_reserve.json) reports 14 roots
`[F_j,F_(j+1)]` for `j=12..25`, 3,202 evaluations, 1,608 leaves and depth 12.
Every leaf proves `Gamma > 9/10^8`; the smallest lower endpoint is
`9.45202409092205664866e-8` at `[44627,44771]`. Gamma uses the global-minimum
relaxation in §94, not the sharper clipped formula. The Euler-constant
harmonic enclosure uses `m=10^6`. All six reserve quantities at `x=100000`
were reproduced; [recursive_reserve_check.json](recursive_reserve_check.json)
records the saved-certificate checks. Fourteen prefix/direct-sum interval
overlap checks are diagnostics, not proofs of numerical equality. At the
diagnostic point `B2=R2` follows from equality of their prime masks.

The analytic bridge requires `a>=4` and `a<b`, uses `P(b^-)` and `Psi(a)`,
and handles the closed right endpoint by event continuity. Subdivision
improves Gamma but can retain positive relaxation slack, so it does not
guarantee successful termination. The unconditional tail estimate is
`0 <= R-R_K <= (4+2/K)*x^(-K/(K+1))`. The exponent bound `a_p<=K` requires
both `x>=K^K` and retained primes `p>x^(1/K)`.

[index_stopping.json](index_stopping.json) contains 50,000 actual Fibonacci
valuation comparisons and 1,040 large modular checks. `--limit` selects the
positive direct cutoff (default 10,000), `--seed` selects the deterministic
large-index sample (default 20260929), and repeatable `--index j` adds indices
`j>=3`. The exact infinite statement in §95 uses Lengyel's original Lemmas 1–2
and rank/lifting theorem plus Axler/Hertlein: for the authenticated standard
source `n=5040*F_j`, all five tests fail exactly when
`2045861090389670400000000` divides `j`. A surviving index is not a Robin
counterexample or necessarily unresolved: `j=D` already passes Axler's
13-adic test. Metadata alone does not authenticate the source equality.

[relational_gluing.json](relational_gluing.json) records 4,096 seam pairs,
4,096 cocycle triples, 2,720 local monotonicity cases, 24,768 finite future
comparisons, 4,096 unrestricted-support comparisons, 8,192 partial-factor
lower bounds, and the 5040 history/seam check (256 histories, 60 normal seams,
weight ratio `1296/403`). Conditioning KL is relative to the original product
law and need not equal mutual information. Future pruning requires all
allowed loss factors and compatible future feasibility; current weight and
budget dominance alone fail even within the 5040 family. These finite checks
do not replace the quantified proofs in §§96–97.

All retained outputs were generated from the final portable source bytes.
Suite certificate references are relative to their result directory; source
hash keys in each suite name files in this README's directory. Other result
source hashes identify their corresponding same-named program (the reserve
result also identifies its engine). Full compressed certificates remain
runtime output. The new suites were executed from a different working
directory using copied source paths containing spaces and an environment
without personal shell setup; this checks that portability scenario, not
every operating system.

The analytic results in §§92–94 prove equivalences: the eventual Phi barriers
with constants `1/2` and `4/5`, and eventual nonnegativity/positivity of the
specified unconstrained price gap, have RH strength. Neither side of those
equivalences is established here. The normalized price-gap band explicitly
assumes RH. No new originality or kernel-verification claim is made for these
deductions. The existing scoped Lean build applies only to the existing
modules named above; its success does not verify Python or the appended prose.

## Critical slices and context completion (§§98–99)

```sh
python3 docs/reports/fib-robin-boundary/critical_slice.py --out '/tmp/fib critical slice'
python3 docs/reports/fib-robin-boundary/critical_slice_check.py --certificate '/tmp/fib critical slice/certificate.json.gz' --out '/tmp/fib critical replay'
python3 docs/reports/fib-robin-boundary/critical_slice_regression.py --certificate '/tmp/fib critical slice/certificate.json.gz' --out '/tmp/fib critical regressions'
python3 docs/reports/fib-robin-boundary/context_completion.py --out '/tmp/fib context/results.json'
```

The three critical-slice commands require output **directories**. The context
command requires an output **JSON file**. All four require `--out`, disable
bytecode writes, and reject Python optimization, which would disable assertions.
The critical producer and independent checker load only the unchanged
same-directory `price_band.py` as their local numerical dependency. Keep the
regression program beside that checker and engine. Context completion uses
only the standard library. Outputs, including corrupted-certificate fixtures,
remain inside the explicit output locations; use external directories. Existing
selected output files are overwritten. Run the regressions in a fresh directory.

The critical producer writes `results.json` and the runtime-only full
`certificate.json.gz`. The checker rebuilds the complete prime and layer sets,
rechecks the strict order of all adjacent thresholds, classifies every stable
cell and recreates every critical-point and endpoint interval. For the integer
patch it independently computes divisor sums using a smallest-prime recurrence;
the producer uses a divisor sieve. They share interval primitives, so this is
independent replay of coverage and arithmetic, not a second analytic proof
kernel. The regression program checks three concrete rejections: a missing
layer, a false cell classification, and a false attained patch maximum. Each
must fail at its intended assertion, not merely return an arbitrary error.

| Retained small result | Scope and reproduced values |
|---|---|
| [critical_slice.json](critical_slice.json) | All real `x` in `[log(40000),121393]`; 11,425 primes, 8 initial layers, 11,568 events, 11,569 cells, 133 strict self-matching minima (117 at `x>=144`), first integer 720720; all minima and endpoints exceed `51/250000` |
| [critical_slice_check.json](critical_slice_check.json) | Complete independent replay; all 34,960 integers from 5041 through 40000 covered by four exact-maximum blocks |
| [critical_slice_regression.json](critical_slice_regression.json) | Three false-certificate regressions, each rejected at the intended check |
| [context_completion.json](context_completion.json) | 34,384 optimum comparisons, 3,600 state products, 216,000 associativity triples, 5,040 unit-fiber coordinates, 32,768 gcd endpoint checks and 3,708 finite reverse witnesses |

The critical minimum lower endpoint among internal valleys is approximately
`0.0002052870022118778275605233327`, at scale
`119544.1883346433876462307764`. The two endpoint lower bounds are approximately
`0.008314953821252398723132344539` and
`0.0002044061996600856183985968307`. The narrow Euler-constant enclosure is
`H_m-log(m)-1/(2m) < gamma < H_m-log(m)-1/(2(m+1))`, with `m=1000000`.
It improves the older enclosure without altering the old experiments. The
finite patch uses exactly four blocks: 5041–9410, 9411–13780, 13781–22520 and
22521–40000. These values belong to this implementation, not to another
certificate's subdivision convention. Nearest-rounded decimal strings remain
displays; signs use exact wire endpoints.

The critical producer and checker `certificate_sha256` field hashes the
**uncompressed compact JSON**, not gzip bytes. Its value is
`8885dc697a178d2b2944bcac093936ba61bd050eee37871667fd0ad4786160d9`.
Compression bytes can depend on the Python/zlib implementation. Retained result
files match the final sources' external runs; the producer identifies its own
source and the engine, the replay identifies its checker, and the regression
result hashes its program, checker and engine. The context result is entirely
mathematical data and remains byte-identical to the preparation result. The
portable runs use copied sources in a path containing spaces, a different
working directory and a minimal environment. This verifies that scenario,
not all operating systems.

Context comparisons use exactly `exp(25*J(n))=sigma(n)^25/n^26`. The 263 contexts
are 1–256 plus 5040, 10080, 65520, `2^40`, `3^20`, `11^5` and
`2^8*3^5*11^2`. Candidate actions are 1–128 plus `A_*`, `2*A_*`, `3*A_*`,
with duplicates removed. The exact comparison checks equality only at `A_*`.
General additive distinguishability is tested for every ordered unequal
residue pair at `H=2..64`; all 5040 large-template suffixes and every nonzero
residue difference are also checked. The output includes 60 fiber sizes and
`phi(5040)=1152`. Of the 4096 ordered pairs `A,B<=64`, 388 pass permanent price
dominance and 3708 have actual finite counter-continuations; witness exponent
histograms and samples are retained. The diagnostic search cap is 64, not a
claimed uniform bound on the general theorem's witnesses.

The mathematical input mapping is precise:

| Input in the appended deductions | Existing source and scope |
|---|---|
| Positive-price global maximum and positive-part sum | `D5/S3/Arith/GoldenResource/GoldenResourceSupremum.lean`, `golden_resource_supremum_eq_positive_part_sum` |
| Strict prime-axis layer decrease | `D5/S3/Arith/GoldenResourceOptimalInteger.lean`, public `golden_layer_strict_decrease` |
| Strict 5040 template thresholds, tail exclusion and per-axis unimodality | Same file's private `thresholds`, `tail_exclusion`, `optimalExponent`, `exponent_thresholds`, and the local `up`/`down` arguments within `local_unique_max` |
| Unconstrained 5040 uniqueness | Same file's public `golden_resource_unique_optimum`; this statement alone is insufficient for context-restricted optimization |
| General threshold-to-local-maximum interface | `D5/S3/Arith/GoldenLocalThreshold.lean`, `golden_prime_local_objective_maximal_of_threshold` |
| Naming the divisor-state range by a golden window | `D5/S3/Arith/GoldenResource/GoldenDivisorLanguage.lean`, `full_window_divisor_golden_equiv` and its 5040 specialization; not identification with arbitrary exponent-window projection |
| Related finite controlled-behavior interface | `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean`, `controlled_behavior_universal_property`; its finite-carrier assumptions do not establish the infinite-positive-integer bridge |
| Exact all-prime future infimum and feasibility conditions | Theory §97, specialized to the gcd expressions in §99; no duplicate gluing experiment |

The newly read local-threshold, divisor-language and controlled-behavior
interfaces are source mappings, not newly compiled applications. The previously
successful scoped build remains limited to its named unchanged modules. No new
Lean statements or kernel verification of §§98–99 or Python are claimed.
Private source interfaces are identified, not copied into new wrappers.

Section 98 proves local event finiteness, cancellation of `Phi+R`, a strictly
negative derivative jump even for simultaneous activations, and the exact
stable-cell self-matching condition. Its unconditional `D(x)->0` proof plus
verified positive `x0=log(40000)` gives a nonpositive-failure reduction, including
zeros; the finite 5041–40000 patch is needed in the final RH equivalence. None
of this proves the remaining infinite positivity target or convergence of a
fixed-point iteration. The scalar Phi barrier remains a sufficient route;
the pointwise joint-gap target allows same-source compensation.

Section 99 needs strict unimodality on every prime axis. Its completion is
numerically unique; original syntax need not be. The 60-state minimum concerns
accurate actions with multiplicative futures and no source reopening, while
arbitrary additive futures require 5040 residue states. Cardinality is not
physical dimension. All-future price dominance still requires continuation
feasibility for pruning, and context Robin bounds need size/value information
in addition to the action state. These deductions and finite diagnostics make
no originality or RH-completion claim.

## Operation-library resolution (§100)

[operation_resolution.py](operation_resolution.py) is a standalone standard-library
program; [operation_resolution.json](operation_resolution.json) is its actual
output. It requires Python 3.8 or newer and an explicit `--out` JSON file,
creates that file's parent directories, and overwrites the selected file.
It disables bytecode writes and rejects `-O`/`-OO`, since its exact checks use
assertions. It reads neither repository data nor a proposed result file.

To reproduce from the repository root, including an unrelated working directory,
copied source path containing spaces, and minimal environment:

```sh
operation_python="$(command -v python3)"
operation_source="$PWD/docs/reports/fib-robin-boundary/operation_resolution.py"
operation_expected="$PWD/docs/reports/fib-robin-boundary/operation_resolution.json"
operation_run="$HOME/fib operation reproduction"
mkdir -p "$operation_run/source files" "$operation_run/working directory"
cp "$operation_source" "$operation_run/source files/operation_resolution.py"
(
  cd "$operation_run/working directory" || exit 1
  env -i PATH=/usr/bin:/bin "$operation_python" "$operation_run/source files/operation_resolution.py" --out "$operation_run/output/operation_resolution.json"
)
cmp "$operation_expected" "$operation_run/output/operation_resolution.json"
cmp "$operation_source" "$operation_run/source files/operation_resolution.py"
```

The retained source was executed in that portability scenario with exit 0;
the result was byte-identical to the preparation result and the retained JSON.
Both source copies remained unchanged; the copied source directory contained
only the program and the working directory remained empty. Missing `--out`
exited 2; optimized execution exited 1 at the explicit assertion guard. These
are checks of this environment, not of every Python/platform combination.

The independent minimizer starts from the concrete residues and their gcd
readouts, then refines by concrete modular successors until stable. It never
calls `encode`, `local_encode`, or `predicted_count`. Only after convergence
does the verifier compare the **entire canonicalized partition** to the
proposed encoding. Section 100.10 proves why stability covers arbitrary finite
words, rather than a fixed sampled horizon.

Multiplication uses fewer than all scalar residues. A separate unit-group
closure verifies its unit generators, then an independent breadth-first
traversal checks that the generated multiplicative monoid reaches every
residue for each encountered modulus. For 5040 the chosen multipliers are
`2,3,5,7,11,13,17,19,23`. Prime divisors plus unit generators generate every
positive scalar action; the zero residue is represented by a positive
multiple of the modulus. Translation `+d` represents the original library's
finite modular closure, not necessarily one primitive operation. Its
equivalence is proved in §100.2 and checked separately for 376 small libraries.

The JSON schema is `fib-operation-resolution-exact-diagnostics-v1`. Model rows
retain the actual stabilized state counts, proper refinement rounds, generator
counts and maximum record fibers. The legacy field name
`max_extra_record_alphabet` means **最少记录取值数**: the number of distinct
values of one finite record map decoded jointly with the already known gcd
state. It is not a lower bound on textual characters or the alphabet size of
unrestricted variable-length strings. The exact value is `varphi_E(H/d)`;
the program checks that the gcd-1 fiber attains it. The record is not required
to update independently of gcd, and cannot be recovered from gcd alone.

| Operation-resolution check | Actual count |
|---|---:|
| Local behavior models | 83 |
| Small composite behavior models (61 distinct moduli) | 367 |
| All divisor parameters `d` for `H=5040` | 60 |
| Source-residue partition comparisons | 330781 |
| Refinement transition scans | 11586075 |
| Refinement-derived distinguishing suffixes | 55165 |
| Separately constructed global affine witnesses | 55165 |
| Executed operations in selected distinguishing suffixes | 74468 |
| Longest selected suffix | 9 |
| Local scalar updates | 1263471 |
| Products of two abstract local operands | 1263471 |
| Local allowed-addition updates | 313091 |
| Large positive-scalar edge checks | 498 |
| Same-source join models | 1830 |
| Same-source join source comparisons | 9223200 |
| Maximum conditional-record fiber checks | 510 |
| Original-addition-library closure checks | 376 |
| Coarse-state `+2520` updates | 5040 |

Local models use `p=2,3,5,7,11`, every `p^h<=256` with `h>=1`, and every
`e=0..h`. Update checks enumerate every local source residue, every scalar
residue (zero represented by the positive modulus), every permitted
translation, and every pair of abstract operands via their source residues.
Additional scalar probes are `p^(h+1)` and `p^(h+1)+1`, at source residues
`0,1,p^h-1`. Small composite models use every `d|H` for `2<=H<=96` with at
least two distinct prime factors. The 5040 models cover all 60 divisors.
The 376 original-library checks use `H=2..48` and each list
`[],[2],[3],[7],[10],[2,5],[4,6],[H//2,H]`.

Witnesses select adjacent final-class representatives **within each original
gcd fiber**, not every unequal pair. One suffix is reconstructed only from
the refinement history. The second witness has form `a*C+d*b`, using the
inverse of `d/p^e` modulo `p^(h-e)` to realize the local separating translation
globally. Both are executed and checked. Length 9 bounds only these selected
generator words; it is neither a universal depth bound nor a bound on their
expansion into original primitive addends. The witness digest hashes the
deterministic sequence of compact JSON tuples `[H,d,x,y,word,a,b]`:
`483e9b46b1433eb12daa347be5ffa450ee34de90f8f62bc2a639a22d333c46df`.
No full transition tables or witness lists are retained.

The 1830 join models are all unordered divisor pairs with repetition, with
all 5040 common sources checked for each. The joint partition equals the
partition for `gcd(d1,d2)`; its size counts the actual image, not a Cartesian
product of independent labels. In particular, `+7` and `+10` have 1440 and
1512 states, but their same-source join has only 5040. The examples give
`+13 -> 5040` and `+2520 -> 60`; all 5040 source residues satisfy §100.8's
explicit `+2520` gcd update. Exposing `+2` and `+5` separately gives 5040
states, while a closed `+7` macro has 1440. The retained counterexample is
`C=5` and `C=725`: equal macro states, but after `+2` the gcd readouts are 7 and 1.

Final SHA-256 identifiers:

| Artifact | SHA-256 |
|---|---|
| `operation_resolution.py` | `2d78f72b2f7bfbb46f3ef0ed5f60e5192715838dbf23412e6963ff9f2bcc6fb6` |
| `operation_resolution.json` | `afa1bb88f5605e1872235221854866e7607ac4911e7238092f6f2f8778f44331` |

Section 100 reuses §99.1's contextual-completion theorem with its strict
prime-axis unimodality assumptions; it does not repeat that proof. Its
minimality contract is deterministic exact output for every positive source
and arbitrary finite legal words, without free source rereading or an extra
oracle. A particular finite DAG need not allow all such continuations.
State cardinality is not physical dimension. The conclusions classify the
action interface; they do not recover size, `Z`, `J`, source syntax, or Robin
margin. The paper proofs and finite diagnostics have no new Lean kernel
verification, originality, or RH-completion claim. Earlier programs and results
remain unchanged, and the earlier scoped Lean check is not extended to this
new prose or Python.

## Coarse additions and direct half-turn checks (§101)

[`coarse_additions.py`](coarse_additions.py) is the adapted finite verifier for §101. It uses only Python's standard library and exact integer gcd arithmetic. It checks every positive translation representative for `H=2,…,256`, then computes stable Moore behavior partitions for selected libraries with `H=2,…,48`, positive representatives for every scalar, and the explicit `H=5040` macro cases. Assertions are part of verification: optimized execution is rejected, bytecode writes are disabled, and `--out` is the only output path.

```sh
python3 docs/reports/fib-robin-boundary/coarse_additions.py \
  --out "/tmp/fib_atomic final verification/coarse_additions.json"
```

The delivered JSON is [`coarse_additions.json`](coarse_additions.json). Its actual run counts are 255 complete translation windows, 32,895 one-addition models, 857,558 direct source-translation checks, 32,512 one-addition counterexample pairs, 49,407 closed update checks, 3,447 positive-lift checks, 424 independent complete behavior models, 738,785 Moore transition scans, and 20,160 `H=5040` closed-update checks. The retained JSON hash is `6a5e99b69699873ef4e31f0a93ab95489f710f1edc27c5593122db77d9956fac`; the delivered source hash is `3177c59b037a59e99dd56be8c7b7a31694c1d965d14f5004dd880c07fc1ba03e`.

## Refinement records and conditional capacity (§102)

[`refinement_records.py`](refinement_records.py) independently enumerates actual affine gcd responses for `H=2,…,24`, checks every nested `d_new | d_old` pair through `H=128`, and checks the `H=5040` examples, the `+H/2` no-refinement corollary, and incomparable-library gcd joins. It constructs and decodes a finite record map jointly with the old summary, checks local maxima at unit sources, and keeps all output in the caller's `--out` path. It is standard-library-only, disables bytecode writes, and rejects `-O`/`-OO` because assertions bear verification.

```sh
python3 docs/reports/fib-robin-boundary/refinement_records.py \
  --out "/tmp/fib_atomic final verification/refinement_records.json"
```

The delivered JSON is [`refinement_records.json`](refinement_records.json). Its actual counts are 83 raw affine models, 151,487 raw affine gcd evaluations, 202 raw behavior-refinement pairs, 2,044 eta-refinement pairs, 2,267 total refinement-pair record checks, 262,060 encode/decode checks, 92,882 unit-source maximum checks, 60 half-modulus no-refinement libraries, and 302,400 corresponding source checks. The retained JSON hash is `c6b9c8394b1865df6282883e790dbba3ccc355e35f02808163905428f1438438`; the delivered source hash is `2adbd12ef8a9affe072960f8a61ba2e4e2732a086fc69fae7a27954132604a8a`.

For both programs, a portability run uses an unrelated working directory, copied final source paths containing spaces, `env -i PATH=/usr/bin:/bin`, and external output paths; the produced JSON is compared byte-for-byte with the retained file. These finite programs verify the stated finite scopes and record contracts only. Sections 101–102 are paper mathematics and direct corollaries of §100, with zero new Lean candidates; they make no originality, RH, or physical-dimension claim and do not complete the infinite-scale research goal.

The exact portability command is:

```sh
run_root="/tmp/fib_atomic final verification"
mkdir -p "$run_root/source files" "$run_root/unrelated cwd" "$run_root/output"
cp docs/reports/fib-robin-boundary/coarse_additions.py "$run_root/source files/coarse additions.py"
cp docs/reports/fib-robin-boundary/refinement_records.py "$run_root/source files/refinement records.py"
(cd "$run_root/unrelated cwd" && env -i PATH=/usr/bin:/bin PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3 \
  "$run_root/source files/coarse additions.py" --out "$run_root/output/coarse additions.json")
(cd "$run_root/unrelated cwd" && env -i PATH=/usr/bin:/bin PYTHONDONTWRITEBYTECODE=1 /usr/bin/python3 \
  "$run_root/source files/refinement records.py" --out "$run_root/output/refinement records.json")
cmp "$run_root/output/coarse additions.json" docs/reports/fib-robin-boundary/coarse_additions.json
cmp "$run_root/output/refinement records.json" docs/reports/fib-robin-boundary/refinement_records.json
```

`temporal_projection.py` 为 FIB §§141–142 的完整剩余时间模型提供可重建的有限目录。默认 `H=5040`，保留实际数量 `6H` 的共同来源，枚举一个零秩周期内的全部纤维及损失闭包，并检查小模数退化情形。只依赖 Python 3.9+ 标准库；运行 `python3 -B docs/reports/fib-robin-boundary/temporal_projection.py --out docs/reports/fib-robin-boundary/temporal_projection.json`，或指定正整数 `--H` 搜索其他模数。输出是精确有限实验，不是一般闭包或 RH 的形式证明。

FIB §§143–144 使用同一程序的 `projection` 与 `seed_10080` 数据。`Fraction` 有理数检验时间 Möbius 壳、旧体/未来体素乘增量；小模数部分直接构造每个探针的纤维平均，独立对照 gcd 公式。种子证书使用带显式尾界的对数展开、调和数的 Euler 常数夹界及指数 Taylor 下和，保留向外取整的有理端点。它可用于搜寻其他 `--H` 的混合秩与候选增量；全称分析结论仍由正文的条件与推导承担。

可移植复现已检查：脚本拷贝到含空格的目录，从另一工作目录、空环境（仅系统 `PATH`）调用 Python 后，默认 JSON 与入库结果逐字节一致；`--H 0` 明确拒绝。平台范围为本次 macOS/Python 运行，未将其泛化为所有平台的实测。

FIB §§147–148 使用新增的 `rank_shell_bounds` 与 `finite_prime_signs` 数据。前者以直接除数和对照时间可见能量的 Möbius 乘积，检查 5040 的单层 7 壳、`37^a*113`（`a=1,2,3,4`）的共同秩 19 壳与 4181 的 113 增量，共六项精确上界、等号及超额检查。后者对 `P={2,3,5,7}` 用整数筛与规范 Zeckendorf 贪心展开，保留 `X=100,1000,10000,100000` 的普通和及数字奇偶加权和，并逐项核对 64 个平方自由倍数计数与其 Möbius 展开。默认运行命令不变；全部旧结果字段保持原值。它们只验证有限实例；碰撞族的极限、固定有限素数集的正均值证明及外部数字正交定理由正文分别说明，不是对实际 Möbius 函数或 RH 的反例。

## Source scale and rank tails (§§162–164)

[`source_scale.py`](source_scale.py) provides exact rational diagnostics for
Robin estimates on the authenticated source `n = 5040*F_j`. Run:

```sh
python3 -B docs/reports/fib-robin-boundary/source_scale.py \
  --out /tmp/fib-robin-source-scale.json
```

The retained result is [`source_scale.json`](source_scale.json). It checks:

- the source-size thresholds and the three five-prime bootstrap stages;
- the explicit index `j = D*(223092870)^10`, where even the true-size
  nine-factor criterion fails but the exact valuation at 29 certifies Robin;
- budget exhaustion (`UNRESOLVED`), and a different certificate from the
  genuinely absent prime 59 using the totient padding identity;
- every arithmetic constant in the rank-tail paper argument, with rational
  bounds for logarithms or powers bracketing `e`;
- 77 high-rank buckets from complete factorizations of `F_j`, `1 <= j <= 48`.

Large-index residues use fast doubling and independent matrix powering.
The adaptive certificate constructs no huge Fibonacci integer. Its optional
`--index` arguments must be positive multiples of `D`; `--prime-limit` and
`--valuation-cap` bound the observations for those requested indices. A zero
residue at the cap is recorded as a lower bound on the valuation, never as an
exact valuation. Missing primes affect the totient padding factor only.
The program rejects optimized Python because assertions verify the evidence.
It uses only the standard library, writes only the requested output, and
records hashes of itself and its two existing arithmetic dependencies.

The universal conclusion in §164 is a paper synthesis of published Axler
inputs, classical Fibonacci ranks and valuations, and a new in-repository
rank-tail derivation. The finite report is not its Lean proof. A current
scoped build of the existing `D5.S3.Arith.FibonacciRank` succeeded; this does
not verify the new analytic composition. The source family is one Fibonacci
term times 5040, not every integer encoded in Zeckendorf form. No RH or
originality claim is made.

## Golden norm and two-term sources (§§165–169)

[`orbit_norm.py`](orbit_norm.py) checks the arithmetic bridges from fixed
nonnegative FIB compositions and legal same-parity two-term sums to prime
exclusions and finite rank carriers. Run with Python 3.9 or newer:

```sh
python3 -B docs/reports/fib-robin-boundary/orbit_norm.py \
  --out /tmp/fib-robin-orbit-norm.json
```

Keep the program beside `kernel_tail.py`, which supplies exact primality and
outward rational logarithm bounds. Only the standard library is required.
The required `--out` names the result file; that selected file is overwritten.
Optimized Python is rejected because assertions verify the diagnostics.
The program writes no bytecode or implicit output beside its sources.

The retained [orbit_norm.json](orbit_norm.json) contains:

- 88,128 exact adjacent-gcd and norm-invariant checks for coefficients
  `0 <= a,b <= 32`, not both zero, and indices `0 <= j <= 80`;
- 97,929 exclusions of primitive-norm prime factors, with valuations
  independently divided out of the actual integer `5040*U_j`;
- 135,680 quantity-fiber residue checks for `1 <= n <= 128` and primes at
  most 97, including 2,593 locally primitive norm roots;
- 5,476 two-term product identities for `4 <= a <= 150`,
  `2 <= b <= a-2`, and `a == b modulo 2`;
- 1,973 actual prime-rank checks from complete sum factorizations with
  `a <= 48`, and 48 pairs sharing an odd factor across the product;
- rational certificates for the effective seed thresholds and the
  same-parity tail bound `a > exp(60)`, whose final linear slack at 60
  is `77/195`;
- the improved fourth-root divisor bound, the new `a > exp(38)` tail
  with slack `62/195`, the exact forced index lower bound
  `17323418604800000000 > 3^38`, and 150 direct checks of the local
  Lucas formulas used to connect the remaining branch to that tail;
- the exponent caps of all 60 positive divisors of 5040, supporting the
  same proof for each multiplier `c | 5040`, including `c = 1`.

The carrier keeps rank 3 separately: `F_32+F_8=F_20*L_12` contains every
core prime but gets its factor 2 only from the Lucas term. Removing that
exception loses an actual prime despite retaining the whole core. The
different-parity example `F_8+F_3=23` also records the limits of the
two-divisor-set argument.

The legal branch example starts at `23=2+21`, whose composition has norm
11, and applies `S*x + d_2` to obtain `99=2+8+89`, of norm 41. Thus an
excluded prime along a fixed seed's linear orbit can reappear after a
legal translation branch. The program retains this obstruction explicitly.

The final program was copied to a path containing spaces and run from an
unrelated working directory with only the system `PATH` in its environment;
its output matched the retained JSON byte for byte. Optimized execution and
an omitted `--out` both returned exit 2 without producing a result. These
portability checks were performed on macOS with Python 3.9; no other
platform run is claimed.

These are finite arithmetic diagnostics. The general norm argument, unit
classification, effective analytic thresholds and universal two-term bounds
are paper deductions using the cited published inputs; the program does
not formally prove them. The unit-norm classification is not separately
enumerated here. The fixed-seed theorem has a seed-dependent threshold;
section 169 connects the five-prime stopping rules to the improved tail
and covers every `c*(F_a+F_b) > 5040` with positive `c | 5040` and legal
same-parity indices, using the common Lucas index's incompatible
divisibility phases at 3 and 7. The case `c = 1` includes the two-term
sums themselves. Opposite-parity
sums and arbitrary multi-term histories remain outside that conclusion.
These paper deductions and the finite program are not a Lean proof of
the full family or of RH; no literature-priority claim is made.

## Opposite-parity sources and joint modular phases

`opposite_phase.py` supports FIB theory §§170–171. Run:

```sh
python3 -B docs/reports/fib-robin-boundary/opposite_phase.py --out /tmp/fib-opposite-phase
```

The retained [opposite_phase.json](opposite_phase.json) exhausts all 14,400
opposite-parity residue pairs modulo the Fibonacci period 240 at modulus
9240. It finds exactly four ordered `(even index, odd index)` pairs, without
assuming which index is larger, and realizes both index orders. It also
checks 100 odd-gap norms and gcds, 9,900 response identities, and 1,980
missing-eleven cases. Twelve lifted periods and two huge actual two-term
sources are checked by independent doubling and matrix-power algorithms.

At period `2D`, all five individual stops fail but the global joint stop
passes. At period `2^26*3^18*5^12*7^9*11^8`, the actual exponents of
`5040(F_(2P-1)+F_(P-2))` at `(2,3,5,7,11)` are `(31,21,13,11,9)`;
the fixed five-factor joint condition also fails. Neither statement is a
Robin counterexample. The universal fixed-prime obstruction uses the paper
period-lifting and growth argument, not extrapolation from these finite runs.
Keep `index_stopping.py` beside this script; both source hashes are recorded.

For the earlier `source_scale.json`, the reported tail constant `63/2560`
is a conservative bound: for `u>10`, use `8/u<4/5` and
`log(u)/u<3/10` in `(6/512)(1+(8+log(u))/u)`. The sharper paper
choice `log(u)/u<1/4` gives `123/5120`; both are below `1/40`.

Theory §172 additionally derives a uniform vanishing Robin ratio for each
fixed multiplier and bounded number of Fibonacci/Lucas factors. Its proof
uses the full rank carrier and the standard subpolynomial divisor bound;
it is a paper consequence of §167, not a conclusion of the finite script.
Zero Fibonacci factors are excluded; Lucas index zero contributes two.

## Finite window resolution and arithmetic progressions (§§173–175)

[`affine_resolution.py`](affine_resolution.py) connects the legal five-window
source to its two golden coordinates and checks actual additive sources:

```sh
python3 -B docs/reports/fib-robin-boundary/affine_resolution.py \
  --out /tmp/fib-affine-resolution.json
```

Python 3.9 or newer and the standard library are sufficient. The script is
standalone, uses exact integers and rational constants, and writes only the
required `--out` JSON file, overwriting that selected file. It rejects `-O`
because assertions check the finite diagnostics. The result records the hash
of the script; [`affine_resolution.json`](affine_resolution.json) is the
retained default output.

The default ranges check:

- All 8,848 nonzero legal bit patterns in one through six windows, including
  composition reconstructed independently by five-window Horner updates,
  exact golden-coordinate comparisons, and 79,632 low-null shift identities.
- All 1,680 nonzero coefficient pairs in `[0,40]^2`, with 1,955 primitive
  norm-prime bounds and the separate small-core bound for 171 unit seeds.
- 10,080 arithmetic-progression sums with `3 <= a <= 30`, `1 <= d <= 12`,
  `1 <= h <= 30`, and 4,377 actual prime-carrier checks from complete
  factorizations when the largest occupied index is at most 42.
- 2,352 opposite-parity identities with largest index at most 100, plus
  573 actual prime-phase checks when that index is at most 36.
- The full 7,866 local cases with prime below 100, excluding 2 and 5, and
  largest index at most 40. These include 210 nonunit denominators and
  323 cases where the squared rank condition selects only the difference,
  so the sum's divisibility does not follow.

Ranks are computed using the classical `z(p) | p-(5/p)` bound for odd
`p != 5` and the zero-index divisibility criterion, modular fast doubling,
and prime-factor reduction with minimality checks; ranks at 2 and 5 are
handled separately. This rank computation is
an arithmetic diagnostic using the known bound, not an independent proof
of that bound. The example `F_11+F_6=97`, of rank 49, remains outside every
power-of-two enlargement of the four indices 11, 6, 17, 5. The example
`F_8-F_3=19`, with sum 23, records the sign information lost by squaring.

Sections 173–175 are paper deductions, with no new Lean verification of
their analytic composition. The window result excludes the independent
unit bit and requires low-end null windows; the progression result fixes
the multiplier while allowing unboundedly many regularly spaced terms.
Neither applies to arbitrary five-window histories or proves RH. The
Möbius relation uses the complete quadratic residue algebra and explicitly
requires its denominator to be a unit.

## Two-factor sources and all-index progression bounds (§176)

The same script now also checks 36,000 valuation bounds for `F_t` and
`L_t`, `1 <= t <= 2000`, at the nine primes through 23. First-rank data
are exhaustively checked up to each stated rank. The individual Robin
stops remain published external inputs; enumerating valuations does not
prove those stopping theorems.

If all nine stops fail for `c*V`, with positive `c | 5040` and
`V | A_r*B_s` for two positive-index Fibonacci/Lucas factors, the general
valuation bounds force the same index product `r*s` to be divisible by
`2^13*3^9*5^8*7^4*11^4*13^3*17^3*19^3*23^2`. Its exact comparison with
`(49/18)^80` forces `max(r,s) > exp(40)`. The existing rank tail then
applies when the actual `V >= F_max(r,s)`. Thus §176 gives a paper
all-index conclusion for those two-factor divisors and, as a corollary,
every `c*sum(F_(a+2*d*j), j=0..h-1) > 5040` with `a >= 3`, `d,h >= 1`
and positive `c | 5040`. The explicit growth hypothesis cannot be dropped.
Arbitrary multipliers retain only the earlier eventual bound.

The large legal progression with `K=44375007600000`, `a=K+2`, `d=2`,
`h=K` has sum `F_(3K)*F_(2K)`. Fast doubling and separate golden-ring
binary powering confirm its exact valuations without constructing the
integer. Its first five valuations are `(23,15,11,9,8)` after multiplication
by 5040, and even the true-size five-factor test fails. Its valuation at
17 is exactly two, so the new direction certifies Robin. The script retains
both the failed sufficient condition and the successful new stop.

The final script was rerun from an unrelated directory, with a filename
containing spaces and only the system PATH; output matched byte for byte.
Optimized execution and missing `--out` were rejected with exit 2. These
portability checks were performed on macOS/Python 3.9. All earlier result
fields were preserved, apart from the intentionally updated source hash.
No new Lean proof of §176 or RH is claimed.

## Quadratic characters of actual FIB sources (§§177–181)

[`character_slice.py`](character_slice.py) checks the source identities and
finite character algebra used by the new Euler-weight estimate:

```sh
python3 -B docs/reports/fib-robin-boundary/character_slice.py \
  --out /tmp/fib-character-slice.json
```

It is a standalone Python 3.9+ standard-library program. The required
`--out` names the sole output file, which is overwritten; optimized Python
is rejected because assertions verify the diagnostics. The retained default
result is [`character_slice.json`](character_slice.json), including the
script hash and explicit finite ranges.

For a legal opposite-parity sum `V = F_a + F_b`, two square identities force
every actual odd prime divisor, including 5, into quadratic-residue classes
for `D = (-1)^b L_(a-b)` and `E = -L_(a+b)`. The first may be a square and
must then be excluded from the nonprincipal-character argument; the second
is always negative. The estimates use the actual prime support of the same
integer. They can use the smaller available fundamental discriminant,
rather than the full size of either Lucas value.

The paper estimate for a nonprincipal real character modulo `m` is
`P_chi(x) <= exp(8)*sqrt((1+log(x))*(2+log(m)))`, for `x >= 2`.
It uses only absolute Euler products to the right of 1, a Chebyshev bound,
and cancellation over a full character period. Neither finite character
checks nor exact Euler-factor identities certify this infinite estimate.
No PNT, GRH or ineffective zero-free-region constant is assumed.

For each fixed positive multiplier `c`, the paper deduction gives a uniform
vanishing Robin ratio for opposite-parity sums with gap `k = o(log(a))`.
The cited published classification of Lucas squares handles the exceptional
square branch through its Fibonacci factorization. This is an eventual
bound on a specified family, not an all-index theorem for arbitrary gaps.
The more general sufficient condition controls the fundamental discriminant
relative to `log(log(c*V))`.

For a general nonzero nonnegative ATOM composition, first remove its
coordinate gcd `g`. The same argument applies to the primitive quantity
`u = 2*a + 3*b` and its golden norm when the resulting `D` is nonsquare,
but the multiplier is now `C = c*g`. Its cost `C/phi(C)` cannot be omitted.
A fixed primitive seed `(1,0)` and arbitrary `g` already encode every even
integer. The primitive example `(16,29)` instead has square `D = 121`,
so the nonprincipal-character premise also cannot be dropped in that
broader family.

These additions are paper derivations and finite diagnostics. Their analytic
composition has not been proved in Lean; no RH proof or literature-priority
claim is made. The reusable formal gap is the uniform weighted tail estimate
for a zero-mean periodic function, followed by the character Euler-product
comparison. The formalization can reuse existing Chebyshev and character-sum results;
no new bind-only declarations are retained.

Default diagnostics check 6,162 opposite-parity pairs through index 160,
with 9,678 actual odd prime-divisor checks through prime 500, including
1,232 at prime 5. A separate complete-factorization window through index
44 checks all odd prime factors of 420 sums, including 348 checks beyond
that prime cutoff. The character/algebra checks cover 22 full induced
character periods and 23 quadratic residue algebras. The primitive-ATOM
window `[0,40]^2` checks 1,680 nonzero seeds and 2,048 actual odd-prime
incidences. These ranges and the explicit principal-character boundary are
recorded in the JSON; no finite window classifies all Lucas squares.

The final script was independently rerun from a different directory, with
its filename containing spaces and an environment containing only system
PATH. Output matched the retained JSON byte for byte. Optimized execution,
missing `--out`, and attempting to overwrite the program were rejected with
exit 2. These execution checks were performed on macOS with system Python.
The square classification is cited in the
[primary-source note](../../../Library/Scale/bugeaud2006fibonaccipowers.md).

The [Mertens progression note](../../../Library/Scale/languasco2008mertensprogressions.md)
records the classical fixed-modulus background and why that asymptotic
alone cannot replace the explicit estimate with a moving discriminant.
