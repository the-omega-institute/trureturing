---
slug: h384819-primepower
bibkey: hanna2025a384819
doi: null
url: https://oeis.org/A384819
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result
---

# Hanna's prime-power correction formula

## Problem

Paul D. Hanna, OEIS A384819, approved revision 14, NAME:

> Nonnegative numbers a(n) < n for n >= 1 such that exp( Sum_{n>=1} (n^2 - a(n))*x^n/n ) is a power series with integral coefficients.

The sole COMMENTS conjecture is:

> Conjecture: a(p^n) = p - 1 when p is prime for n >= 1.

All series are formal over the rationals. The offset is 1,3; the unused value
$a(0)$ is unconstrained. The conclusion quantifies over every integer sequence
satisfying the defining condition, every natural prime $p$, and every natural
exponent $r\ge1$.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Nonnegative numbers $a(n)<n$ for $n\ge1$ | `IsCorrection`: integer-valued sequence and both positive-index bounds | Literal |
| Integral coefficients of the specified formal exponential | `IsCorrection`: literal `PowerSeries.mk`, rational division, `PowerSeries.subst`, `PowerSeries.exp`, and reused `IntegralSeries` | Literal; the exponent's constant coefficient is zero |
| $p$ prime | `claim`: `Nat.Prime p` | Includes 2 |
| $n\ge1$ | `claim`: positive natural exponent $r$ | Bound variable renamed |
| $a(p^n)=p-1$ | `result` proves `claim` | Unbounded in both parameters |
| Every solution; natural index zero | Universal sequence binder and an unused $a(0)$ | No choice of a canonical solution and no added restriction |

## Motivation

The settling GID is `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.result`.
It resolves the source's prime-power assertion rather than extending a finite
table. Admission is `open-problem-resolution (#21787; Proved)`; every theorem
is conservatively classified `bind-only`, with no independent escape witness.
The literal exponent and exponential are inlined in `IsCorrection`; proofs
reuse `logarithmicInput` and `exponentialSum` through definitional correspondence.

## Gap

Preregistration [#21787](https://github.com/the-omega-institute/trureturing/issues/21787)
records the source and literature screen. Its inspected OEIS revision retains
the conjecture and links no source paper or arXiv identifier. The inspected
Euler/Dold and Witt-vector sources supply classical background rather than
this bounded square-correction conclusion. The inspected scope contains no
prior settlement; completeness is `ASSUMED-UNVERIFIED`.

## Route

Put $b_m=m^2-a(m)$. Formal integrality yields an integer Euler ledger $(e_d)$
with $b_m=\sum_{d\mid m}d e_d$ for positive $m$. This is the necessary
integrality direction in the reused `integral_input_ledger`, specialized by
`correction_ghost`. The reused `divisor_ghost_gauss`, specialized by
`prime_power_difference`, gives $p^r\mid b_{p^r}-b_{p^{r-1}}$.
The bound at 1 forces $a(1)=0$. At $p$, the unique residue in $[0,p)$ is
$p-1$. For $r\ge2$, both square terms are divisible by $p^r$, so the two
corrections are congruent modulo $p^r$. Their bounds put them in the same
representative interval, hence they agree. `bounded_prime_powers` performs
this induction; `result` combines the three helpers.

## Falsifier

A bounded integral correction and a prime $p$ with positive $r$ for which
$a(p^r)\ne p-1$ would falsify the conjecture. A finite test or a failed
registration is neither such a correction nor a refutation.

## Evidence

The Lean source is `D5/S3/Arith/Congruence/HannaPrimePowerCorrection.lean`;
its public theorem is `D5.S3.Arith.Congruence.HannaPrimePowerCorrection.result`.
The Scribe gives the complete defining expression and expanded settling
proposition. No frozen owner is changed or published.

Escape audit unfinished:
[#25058](https://github.com/the-omega-institute/trureturing/issues/25058).
The universal sequence and formal-integrality hypothesis have no delivered
four-slot registration; the exact reconstruction, observational dependence,
and variation/sensitivity evidence remain missing. No `declared_validated`
registration is claimed.

### Finite source checks

The pinned experiment is
[trureturing-experiments, hanna-a384819-primepower](https://github.com/the-omega-institute/trureturing-experiments/tree/0916ed2028a0f5b6655667b45b620902fe84fcd4/docs/reports/hanna-a384819-primepower).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/hanna-a384819-primepower/check.py`;
exit 0. Script SHA-256:
`f36ce92f3986ede4ecae3c75d79e10caf2bd083ddb5e5d7994412da3c92bc86b`.
Its bytes equal `check.py` at the linked immutable revision. All 520 published
A384819 terms ($1\le n\le520$), all 41 displayed A384820 coefficients
($0\le n\le40$), and all 340 prime-power indices at most 2048 match.
The coefficient recurrence and divisor-ledger recursion agree through 2048;
the signed-binomial Euler product agrees through degree 96 and the rational
Taylor expansion through degree 32. These are finite computations.

## Triage

| Item | Status and evidence kind | Evidence |
| --- | --- | --- |
| Integrality alone supplies the necessary integer divisor-sum ghost identity; bounds are used only afterwards | Proved; kernel-checked owner | `HannaDiagonalGhostPowerIntegrality.integral_input_ledger` has only formal integrality as its premise; `correction_ghost` applies it to the integral component |
| All primes, including 2, and all positive exponents; $a(0)$ irrelevant | Proved; kernel-checked | Full statement of `HannaPrimePowerCorrection.result` |
| No nonnegative Euler exponents or positive exponential coefficients | Proved; kernel-checked | Complete hypotheses of `result`, and integer-valued ledger from `correction_ghost` |
| The bounded integral defining condition is inhabited by the quotient/remainder Euler-ledger construction | Proved in prose | The construction and formal-series argument below; no additional retained Lean theorem |
| 520 source terms, 41 exponential coefficients, and 340 prime powers through 2048 match | Computed | Pinned experiment, command, exit 0 and SHA-256 in Evidence; no assertion beyond its stated ranges |
| Analogous prime-power assertion for weights $m^k$, $k\ge2$ | Open | Separate adjacent assertion; neither formalized nor settled here |
| Uniqueness on all positive indices and a closed composite-index formula as additional Lean results | Open | No such additional Lean results are delivered |

### What the settlement shows

The decisive mechanism is that integrality supplies divisibility, while the
bounded representative interval upgrades congruence to equality. It covers
all primes and positive exponents without positivity assumptions on either
Euler exponents or exponential coefficients (`result`, kernel-checked).
The source associates A384820 with the resulting integral series, and states
no further theorem depending on its COMMENTS conjecture.

For nonvacuity, the following is a proof in prose. Recursively for $m\ge1$,
let $S_m=\sum_{d\mid m,\ d<m}d e_d$ and take $a(m)$ to be the least
nonnegative residue of $m^2-S_m$ modulo $m$. Then
$e_m=(m^2-S_m-a(m))/m$ is an integer and $0\le a(m)<m$.
The formal product $F=\prod_{d\ge1}(1-x^d)^{-e_d}$ is well-defined over
$\mathbb Z[[x]]$: integer powers and inverse powers have integral binomial
coefficients, and each coefficient depends on finitely many factors.
Its constant coefficient is 1 and its logarithmic derivative has coefficient
$\sum_{d\mid m}d e_d=m^2-a(m)$ at $x^m$. The specified formal exponential
has the same logarithmic derivative and constant coefficient. Over
$\mathbb Q[[x]]$, equality follows recursively from the differential equation
$m F_m=\sum_{j=1}^m b_j F_{m-j}$. Thus this product is the required integral
exponential and the defining condition is inhabited. This paragraph proves
existence in prose; it is not an extra kernel-checked claim.

Weights $m^k$ for $k\ge2$, all-positive-index uniqueness as a retained Lean
result, and a closed composite-index formula remain outside this settlement.

## ASSUMED-UNVERIFIED

Literature completeness and absence of every external prior settlement are
`ASSUMED-UNVERIFIED`. The preregistration's OpenAlex and Semantic Scholar
requests were rate-limited; global arXiv full-text discovery timed out, and
bounded metadata screens do not constitute exhaustive search. No originality
or first-publication priority is inferred. Four-slot audit evidence remains
unfinished under #25058.
