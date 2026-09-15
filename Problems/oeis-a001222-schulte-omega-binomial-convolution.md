---
slug: oeis-a001222-schulte-omega-binomial-convolution
bibkey: schulte2018a001222
doi: null
url: https://oeis.org/A001222
triage: theorem
motivation_gids:
  - D5/S3/Arith/SchulteOmegaBinomialConvolution
---

# Schulte's Ω/ω binomial convolution

## Problem

OEIS A001222, NAME (`%N`, verbatim):

> Number of prime divisors of n counted with multiplicity (also called big omega of n, bigomega(n) or Omega(n)).

COMMENT (`%C`, verbatim):

> Conjecture: Let f(n) = (x+y)^a(n), and g(n) = x^a(n), and h(n) = (x+y)^A046660(n) * y^A001221(n) with x, y complex numbers and 0^0 = 1. Then f(n) = Sum_{d|n} g(d)*h(n/d). This is proved for x = 1-y (see Dressler and van de Lune link). - _Werner Schulte_, Feb 10 2018

The A001222 offset (`%O`) is `1,3`. A046660, NAME (`%N`, verbatim):

> Number of prime factors of n counted with multiplicity minus number of distinct prime factors. Omega(n) - omega(n).

A001221, NAME (`%N`, verbatim):

> Number of distinct primes dividing n (also called omega(n)).

Write Ω for `ArithmeticFunction.cardFactors` and ω for
`ArithmeticFunction.cardDistinctFactors`. The full-quantifier reading is

```lean
theorem result (x y : ℂ) (n : ℕ) (hn : 0 < n) :
    (x + y) ^ Ω n = ∑ d ∈ n.divisors,
      x ^ Ω d * ((x + y) ^ (Ω (n / d) - ω (n / d)) * y ^ ω (n / d))
```

Every complex pair x, y and every positive natural n are quantified.
The sum uses all positive divisors, including 1 and n; `n / d` is natural
division and is exact for these divisors. Exponent subtraction is natural
subtraction; ω(m) ≤ Ω(m) follows from deduplication of the prime-factor
list, so it equals the ordinary nonnegative difference. Natural powers
implement `0^0 = 1`. The statement includes n = 1 and allows x, y, and x+y
to vanish, without any nonzero-base assumption.

Only the general x, y assertion in the quoted Conjecture sentence is
settled. The historical x = 1 − y case is Dressler and van de Lune,
Proc. AMS 41 (1973), 403–406, doi 10.1090/S0002-9939-1973-0340191-8.
Other OEIS assertions and historical priority are outside the formal claim.

## Motivation

The independent question is Schulte's published 2018 binomial convolution,
a first-tier external named small conjecture. It relates A001222, A001221,
and A046660 uniformly over both complex parameters and all positive indices.
`question_answered`: the A001222 `%C` assertion quoted above, preregistered
in issue #8126.

`proof_shape: bind-only`; `escape_witness: null`;
`admission_basis: open-problem-resolution`. The identity follows by direct
application of pinned Mathlib count formulas, multiplicative extensionality,
and a geometric-sum identity, with finite-sum and algebraic normalization.
All supporting facts are local `have`s inside the single public theorem
`result`; there are no helper theorem declarations, public definitions, or
direct frozen project dependencies. The admission basis is the external
open-problem settlement exception; its literature premises are bounded by
the search readings below.

`computational_content.kind: none`: the only declaration is an unbounded
symbolic identity for all complex x, y and positive natural n. It is neither
a bounded enumeration, a checker, a numerical reduction, nor a certified
finite instance. Other computational-utility fields are
`not-applicable(kind=none)`; the finite symbolic check is not a proof premise.

## Gap

Literature readings of 2026-09-16: OEIS still labels the A001222 `%C` line
Conjecture and states only x = 1 − y is proved. OpenAlex for
`Dressler van de Lune number of prime factors divisor sum` returned 3
unrelated hits; the Math.SE API returned 0. The arXiv API gave no response
and was not searched. No literature proof of the general case was found in
these searched surfaces. These readings do not establish exhaustive
historical openness or priority.

Repository prior art at `origin/dev = e67699dc905b37ef05859ed0075831fd01b1e1ce`:
the query `cardFactors|cardDistinctFactors|A001222|Dressler` over D5,
Blueprint, Library, and Problems returns 187 matching lines in 33 files,
including 18 Lean modules with existing frozen state pins. The matching
frozen modules and their distinct conclusions are:

| Frozen modules | Why they do not cover the target |
| --- | --- |
| `DivisorPairProductPrimePreimages` | Classifies preimages of prime divisor-pair sums. |
| `DistinctPrimeFactorCountBound` | Bounds distinct prime counts using the radical and a logarithm. |
| `MultiplicativeComplexityActivation` | Gives factorization sums, finite support, and zeta occupancy laws for Ω. |
| `PrimeFactorCountGeneratingFunction`, `PrimeFactorCountMoments` | Give a distinct-count Euler product and zeta-distribution moments, with real parameters and analytic hypotheses. |
| `DivisorCountPrimeFactorBound`, `DivisorCountRadicalCoincidence` | Compare divisor counts with prime-factor corrections or the radical. |
| `DivisorParity` | Describes the prime-factor parity sign of divisor reflection. |
| `EightStepAbundancy` | Identifies an abundancy maximum at eight prime factors. |
| `OmegaGreedyPermutation` | Proves surjectivity of an omega-indexed greedy sequence. |
| `SchulteLiouvilleCubeMobius` | Proves the separate A299406 Liouville/cube-Möbius convolution identity. |
| `MarkedPrimeWordReadoutDeletion` | Gives deletion identities for marked prime-word readouts. |
| `StrictDivisorChainCount`, `StrictDivisorChainMobius` | Count strict divisor chains and their alternating Möbius sum. |
| `IanakievPrimeExponentSumIterationReachesFive`, `PrimeExponentRecordLimitOne` | Treat prime-exponent iteration and record sequences. |
| `PrimeGoldenBigradedChronologicalSignature`, `PrimeWordAntipodeParityStepBridge` | Treat prime-word bigradings and Liouville parity, including the specialized base −1. |

No Ω/ω binomial convolution identity or multiplicativity lemma for
`x ^ Ω n` with an arbitrary complex base was found in this repository scope.

Pinned Mathlib, commit `db584cd6d46c92f209a44c0f1c829460d327499d`, contains
`cardFactors_mul`, `cardDistinctFactors_mul`, the two prime-power count
formulas, `IsMultiplicative.eq_iff_eq_on_prime_powers`, `geom_sum₂_mul_add`,
and `geom_sum₂_comm`. The name `cardDistinctFactors_le_cardFactors` is absent;
the bound follows from `List.dedup_sublist.length_le`. No statement of the
full target was found in the arithmetic-function and number-theory search.
`dominating_theorem_search: not-found-in-searched-scope`; the component
declarations are used directly.

The SymPy check of the final statement finds zero nonzero residual
polynomials for `1 ≤ n ≤ 300`. This finite result does not establish the
unbounded theorem.

Pre-registration issue #8126 (created 2026-09-15T16:35:21Z) precedes the first proof attempt (2026-09-15T16:36:34Z)

## Route

1. Extend `F(z,n) = z^Ω(n)` and
   `H(n) = (x+y)^(Ω(n)−ω(n)) y^ω(n)` by zero at n = 0.
   The additive factor-count laws at coprime positive inputs show that
   F and H are multiplicative. Hence both `F(x) ⋆ H` and `F(x+y)` are
   multiplicative, where ⋆ is Dirichlet convolution.
2. At a prime power p^e, the divisor sum is
   `Σ_{i=0}^e x^i H(p^(e−i))`.
   Since Ω(p^k) = k and ω(p^k) = 1 for positive k, this equals
   `x^e + y · Σ_{0 ≤ i < e} x^i (x+y)^(e−1−i)`.
   For y ≠ 0 it can also be written
   `x^e + y · (((x+y)^e − x^e) / y)`.
   The proof uses the division-free identity `geom_sum₂_mul_add`, with
   `geom_sum₂_comm`, so y = 0 and e = 0 are included.
3. Multiplicative extensionality lifts equality at all prime powers to
   equality of arithmetic functions. Evaluation at n > 0 removes the zero
   guards and gives the stated positive-divisor sum.

## Falsifier

A complex pair x, y and positive natural n with a nonzero difference
between the binomial power and the divisor sum would refute the assertion.
A mismatch between A001222/A001221 and the two formal factor-count
functions, or between A046660 and their nonnegative difference, would
invalidate the OEIS correspondence. Bounded symbolic agreement alone
cannot rule out a counterexample at a larger index.

## Evidence

The final module is `D5/S3/Arith/SchulteOmegaBinomialConvolution.lean`.
Its only public declaration is `result`.

- Final single-file `lake env lean` exits 0 with no Lean diagnostics.
  Wall time is 3.35 seconds, measured with a warm cache while import-deletion
  checks ran concurrently. The final module has 91 lines and 4166 bytes;
  its containing directory has 47 immediate Lean files.
- `tools/scripts/agent/header-check.sh` exits 0. The seven-line header has
  generality G, utility none, a 79-character digest payload, and a
  93-character physical digest line.
- A scratch copy of the final source with profiling and the axiom query
  exits 0. The axiom closure of `result` is exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  or new axiom occurs in the final source.
- The profile reports 42.8 ms of cumulative kernel type checking and
  21.98 seconds wall time, including detailed profiler output and the axiom
  query. Measurements use Lean v4.33.0 on macOS 26.6.2 arm64 with a warm
  cache. Peak resident memory was not measured.
- Python 3.9.6 / SymPy 1.14.0 exits 0 for the exact symbolic check of
  `1 ≤ n ≤ 300`: 300 residual polynomials over ZZ[x,y], zero nonzero
  residuals. Factorization multiplicities and distinct factors implement
  Ω and ω; subtraction and divisor quotients have their natural-number
  meanings. This computation is independent of the Lean proof.

Deleting each final direct import separately gives these bare Lean exits:

| Deleted import | Exit |
| --- | --- |
| `Mathlib.NumberTheory.ArithmeticFunction.Misc` | 1 |
| `Mathlib.Data.Complex.Basic` | 1 |

There is no direct D5 or umbrella tactic import. Source-level Scribe
selfchecks match the single theorem, binder symbols, complex domain,
natural powers, natural subtraction, and natural division. Parentheses
use one helper, named count functions use `Operatorname` and `Grp`, and
no relation is a `LatexGroup.Items` entry.

## Triage

`theorem`; resolution `proved` for the general complex-parameter binomial
convolution at every positive natural index under the stated sequence
identifications.

## ASSUMED-UNVERIFIED

The literature check of 2026-09-16 consisted of reading the OEIS A001222
entry (the `%C` line is still marked Conjecture and the entry states that
only x = 1 − y is proved, citing Dressler and van de Lune 1973), an
OpenAlex query (`Dressler van de Lune number of prime factors divisor sum`:
3 hits, none about this identity), a Math.SE API query
(`"A001222" conjecture Schulte`: 0 hits) and a formal-conjectures code
search (0 hits); pre-registration issue #8126 was created at
2026-09-15T16:35:21Z, before the first proof attempt at
2026-09-15T16:36:34Z. The arXiv API gave no response and was not searched.
Historical openness outside these surfaces and exhaustive novelty or
priority are unverified. The sequence identifications are the stated
source bridge; the Lean theorem proves the displayed arithmetic identity.
