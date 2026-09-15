---
slug: oeis-a133907-ordowski-binomial-power-sum-least-prime
bibkey: ordowski2018a133907
doi: null
url: https://oeis.org/A133907
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime
---

# Ordowski's binomial and power-sum least-prime conjecture

## Problem

OEIS A133907, NAME (`%N`, verbatim):

> Least prime number p such that binomial(n+p, p) mod p = 1.

Ordowski's COMMENT (`%C`, verbatim):

> Conjecture: a(n) is the smallest prime p such that Sum_{k=1..n} k^(p-1) == n (mod p). Thus a(n) >= A317358(n). - _Thomas Ordowski_, Jul 29 2018

The offset is `%O 1,1`. The AUTHOR line (`%A`, verbatim) is:

> _Hieronymus Fischer_, Oct 20 2007

The related unsigned COMMENT (`%C`, verbatim) is:

> Also the least prime number p such that p divides floor(n/p) or p > n.

Define `a n = sInf {p : Nat | p.Prime ∧ (n+p).choose p ≡ 1 [MOD p]}`.
For each natural `n`, let
`S(n) = {p : Nat | p.Prime ∧ (∑ k ∈ Finset.Icc 1 n, k^(p-1)) ≡ n [MOD p]}`.
The full-quantifier reading is: for every `n : Nat`, if `0 < n`, then
`a n ∈ S(n)` and, for every `q : Nat`, `q ∈ S(n)` implies `a n ≤ q`.
Thus membership includes primality and the sum congruence, and leastness
compares against every prime satisfying that congruence. The exact Lean type is:

```lean
theorem result (n : ℕ) (_hn : 0 < n) :
    IsLeast {p : ℕ | p.Prime ∧
      (∑ k ∈ Finset.Icc 1 n, k ^ (p - 1)) ≡ n [MOD p]} (a n)
```

The sum includes both endpoints, division is natural-number floor division,
and `p - 1` is natural subtraction. The unused hypothesis `_hn : 0 < n`
retains the OEIS domain; no strengthened premise is introduced. The defining
prime set is nonempty, so the natural infimum is an attained least element.
Only the `Conjecture:` sentence is settled. The clause
`Thus a(n) >= A317358(n)` is a consequence, not claimed separately, and the
unsigned comment receives no separate public theorem or resolution claim.

## Motivation

The independent question is Ordowski's published least-prime characterization
for every positive natural index, registered in issue #8099. It is a first-tier
small OEIS conjecture under the external named open-problem route. It connects
a binomial congruence to a power-sum congruence without changing the sequence's
original definition.

## Gap

Readings of 2026-09-15: OEIS still marks the `%C` line `Conjecture`. OpenAlex
search for `A133907` returned 0 results, and the Math.SE API returned 0 results.
The arXiv API gave no response and was not searched. No literature proof was
found in those searched surfaces; they do not establish exhaustive historical
openness or priority.

At the historical repository prior-art reading, `origin/dev = fe47b6c24b`:
`git grep A133907` found 0 matches. The query over D5, Blueprint, Library and
Problems at that snapshot has 0 matches (exit 1). Existing Ordowski
modules concern the A126762 and A239293 conjectures. Eight D5 modules already
use the Lucas step; the pinned theorem is reused directly here, with no D5
import or new wrapper declaration.

Pinned Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`
(v4.33.0) contains `Choose.choose_modEq_choose_mod_mul_choose_div_nat`,
`ZMod.pow_card_sub_one`, and `Nat.Ioc_filter_dvd_card_eq_div`.
No statement of the complete target was found in the searched repository or
pinned Mathlib scope (`dominating_theorem_search: not-found-in-searched-scope`).
The three independently searched least-prime characterizations, using the
binomial congruence, power-sum congruence, and `p ∣ floor(n/p)`, agree for every
`1 ≤ n ≤ 2000` with zero exceptions; the 31-term data prefix matches.

Pre-registration issue #8099 (created 2026-09-15) precedes the first proof attempt (2026-09-15T13:44:01Z)

## Route

1. For every prime `p`, instantiate
   `Choose.choose_modEq_choose_mod_mul_choose_div_nat` to obtain
   `C(n+p,p) ≡ floor(n/p) + 1 (mod p)`.
2. Apply `ZMod.pow_card_sub_one` termwise: `k^(p-1)` has residue zero at
   multiples of `p` and one elsewhere. The inclusive interval `1..n` has
   `floor(n/p)` multiples by `Nat.Ioc_filter_dvd_card_eq_div`. Therefore
   `Σ k^(p-1) ≡ n - floor(n/p) (mod p)`, with the subtraction performed
   in the residue field `ZMod p`.
3. Each congruence predicate is equivalent to the residue of `floor(n/p)`
   being zero, namely `p ∣ n / p`. Hence the prime candidate sets coincide.
4. A prime `p > n` makes `n / p = 0`, proving nonemptiness of the binomial
   set. Apply `Nat.sInf_mem` and `Nat.sInf_le` through the pointwise
   equivalence to obtain membership and minimality in the power-sum set.

The theorem's `proof_shape` is **bind-only**, its `escape_witness` is null,
and its `admission_basis` is **open-problem-resolution** under issue #8099.
The upstream instantiations and normalization remain local `have` steps
inside `result`. There are no auxiliary theorem declarations or direct
frozen D5 dependencies. The public surface is exactly the definition `a`
and the theorem `result`.

The computational-content classification is `none`: the definition and
unbounded symbolic theorem are neither bounded enumeration, a certified
finite instance, checker infrastructure, nor a conditional numerical
reduction. The numeric comparison is fault-detection evidence and is not
a premise of the Lean proof.

## Falsifier

A positive natural `n` for which `a n` is not prime or does not satisfy the
power-sum congruence would falsify membership. A prime `q < a n` satisfying
that congruence would falsify minimality. A prime `p` for which either
congruence disagrees with `p ∣ n / p` would invalidate the pointwise route.
Bounded numerical agreement alone cannot establish the universal claim.

## Evidence

- Final module: `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.lean`;
  exactly one definition and one theorem, 70 lines and 3026 UTF-8 bytes.
  Its directory contains 43 Lean files.
- Single-file `lake env lean --profile` on the final module: exit 0;
  wall time 10.371 seconds, type checking 7.19 milliseconds, zero warnings.
  Environment: Lean v4.33.0, arm64 macOS, warm dependency cache, with
  independent Lean checks running concurrently.
- `tools/scripts/agent/header-check.sh` on the final module: exit 0;
  seven-line header, generality G, digest payload 71 characters and
  digest physical line 85 characters.
- The final-source `#print axioms` audit exits 0. Both `a` and `result`
  depend on exactly `[propext, Classical.choice, Quot.sound]`.
- Deleting `Mathlib.Data.Nat.Choose.Lucas` alone from the final source
  makes Lean exit 1; deleting `Mathlib.FieldTheory.Finite.Basic` alone
  makes Lean exit 1. These are the only direct imports.
- Independent numeric comparison: exit 0, all 2000 indices `1 ≤ n ≤ 2000`,
  three least-prime characterizations, zero exceptions, matching 31-term
  prefix. The candidate search covers 304 primes through 2003; the largest
  least prime in this window is 1997.

## Triage

`theorem`; resolution `proved` for Ordowski's `Conjecture:` sentence at every
positive natural index. The Scribe theorem node carries the corresponding
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

The dated OEIS locator, external search counts, and issue #8099 creation and
first-attempt timestamps were not independently re-fetched during the
offline verification. The arXiv surface was not searched because its API
gave no response. A proof outside the stated search surfaces remains an
unexcluded alternative; no exhaustive novelty or priority claim is made.
Scribe compilation, emitted Markdown validation, whole-tree Lean reports,
repository admission, and freezing are not verified by the single-file
checks listed here.
