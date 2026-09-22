---
slug: oeis-a249759-krizek-sigma-prime-fermat-mersenne
bibkey: krizek2014a249759
doi: null
url: https://oeis.org/A249759
triage: theorem
motivation_gids:
  - D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.sigma_one_prime_imp_prime_pow
  - D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.result
---

# Krizek's Fermat-Mersenne classification for A249759

## Problem

OEIS A249759, revision #40 Sep 10 2025 16:53:46, records these lines
verbatim:

> %N A249759 Primes p such that sigma(p-1) is a prime q.
>
> %S A249759 3,5,17,65537
>
> %C A249759 Conjectures: 1) sequence is finite; 2) sequence is a subsequence of A019434 (Fermat primes); 3) sequence consists of Fermat primes p such that sigma(p-1) is a Mersenne prime; 4) a(n) = (A249761(n)+3)/2.
>
> %A A249759 _Jaroslav Krizek_, Nov 13 2014

Items 2 and 3 have the following formal joint statement, where `σ 1` is
Mathlib's sum-of-divisors function:

```lean
open scoped ArithmeticFunction.sigma in
theorem result {p : ℕ} (hp : p.Prime) (hq : (σ 1 (p - 1)).Prime) :
    (∃ m : ℕ, p = 2 ^ 2 ^ m + 1) ∧
      (∃ r : ℕ, r.Prime ∧ σ 1 (p - 1) = 2 ^ r - 1)
```

Natural subtraction does not weaken this statement. `Nat.Prime.two_le`
gives `2 ≤ p`, and the proof separately rules out `p = 2` from
`σ 1 (2 - 1) = σ 1 1 = 1`, which is not prime.

Not claimed: item 1 is a finiteness statement about the resulting class of
Fermat primes and remains open. Item 4 concerns the definition of the
separate sequence A249761. Neither item appears on the Lean delivery surface.

## Motivation

The independent question is items 2 and 3 of Krizek's published 2014
conjecture, preregistered in issue #8164 before the proof probe. The result
places every member of A249759 in the Fermat-prime sequence A019434 and
shows that its divisor sum is a Mersenne prime.

Both public declarations have `proof_shape: content` and
`admission_basis: escape-witness`. The escape witness is the reusable public
theorem `sigma_one_prime_imp_prime_pow`: for arbitrary natural `m`, primality
of `σ 1 m` forces `m` to be a positive power of one prime. It is a direct
constant dependency of `result`, is not supplied by a pinned theorem, is not
a restatement of the prime-`p` classification, and remains on the live path
that produces both final conjuncts.

`computational_content.kind: none` for both declarations. They are unbounded
symbolic theorems, not bounded enumerations, checkers, numeric reductions, or
certified finite instances. Their direct frozen prerequisite list is empty.

## Gap

The 2026-09-15 literature reading found revision #40 of A249759 still using
the label `Conjectures:` for all four items. The entry contains no `%D`
bibliography and no `%H` literature link. No published proof or refutation
of items 2 and 3 was found on that source surface.

Repository and pinned-library searches found no earlier A249759 settlement
and no theorem of either exact inverse shape
`(σ 1 m).Prime → ∃ q k, q.Prime ∧ 1 ≤ k ∧ m = q ^ k` or
`(σ 1 m).Prime → IsPrimePow m`. The two exact `#find` queries returned zero
results. A third-party GitHub Lean code search for `A249759` also returned
zero results. The pinned library does provide the forward divisor-sum
factorization and the two Fermat/Mersenne exponent lemmas used after the new
inverse theorem. `dominating_theorem_search: not-found-in-searched-scope`.

The seven existing `Krizek*` modules settle different OEIS assertions,
including the sibling sigma-tau Mersenne characterization in this directory;
none states either theorem here.

## Route

1. Exclude `m = 0` and `m = 1`, then write `σ 1 m` as the product, over all
   prime factors `q` of `m`, of the geometric sums
   `∑ i < factorization q + 1, q^i`.
2. Each geometric factor is greater than one. If their product is prime,
   deleting any selected prime factor leaves an empty prime-factor set.
   Hence `m` has one prime factor and is a positive prime power.
3. Apply the general theorem to `m = p - 1`. Since `p = 2` would make the
   divisor sum one, `p` is odd and `2 ∣ p - 1`; the prime base of the power
   is therefore two. This gives `p = 2^k + 1` without truncated subtraction.
4. Pinned `Nat.pow_of_pow_add_prime` gives `k = 2^m`, proving item 2.
   The prime-power divisor-sum formula gives
   `σ 1 (p - 1) = 2^(k+1) - 1`, and pinned
   `Nat.prime_of_pow_sub_one_prime` makes `k + 1` prime, proving item 3.

## Falsifier

A prime `p` for which `σ 1 (p - 1)` is prime but `p - 1` is not a power of
two would refute item 2 and the prime-power classification used here. A
member whose divisor sum is not of the form `2^r - 1` with prime `r` would
refute item 3. A mismatch between OEIS `sigma` and Mathlib's `σ 1` convention
would invalidate the source correspondence.

## Evidence

The module
`D5/S3/Arith/Mersenne/KrizekSigmaPrimeFermatMersenne.lean` contains exactly
the two public theorems stated in this dossier and no private helper, numeric
example, `sorry`, new axiom, or `native_decide`. Both theorem axiom closures
are exactly `[propext, Classical.choice, Quot.sound]`.

The seven-line header checker and the serial Lean compilation exit zero.
Deleting the sole retained direct import `Mathlib.NumberTheory.Fermat` makes
the module fail to elaborate. Deleting either tested redundant import,
`Mathlib.NumberTheory.ArithmeticFunction.Misc` or `Mathlib.Tactic.NormNum`,
still compiles, so neither remains in the source.

The known OEIS terms give
`(p, σ 1 (p-1)) = (3,3), (5,7), (17,31), (65537,131071)`. These finite
values agree with `%S` but do not prove either unbounded theorem and are not
part of the Lean module.

## Triage

`theorem`; resolution `proved` for items 2 and 3 of the quoted A249759
conjecture, under the entry's defining prime hypotheses.

## ASSUMED-UNVERIFIED

Google Scholar and MathSciNet were not searched. Historical openness,
priority, and exhaustive novelty outside the current OEIS record, repository,
pinned Mathlib, and the recorded GitHub Lean-code search are unverified. The
source-to-Lean bridge identifies OEIS `sigma` with Mathlib's divisor-sum
function `σ 1`; the kernel theorem proves the displayed arithmetic statement.
