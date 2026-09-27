---
slug: oeis-a280258-krizek-phitorial-divisor-sum-parity
bibkey: krizek2017a280258
doi: null
url: https://oeis.org/A280258
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekPhitorialDivisorSumParity.result
---

# Krizek's phitorial divisor-sum parity characterization

## Problem

OEIS A280258, NAME (`%N`, verbatim):

> a(n) = Sum_{d|n} pxi(d), where pxi(m) is the product of totatives of m (A001783).

Jaroslav Krizek's COMMENT (`%C`, verbatim):

> Conjecture: a(n) is odd for numbers in A183300; a(n) is even for numbers in A001105 (2*n^2).

The dependent definitions are A001783's product of the integers from one
through `m` that are relatively prime to `m`, A183300's positive integers not
of the form `2*k^2`, and A001105's integers of the form `2*k^2`. The complete
quantified reading is

`forall n : Nat, 0 < n -> (Odd (a n) <-> not exists k : Nat, n = 2*k^2)`,

where `a(n)` sums the phitorials over the positive divisors of `n`.

## Motivation

The independent question is the parity characterization printed as Krizek's
named A280258 conjecture. Issue #8471 registered the verbatim source, full
quantifiers, Tier 1 classification, and literature readings before the proof
probe.

## Gap

The inspected A280258 entry labels the statement `Conjecture` and contains no
settlement marker or linked proof. The A001783, A183300, and A001105 entries
supply definitions and the even-divisor component, but do not settle the
phitorial divisor-sum statement.

Repository searches on the protected base found no `A280258`, `A001783`,
`A183300`, `phi-torial`, `phitorial`, or exact-conclusion owner. Pinned Mathlib
contains the divisor-cardinality factorization and finite-sum parity machinery,
but no phitorial definition or A280258 theorem.

The public theorem has `proof_shape: bind-only`, `escape_witness: none`, and
`admission_basis: open-problem-resolution`. It is the module's sole theorem and
settles exactly the preregistered external assertion. There is no direct frozen
repository dependency. The proof instantiates pinned Mathlib declarations,
including `Nat.card_divisors`, `Nat.coprime_prod_right_iff`,
`Nat.coprime_two_left`, `Finset.isSquare_prod`,
`Nat.prod_primeFactors_pow_factorization`, `Nat.factorization_pow`, and
`Finset.odd_sum_iff_odd_card_odd`, together with divisor/filter/product lemmas
and normalization.

`utility: none` applies because the definitions and result are unbounded
symbolic mathematics, not bounded enumeration, checker infrastructure,
numeric reduction, or a certified finite instance.

## Route

1. The phitorial is odd exactly at one and at even inputs. For odd inputs
   greater than one, the factor two occurs; for even inputs, every totative is
   odd.
2. Finite-sum parity reduces `Odd (a n)` to the parity of the number of divisors
   having odd phitorial. This set is one together with the even divisors.
3. If `n` is odd there are no even divisors. If `n=2*m`, halving gives a
   bijection between the even divisors of `n` and the divisors of `m`.
4. The prime-factorization formula makes the number of divisors of positive
   `m` odd exactly when `m` is a square. Hence `a(n)` is even exactly when
   `n=2*k^2`.

## Falsifier

Any positive natural `n` for which `a(n)` is odd while `n=2*k^2`, or `a(n)` is
even while no such `k` exists, would refute the result. A mismatch between the
inclusive totative product and A001783 would also refute the transcription; at
`m=1` the endpoint contributes one, and at `m>1` it is filtered out because it
is not coprime to `m`.

## Evidence

The Lean definitions `phitorial`, `a`, and `claim` transcribe the source, and
`result` proves the full positive-natural biconditional. The result is frozen
with statement id
`sha256:8e28f255cec6a96e6582d472c6010bfbc996028a0ae8db32d84cfa6b53b6064a`
and uses exactly `[propext, Classical.choice, Quot.sound]`.

## Triage

`theorem`; resolution `proved` for the A280258 parity conjecture. The Scribe
theorem node carries the matching `OpenProblemResolutionClaim` with
`ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

The inspected OEIS surfaces do not establish global historical novelty. A
complete prior proof outside the searched repository, pinned Mathlib, and OEIS
entry scope remains ASSUMED-UNVERIFIED. No priority claim is made.
