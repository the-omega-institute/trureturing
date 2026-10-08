---
slug: oeis-a400194-two-dense-divisor-block-maximum
bibkey: pol2026a400194
doi: null
url: https://oeis.org/A400194
triage: theorem
motivation_gids:
  - D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome
---

# Maximum length of a two-dense divisor block

## Problem

> Conjecture: a(n) = A001511(n) * A400195(n).

— Omar E. Pol, OEIS A400194 revision 18.

For every positive natural n, split its complete strictly increasing list of
positive divisors into maximal contiguous blocks, cutting precisely at
b>2a. Let M(n) be the maximum block length and O(n) the maximum odd count
over the SAME actual block family. The exact assertion is
M(n)=(v₂(n)+1)O(n). Equality b=2a and singleton blocks are retained.

## Motivation

This first-tier recent externally named conjecture has an elementary
universal ordinary proof and a separately missing formal membership bridge.
The existing A384222 palindrome uses the same row but does not supply the
maximum identity. Exact preregistration is issue
https://github.com/the-omega-institute/trureturing/issues/14375.

## Gap

The bounded source qualification found no exact resolution in the inspected
repository and pinned Mathlib declarations, selected third-party Lean
sources, relevant OEIS entries and Höft manuscripts. Dyadic aggregate sums
and boundary counts do not alone identify the cardinality of every actual
block. Global literature absence and discovery priority remain unverified.

## Route

Write n=2ᵛm with m odd. Every positive divisor is uniquely 2ʲu with u odd,
u|m and 0≤j≤v. Conversely all such products divide n, by combining
2ʲ|2ᵛ with u|m in the product decomposition of n.

For the actual ordered partition, consecutive blocks A,C have
2 last(A)<head(C). If x belongs to A and y lies later, sortedness gives
x≤last(A) and head(C)≤y. Thus y≤2x is incompatible with that separating
boundary. Induction on the block list gives symmetric membership for
endpoints x,y satisfying x≤2y and y≤2x. Every intervening divisor is
included by the actual partition; no substitute chain partition is used.

Apply this connectivity at each adjacent dyadic pair 2ʲu,2ʲ⁺¹u.
The complete chain u,2u,…,2ᵛu remains in one actual block. If d is in a
block B, its odd component u is therefore also in B, as is every chain
entry with exponent at most v.

Consequently (j,u)↦2ʲu bijects {0,…,v} times the odd members of B onto B.
Odd-component recovery determines u, and cancellation and injectivity of
powers of two determine j. The complete divisor list has no repetitions,
so set cardinalities equal list lengths. This yields locally
|B|=(v+1)|Odd(B)|. Taking the two maxima over the same block family gives
the exact target, without assuming a common maximizing block in advance.

## Falsifier

Any positive n whose two same-family statistics violate the formula
refutes the conjecture. A finite range cannot prove the universal claim.

## Evidence

The source and ordinary argument have independent qualification.
`D5/S3/Factorization/TwoDenseDivisorBlockMaximum.lean` defines
`oddBlockCounts` and proves the exact all-positive theorem `result`.
The canonical scoped Lean build succeeds. The printed axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.

The formalization is an unbounded symbolic proof, rather than bounded
enumeration, a checker, numerical reduction or a certified finite instance;
its utility classification is `none`. Its proposed admission basis is
`open-problem-resolution`. The result has substantive local boundary and
dyadic induction on its live proof path; it is classified `content`.
Formal admission, freezing and required delivery checks remain separate.

## Triage

The exact maximum identity is proved in Lean for every positive natural n.
The matching Scribe binds this single resolution to the source conjecture.
Independent semantic review and canonical admission remain necessary.

### What the settlement shows

The compiled proof identifies the factor v₂(n)+1 as the common length of
all complete dyadic chains in an actual block. At n=1 the block is [1]
and both maxima are 1. For odd n every chain has length one; for powers
of two the full divisor list is one chain. These cases are within the
universal theorem, rather than separately retained finite certificates.

The live per-block cardinality identity explains the maximum formula.
A separately named settlement of A384222's stronger rowwise conjecture,
other prime thresholds, different cutoffs, and incomplete divisor lists
remain outside this target and need their own qualification and admission.
The proof does not establish global literature priority or discharge
other conjectures merely because they use the same blocks.

## ASSUMED-UNVERIFIED

Source-to-Lean fidelity is a semantic review obligation. The bounded
literature qualification is not an exhaustive assertion of absence.
Ordinary argument, finite corroboration, kernel verification and formal
admission have separate evidential roles.
