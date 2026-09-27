---
slug: ayad-bouchenna-base-b-reverse-multiple-divisors
bibkey: ayad2025reversemultiples
doi: 10.5281/zenodo.15283699
url: https://math.colgate.edu/~integers/z37/z37.pdf
triage: theorem
motivation_gids:
  - D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.result
---

## Problem

Mohamed Ayad and Rachid Bouchenna, *Which Integer Divides the Reverse of Any
of Its Multiples?*, INTEGERS 25 (2025), #A37, printed p. 9, Problem 1:

> Let B ≥ 2 be any number base. Are the divisors of B² − 1 the only positive
> integers satisfying the property P*_B ?

Section 4.1 on printed p. 8 defines the base-B reverse m*_B by reversing
the positional digits of the positive integer m. The property P*_B means
that n divides m*_B for every positive multiple m of n. The exact statement
is: for all natural B ≥ 2 and all natural n > 0,
`(∀ m : ℕ, 0 < m → n ∣ m → n ∣ Nat.ofDigits B (Nat.digits B m).reverse)
↔ n ∣ B ^ 2 - 1`.

## Motivation

The paper's Theorem 3 characterizes the base-ten case by the divisors of 99.
Proposition 5 on printed p. 8 proves sufficiency for every base. The question
asks whether necessity also holds uniformly in the base. The motivation
GID supplies this full characterization, including both directions.

## Gap

The arbitrary-base necessity is the question absent from Proposition 5.
Preregistration #8990 records the fully quantified statement, tier-one
classification and literature readings before the probe. The orchestrator's
September 20, 2026 readings are: arXiv exact phrase and author queries each
returned zero entries; Crossref had no matching index entry; MathDB had no
entry for this question, with a Collatz positive control returning 20;
OpenAlex indexed the article with cited_by_count zero. OEIS A018282 covers
only the already established base-ten case. These searches bound the
literature claim to their queried scope.

## Route

A positive multiple whose leading base-B digit is one forces gcd(n,B)=1
whenever n has the reversal property. For a unit B modulo n, let T be its
multiplicative order. If B² is not one modulo n, then T ≥ 2. Sparse digit
lists with ones at positions 0, 1, T, ..., (c+1)T have forward residue
1+B+(c+1) and B times their reversed residue equal to 1+B+(c+1)B.
Choosing c congruent to −(2+B) makes the forward residue zero. The reversal
property then forces B²=1, a contradiction. This is the private `witness`
lemma used in `result`. Conversely, B²=1 gives the digit-reversal identity
by induction and preserves divisibility for every multiple.

## Falsifier

A base B ≥ 2 and positive n with the reversal property but n not dividing
B²−1 would refute necessity. A positive divisor n of B²−1 and a positive
multiple m with n not dividing m*_B would refute sufficiency. The theorem
ranges over all such B, n and m; bounded enumerations alone are insufficient.

## Evidence

The Lean source is `D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.lean`.
Its public definitions are `reverseBase` and `HasReverseMultipleProperty`;
its single public theorem is `result`. The Scribe theorem node links this
question to that result with `ResolutionKind.Proved`. Reversal uses the
canonical Mathlib digits and handles trailing zeros by positional evaluation.

The orchestrator independently computed the property from its definition
for bases 2 through 16, n ≤ 400 and every multiple t ≤ 4000, obtaining the
divisors of B²−1 with zero extras and zero misses. At B=10 the set is
{1,3,9,11,33,99}, matching Theorem 3. These are attributed bounded readings,
not the justification for the universal quantifiers.

## Triage

`theorem`: the arbitrary-base characterization is an unbounded symbolic
result. No restriction to a finite range of bases, moduli or multiples is
part of the conclusion. Problem 2 and the weaker property in section 4.2
are outside this statement.

## ASSUMED-UNVERIFIED

The literature and numerical readings above are supplied orchestrator
readings; this Stage B seat did not repeat those external computations or
literature queries. The source clauses and preregistered statement were
checked against issue #8990 and the supplied Library note. Exhaustive
publication priority outside the searched scope is unverified. Semantic
fidelity and proof-shape classification remain review judgments rather
than consequences of the resolution marker validator.
