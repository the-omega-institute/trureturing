---
slug: oeis-a380056-fourth-index-divisible-by-five
bibkey: oeis2025a380056
doi: null
url: https://oeis.org/A380056
triage: theorem
motivation_gids:
  - D5/S3/Factorization/A380056
---

# The A380056 divisibility conjecture at multiples of four

## Problem

A sequence is read off an exponential generating function whose numerator is
the exponential minus one and whose denominator is the cosine of twice the
argument. Paul D. Hanna conjectured on January 28, 2025 that five divides
every term whose index is a multiple of four.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September 9,
2026 found it still labelled Conjecture. Two published facts bear on it and
neither settles it, which is what makes the remaining step worth isolating.

## Gap

The entry prints a finite formula for even-indexed terms as a sum over
binomial coefficients against Euler secant numbers and powers of four. The
Euler numbers are known to be periodic modulo an odd prime, by Knuth and
Buckholtz in 1967; at five the period is two. Reducing the printed sum modulo
five with that periodicity kills half the terms, but the remainder is a
weighted binomial sum whose vanishing is not implied by either fact. The
searched indexes returned no proof of that remaining step.

## Route

State the two published facts as hypotheses on an abstract pair of sequences,
and derive the conclusion. This keeps the literature's contribution and the
new content separate: what is proved is the implication, not a property of any
particular construction.

Under the residue hypothesis only the terms with odd Euler index survive, plus
the endpoint where the Euler value is one. Those indices are exactly the ones
congruent to two modulo four. The indicator of that congruence is a
combination of four powers, available because two and three have order four
modulo five; this is a roots-of-unity filter. Each resulting power sum
collapses by the binomial theorem into a closed form, and the four closed
forms cancel modulo five.

## Falsifier

A pair of sequences satisfying the two hypotheses but with some term at an
index divisible by four not divisible by five would contradict the theorem.

## Evidence

- Module: `D5/S3/Factorization/A380056.lean`.
- Main theorem: `a380056_div_five`, conditional on the printed formula and the
  Euler residues, both stated as hypotheses.
- Supporting results: `binomial_residue_two`, `surviving_sum`.
- All three public results are on the standard three axioms with no `sorryAx`.
- There is no finite cutoff in any public statement, and the finite checks are
  confined to fixed facts about fifth-power residues.

The caller verified before dispatching an implementation seat. Expanding the
generating function directly, the conjecture held for every index below forty
with no violation. The Euler residues modulo five matched the alternating
pattern for the first twelve indices. The printed finite formula matched the
expansion exactly for the first nine even indices. The sum of the surviving
terms vanished modulo five for the first six multiples of four, while the
individual products were irregular — for one index all four, for another
mostly zero — which is why the collective cancellation is not a term-by-term
identity.

## Triage

`theorem`. The implication is proved for every index. Nothing is asserted
about the first conjecture on the same entry, nor about whether any given
sequence satisfies the hypotheses.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The searches do not exclude
private or unindexed proofs. The identification of the hypotheses with the
printed formula and the classical periodicity is documentary; the kernel
verifies the implication as stated.
