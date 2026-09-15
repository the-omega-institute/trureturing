---
slug: oeis-a008365-detlefs-rough-residue-characterization-refutation
bibkey: sloane2011a008365
doi: null
url: https://oeis.org/A008365
triage: theorem
motivation_gids:
  - D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation
---

# Refutation of Detlefs's A008365 four-residue characterization

## Problem

OEIS A008365, NAME (verbatim):

> 13-rough numbers: positive integers that have no prime factors less than 13.

Gary Detlefs's COMMENT of December 30, 2011 (verbatim):

> Conjecture: Numbers n such that n^24 is congruent to {1,421,631,841} mod 2310. - _Gary Detlefs_, Dec 30 2011

For natural numbers, define
`isRough13(n) := for every natural p, Prime(p) implies p divides n implies
13 <= p`, and define
`inResidueSet(n) := n^24 mod 2310 is one of {1,421,631,841}`. The literal
refuted statement is `claim := for every natural n, 0<n implies
(isRough13(n) iff inResidueSet(n))`.

The five-residue correction {1,421,631,841,1681} is disclosed but not
claimed. Its structural reason is that 2310 = 2*3*5*7*11: for a value
coprime to 2310, the twenty-fourth power is congruent to 1 modulo 2*3*5*7,
while modulo 11 it equals the fourth power and takes the five quartic
residues {1,3,4,5,9}; 1681 is congruent to 9 modulo 11. The converse
inclusion from the original four-residue set to 13-rough values is also not
claimed.

## Motivation

The COMMENT identifies the 13-rough numbers with four residue classes of
twenty-fourth powers modulo 2310. A single positive 13-rough value outside
those classes refutes the universal biconditional. The prime 17 is the least
such value found by the bounded scan and has residue 1681.

## Gap

Searches recorded on September 15, 2026 checked all 73 OEIS revisions then
available. Revisions 50 through 52 discuss Bala's distinct-product
characterization, while the four-residue line remains labelled "Conjecture"
in revision 73.

The checked arXiv HTML surface returned zero results before the API returned
HTTP 429. OpenAlex returned two unrelated rough-number works; the full text
of Irwin's 2026 preprint could not be checked because its PDF returned HTTP
403 and is `ASSUMED-UNVERIFIED`. MathOverflow returned zero results. A GitHub
exact-sentence search returned one result, an OEIS mirror. The pinned Mathlib
has no matching theorem.

These bounded searches do not establish exhaustive literature coverage,
historical openness, or publication priority. No novelty or priority claim
is made.

## Route

Take `n=17`. Kernel computation proves `Nat.Prime 17`. The theorem
`Nat.Prime.eq_one_or_self_of_dvd` then shows that every prime divisor of 17
is 17, establishing `isRough13(17)`. A second kernel computation gives
`17^24 mod 2310 = 1681`, which is distinct from 1, 421, 631, and 841. Thus
`inResidueSet(17)` is false, contradicting the universal biconditional.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead supplies the primality and residue certificate at 17,
producing `Not claim`.

## Evidence

- Lean module:
  `D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 5.57 seconds wall time and 1.53 milliseconds
  of cumulative type checking, with maximum resident set size
  1,305,755,648 bytes.
- The finite certificate proves `Nat.Prime 17`, derives `isRough13(17)` via
  `Nat.Prime.eq_one_or_self_of_dvd`, and computes
  `17^24 mod 2310 = 1681`; no private declaration is present.

A bounded scan through 200000 reported 8311 mismatches. The least was 17,
followed by 61, 71, 83, 127, 137, 149, 181, 193, and 247. Every mismatch was
13-rough but outside the four-residue set; the count in the opposite
four-set-but-not-rough direction was zero. The 13-rough values in the same
range realized exactly {1,421,631,841,1681}.

These bounded computations support the certified instance but do not prove
the corrected five-residue characterization, its converse, or a global
least-counterexample theorem.

## Triage

`theorem`. The finite certificate at 17 refutes the literal universal
characterization. No claim is made about the corrected five-residue
characterization, its converse, or any other A008365 comment.

## ASSUMED-UNVERIFIED

The full text of Irwin's 2026 preprint, the bounded scans beyond the single
kernel-certified instance, and literature completeness beyond the checked
OEIS, arXiv, OpenAlex, MathOverflow, GitHub, and pinned Mathlib surfaces are
`ASSUMED-UNVERIFIED`.
