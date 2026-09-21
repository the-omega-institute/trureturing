---
bibkey: merca2011sums
authors: Mircea Merca
year: 2011
title: "Inequalities and Identities Involving Sums of Integer Functions"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
claim: Conjecture 1 asserts an exact residue sum when two coprimality conditions hold and the multiplicative order is even.
strata_touched:
  - D5/S0/Certificates/MercaResidueSumEvenOrderRefutation
license: citation-only
triage: anchor
---

# Merca's sums of integer functions

Section 1, printed page 2, defines the remainder operation:

> When m is integer and n is a positive integer the quotient of m divided by n is
> ⌊m/n⌋ and the value m mod n = m − n⌊m/n⌋ is the remainder (or residue) of
> the division.

Section 3.2, printed page 17, defines the multiplicative order:

> For every positive integer m and every integer a relatively prime to m, we denote
> by ord_m(a) the multiplicative order of a modulo m, i.e., the smallest positive
> integer n such that a^n ≡ 1 (mod m), namely
> ord_m(a) = min {n ∈ N∗ | a^n ≡ 1 (mod m)}

Section 4, printed page 23, states the conjecture:

> **Conjecture 1.** Let a and m be relatively prime positive integers. If a−1 and m
> are relatively prime and ord_m(a) is even then
> Σ_{i=1}^{ord_m(a)} (a^i mod m) = m · ord_m(a) / 2.

The formalisation encodes `ord_m(a)` as Mathlib's
`orderOf (a : ZMod m)`.

The printed statement fails at `(a,m) = (2,15)`. Both coprimality conditions hold,
`ord_15(2) = 4`, and the residues `2, 4, 8, 1` sum to `15`, whereas the printed
right side is `30`.

For `m < 80` and representatives `0 < a < m`, exact enumeration of pairs
satisfying both coprimality conditions and having even order gives 761 qualifying
pairs and 94 failures. The first five failures `(a,m,ord,sum,m*ord/2)` are `(2,15,4,15,30)`,
`(8,15,4,15,30)`, `(2,21,6,42,63)`, `(11,21,6,42,63)`, and
`(2,35,12,175,210)`. The failing moduli in this range are
`15, 21, 35, 39, 45, 51, 55, 57, 63, 65, 75, 77`; all are composite. This finite
observation is not a theorem about prime moduli and does not settle Conjecture 2.

The Journal of Integer Sequences article is the published source. No DOI or arXiv
version is listed for it. The preregistered literature search found no proof,
refutation, erratum, or MathDB entry for Conjecture 1 before the counterexample was
checked.

## Verified locator

- URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
- Scope: the remainder definition on printed page 2, the multiplicative-order
  definition on printed page 17, and Conjecture 1 on printed page 23.
