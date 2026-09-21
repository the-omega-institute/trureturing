---
bibkey: merca2011sums
authors: Mircea Merca
year: 2011
title: "Inequalities and Identities Involving Sums of Integer Functions"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
claim: "Conjecture 2 gives a lifted residue-sum identity at even multiplicative order for prime moduli."
strata_touched:
  - D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder
license: citation-only
triage: anchor
---

# Merca's sums of integer functions

Merca defines the remainder operation on printed page 2:

> When m is integer and n is a positive integer the quotient of m divided by n is ⌊m/n⌋ and the value m mod n = m − n⌊m/n⌋ is the remainder (or residue) of the division.

The multiplicative-order convention appears on printed page 17:

> For every positive integer m and every integer a relatively prime to m, we denote by ord_m(a) the multiplicative order of a modulo m, i.e., the smallest positive integer n such that a^n ≡ 1 (mod m), namely ord_m(a) = min {n ∈ N∗ | a^n ≡ 1 (mod m)}

The observation leading to Conjecture 2 appears on printed page 23:

> Using Maple to determine the value of some sums as Σ_{i=1}^{ord_m(a)} (2a^i + m mod 2m), necessary to determine the arithmetic mean (31) for round function, we notice another interesting identity.

The conjecture is stated on the same printed page:

> Conjecture 2. Let a and m be relatively prime positive integers. If m is prime and ord_m(a) is even then Σ_{i=1}^{ord_m(a)} (2a^i + m mod 2m) = m · ord_m(a).

Formula (39), also on printed page 23, encloses each residue summand as
`(a^i mod m)`. The Conjecture 2 display uses the same enclosing typography,
so its summand is read as `(2a^i + m) mod 2m`.

For an even order `r = 2s`, the half-order power satisfies
`a^s ≡ −1 (mod m)`. The residues at indices `i` and `i+s` are complementary
modulo `m`, and their two lifted terms sum to `2m`; summing the `s` pairs gives
`m · r`. Exact enumeration for every prime `m < 400` and every `2 ≤ a < m`
with even order covered 9111 cases with zero failures. The half-order relation
also held in all 9111 cases.

The Journal of Integer Sequences source and its source-linked search surfaces
were checked on September 20, 2026. No arXiv version was found. Title and
author searches in arXiv, MathDB searches for the conjecture and its
multiplicative-order residue-sum shape, and repository, issue, and pull-request
searches found no proof or refutation of Conjecture 2. Semantic Scholar returned
HTTP 429 and was not verified. This bounded search does not establish exhaustive
historical coverage or publication priority.

## Verified locator

- URL: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
- Printed page 2: remainder definition.
- Printed page 17: multiplicative-order definition.
- Printed page 23: formula (39), the Maple observation, and Conjecture 2.
