---
bibkey: golomb1970powerful
authors: Solomon W. Golomb
year: 1970
title: Powerful numbers
doi: 10.1080/00029890.1970.11992654
url: https://doi.org/10.1080/00029890.1970.11992654
claim: Every powerful number is the product of a perfect square and a perfect cube, and the paper studies the distribution of such numbers.
strata_touched:
  - D5/S3/Arith/Powerful/PowerfulNumber
license: citation-only
triage: anchor
---

# Powerful numbers

## Verified locator

American Mathematical Monthly 77 (1970), 848-852,
DOI 10.1080/00029890.1970.11992654.

Golomb defines a positive integer to be powerful when every prime dividing it
has its square dividing it, and records that such an integer can be written as
a square times a cube. The term "powerful number" originates in this paper.
Powerful numbers appear in several Erdős problems, among them the question of
whether three consecutive powerful numbers exist.

## Proof scope

The Lean module states the representation in the form: for n at least one and
powerful, there exist a and b with n equal to a squared times b cubed and b
squarefree. The squarefree part b is uniquely determined, although uniqueness
is not stated.

The proof is a repository derivation from Mathlib's square-times-squarefree
decomposition. Writing n as d squared times c with c squarefree, the powerful
condition forces every prime of c to occur in n to order at least two while
occurring in c to order exactly one, hence to divide d; comparing factorization
exponents gives c dividing d, and substituting d equal to e times c yields the
displayed representation with a equal to e and b equal to c. No distribution or
counting result of the source is formalized.
