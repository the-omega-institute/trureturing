---
bibkey: webb2016pgroups
authors: Peter Webb
year: 2016
title: A Course in Finite Group Representation Theory
doi: 10.1017/CBO9781316677216
url: https://www-users.cse.umn.edu/~webb/RepBook/RepBookLatex.pdf
claim: Chapter 6 gives p-group augmentation nilpotence and the quotient-kernel method.
strata_touched:
  - D5/S3/FiniteGroups/GroupAlgebra/PGroupAugmentation
  - D5/S3/FiniteGroups/GroupAlgebra/PGroupNormalTrace
license: citation-only
triage: anchor
---

# Modular p-group augmentation ideals

Peter Webb, *A Course in Finite Group Representation Theory*, Cambridge University
Press, 2016, DOI [10.1017/CBO9781316677216](https://doi.org/10.1017/CBO9781316677216).
Locators refer to the linked prepublication PDF.

Proposition 6.3.3(3), printed page 92 (PDF page 99), identifies the augmentation
ideal of a finite p-group over a characteristic-p field with the Jacobson
radical, hence proves its nilpotence. The proof uses the unique simple module.

Chapter 6, Exercise 15, printed page 99 (PDF page 106), identifies the kernel of
the quotient group-algebra map for a normal subgroup N with the ideal generated
by the augmentation ideal of N, for a general commutative coefficient ring R.
It also gives the corresponding identity for powers. Exercises 16–17, printed
page 100 (PDF page 107), develop direct field-coefficient nilpotence arguments.

`PGroupAugmentation` implements the central order-p quotient method and proves
the explicit whole-ideal bound I raised to the cardinality of G equals zero for
every commutative characteristic-p coefficient ring. This precise statement is
not asserted to appear verbatim in Proposition 6.3.3. It is a classical method
and no historical novelty is claimed. `PGroupNormalTrace` derives the Galois
trace criterion using the normal basis theorem and this structural bound.
