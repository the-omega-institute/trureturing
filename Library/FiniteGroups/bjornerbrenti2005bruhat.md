---
bibkey: bjornerbrenti2005bruhat
authors: Anders Björner and Francesco Brenti
year: 2005
title: The Bruhat Order
doi: 10.1007/3-540-27596-7_2
url: https://doi.org/10.1007/3-540-27596-7_2
claim: "A Bruhat comparison holds exactly when a reduced word for the upper element contains a reduced expression for the lower element as a subword."
strata_touched:
  - D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation
license: publisher copyright
triage: anchor
---

# The Bruhat subword criterion

Björner and Brenti, *Combinatorics of Coxeter Groups*, Chapter 2, Theorem
2.2.2 (Subword Property) and Corollary 2.2.3 identify the Bruhat comparison
with containing a reduced expression for the lower element in a reduced
expression for the upper element. For this test, some reduced expression
of the upper element is equivalent to any fixed reduced expression of it.
The deletion condition from Chapter 1 shortens a nonreduced word by
deleting two letters with its product preserved. Iteration terminates in
a reduced subword. Thus taking the product of all selected-position
subwords yields the same lower set. The process can identify different
position choices, so it does not preserve Elek's magic-word count.
[Chapter 2](https://doi.org/10.1007/3-540-27596-7_2) · [Chapter 1](https://doi.org/10.1007/3-540-27596-7_1)

The source locators were corroborated through accessible citations and
Chapter 2 metadata. The Lean module uses the positional criterion as its
definition and calculates it directly in the witness.

## Verified locator

Chapter 2, Theorem 2.2.2 and Corollary 2.2.3 cover the subword property.
The DOI and chapter URL are https://doi.org/10.1007/3-540-27596-7_2 .
