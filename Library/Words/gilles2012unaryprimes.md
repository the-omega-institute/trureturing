---
bibkey: gilles2012unaryprimes
authors: Gilles
year: 2012
title: "Prove that the language of non-prime numbers written in unary is not regular"
doi: null
url: https://cs.stackexchange.com/a/4986
claim: "The prime lengths are not ultimately a finite union of arithmetic progressions with a common positive difference; adjoining the single length one leaves this obstruction intact."
strata_touched:
  - D5/S3/Arith/PrimesNotSemilinear
license: citation-only
triage: anchor
---

# Prime Lengths and Eventual Periodicity

Gilles describes unary regular languages as finite unions of arithmetic
progressions with a common difference beyond a finite initial segment, and
states that prime lengths do not have this form. This is the classical
nonperiodicity obstruction underlying the formal theorem.

The formal proof handles the additional element one directly: for a sufficiently
large prime p and a proposed positive period d, the number p*(1+d) is both
composite and greater than one. The source discusses prime lengths; its finite
extension by one is justified by this same argument in the formal module.

## Verified locator

url: https://cs.stackexchange.com/a/4986

The Stack Exchange API at
https://api.stackexchange.com/2.3/answers/4986?site=cs&filter=withbody
returns the answer by Gilles and its text on unary languages, arithmetic
progressions and prime lengths. The answer belongs to question 4984, with the
title above. The source has no DOI (`doi: null`).
