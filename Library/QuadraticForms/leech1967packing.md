---
bibkey: leech1967packing
authors: John Leech
year: 1967
title: Notes on Sphere Packings
doi: 10.4153/CJM-1967-017-0
url: https://doi.org/10.4153/CJM-1967-017-0
claim: "Section 2.31, printed pages 262-263, describes the common-parity Golay integral-coordinate construction and squared integer minimum 32."
strata_touched:
  - D5/S3/Arith/Lattices/Golay/GolayEncoder
  - D5/S3/Arith/Lattices/Golay/IntegerLeech
license: citation-only
triage: anchor
---

# Golay digits and Leech's integral coordinates

## Verified locator

John Leech, Notes on Sphere Packings, Canadian Journal of Mathematics 19
(1967), section 2.31, printed pages 262-263 (PDF pages 12-13).
DOI: 10.4153/CJM-1967-017-0.
URL: https://doi.org/10.4153/CJM-1967-017-0

This locator covers the common-parity coordinates, Golay twos digits,
fours-digit parity rule and integer minimum squared length 32.

## Formalized scope

Leech, Canadian Journal of Mathematics 19 (1967), 251-267, section 2.31,
printed pages 262-263, uses common-parity integer coordinates with twos
digits in the extended Golay code, and a further fours-digit parity rule.
With a common parity bit m, these are the congruences used here:
(x_i-m)/2 modulo 2 belongs to C and sum x_i is 4m modulo 8.
Scaling by 1/sqrt(8) sends squared integer minimum 32 to squared minimum 4.
The formal result derives closure, norm divisibility and the lower bound
from these congruences and supplies twice an encoded octad as a witness.
It does not establish rank, unimodularity, uniqueness or Monster realization.

For the precise cyclic-code convention, Noam Elkies, Math 256x (Fall 2013),
Cyclic codes, final page (page 2), gives
P=X^11+X^10+X^6+X^5+X^4+X^2+1:
https://people.math.harvard.edu/~elkies/M256.13/cyclic.pdf .
The implemented g=X^11+X^9+X^7+X^6+X^5+X+1 is its reciprocal.
The source contains an exact matrix/encoder identity reversing the first
23 coordinates and the 12 message coordinates, while fixing parity.
No cyclic convention is imported as an unproved code equivalence.

A bounded external Lean search also inspected TauCetiProject/TauCeti at
commit a1824f7b24dce4964de6626fdb619b80b241afac, especially
InformationTheory/Coding/Binary/Golay/Basic.lean and
LinearAlgebra/IntegralLattice/ConstructionB/Minimum.lean. That project
uses a systematic bordered-circulant generator, rather than the explicit
cyclic generator required here. Its proof strategy and kernel certificate
splitting were checked; it is not an installed dependency and its code
identification is not assumed. There is no mathematical novelty claim.
