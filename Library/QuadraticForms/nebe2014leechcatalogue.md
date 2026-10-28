---
bibkey: nebe2014leechcatalogue
authors: Gabriele Nebe and Neil J. A. Sloane
year: 2014
title: The Lattice LAMBDA24 (The Leech Lattice)
doi: null
url: https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html
claim: "The catalogue gives dimension 24, minimum squared norm 4 and kissing number 196560."
strata_touched:
  - D5/S3/Arith/Lattices/Golay/GolayOctadCount
  - D5/S3/Arith/Lattices/Golay/LeechMinimalCount
license: citation-only
triage: anchor
---

# Classical Golay and Leech sphere counts

The Nebe-Sloane Catalogue of Lattices entry for LAMBDA24 gives
MINIMAL_NORM 4 and KISSING_NUMBER 196560. Its recorded version is
18 July 2014. These values are classical, not an originality claim.

The Error Correction Zoo entry "[24,12,8] Extended Golay code",
https://errorcorrectionzoo.org/c/extended_golay , identifies weight-eight
supports with the Steiner system S(5,8,24), citing Conway and Sloane,
Sphere Packings, Lattices and Groups, pages 89 and 276. Counting incident
five-subsets gives binomial(24,5)/binomial(8,5)=759. No Steiner-system
property is imported as an assumption into the Lean proof.

The parameterized theorem here instead assumes the stated cardinality,
all-ones, self-duality, minimum-weight and five-weight-spectrum conditions
for an arbitrary binary linear code on twenty-four coordinates. Pair
projection fibers give second moment 565248; complementation and the
size equation force 759. This exact parameterized derivation belongs to
the repository; fiber counting and moment methods are classical.

For the original integer Golay congruences, the complete coordinate
classification and bijection give family sizes 1104, 97152 and 98304,
whose sum is 196560. The function scaledSquare is squareSum/8, so integer
square sum 32 is equivalent to rational scaledSquare 4. The catalogue
attribution supplies no real-lattice identification, real self-duality,
Gram basis, VOA states or Monster representations. Those bridges require
separate proofs. The coordinate convention is described in
[Leech's Notes on Sphere Packings](leech1967packing.md).

## Verified locator

https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html

The catalogue entry records MINIMAL_NORM 4 and KISSING_NUMBER 196560.
The extended Golay code entry at https://errorcorrectionzoo.org/c/extended_golay
identifies the weight-eight Steiner blocks used for the classical octad attribution.
