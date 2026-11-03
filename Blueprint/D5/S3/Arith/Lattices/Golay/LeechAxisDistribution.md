# The actual Leech axis distribution

## Abstract

The actual Leech axis distribution

This is the classical minimal-vector inner-product distribution for a literal coordinate axis of the integer Golay Leech construction. No novelty is claimed. The theorem concerns this actual lattice and every pair of distinct coordinates; it assumes neither a design nor transitivity. It supplies a later construction dependency and makes no Ising, Monster, vertex-operator-algebra, string-theory or physical realization claim.

**Theorem 1.1 (Distribution on the entire norm-32 sphere).**

Lean statement: `D5/S3/Arith/Lattices/Golay/LeechAxisDistribution.axis_distribution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/LeechAxisDistribution.axis_distribution` (`✓ std3`). ∎

*Citation.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Commentary.*

For every i,j in Fin 24 with i unequal to j, put axis = Pi.single i 4 + Pi.single j 4 as an integer vector. For every integer t, the literal subtype of all integer vectors x satisfying Admissible code x, squareSum x = 32, and dotProduct axis x = 8*t is finite. Its Nat.card is 1 when t is 4 or -4, 4600 when t is 2 or -2, 47104 when t is 1 or -1, 93150 when t is zero, and zero for every other integer. There is no coordinate bound on x.

The dot equation is exactly x_i + x_j = 2*t. The established sphereEquiv classifies the entire unbounded sphere into the two-coordinate signed-four family, signed octads of even sign parity, and odd vectors with one exceptional coordinate. The proof transports the literal subtype through this equivalence and sums the three actual coordinate fibers.

For the signed-four family, one support contains both observed coordinates, 44 contain exactly one, and 231 contain neither. Its contributions are 1 at each of t = 4,-4, 88 at each of t = 2,-2, and 926 at zero. For octads, the established coordinate_incidence theorem supplies 77 supports containing both, 352 containing exactly one, and 330 containing neither. Deleting a pivot outside the observed support coordinates via evenSignsEquiv gives 32 signs for a prescribed pair and 64 for a prescribed single sign. Thus octads contribute 2464 at each of t = 2,-2, 22528 at each of t = 1,-1, and 47168 at zero.

For the odd family, the original structural Golay projection proof and translation of additive fibers give 1024 codewords for every prescribed bit pair. The 22 exceptional coordinates outside the observed pair contribute 22528 at each of t = 1,-1 and 45056 at zero. The two exceptional coordinates on the pair add 2048 at each of t = 1,-1 and 2048 at each of t = 2,-2. Summation gives the stated distribution, including emptiness at every other integer.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/LeechAxisDistribution.axis_distribution`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayOctadIncidence](GolayOctadIncidence.md)
- Dependency: [D5/S3/Arith/Lattices/Golay/LeechMinimalCount](LeechMinimalCount.md)
