# Actual Leech Charges and Low Sugawara Spectrum

## Abstract

The actual Golay Leech geometry determines the canonical Sugawara low spectrum.

The integer lattice is precisely IntegerLeech.Admissible for GolayEncoder.code, and its real image is RealLeech.lattice under coordinate inclusion. The real pairing is the coordinate dot product divided by eight. RealLeech.exists_positive_even_unimodular_gram supplies even integral LatticeData D, rank 24, a unit Gram determinant, a positive definite real Gram matrix, and an integral linear equivalence e from Charge D onto this actual real lattice preserving the full bilinear form.

Coordinate inclusion is injective. Mathlib's Submodule.equivMapOfInjective therefore recovers the unique actual admissible integer vector for every e(a). Its squareSum divided by eight equals bilinear(D,a,a). A norm-two charge would have squareSum sixteen and be nonzero, contradicting IntegerLeech.construction_lower_bound with the proved doubly-even and minimum-weight properties of the actual Golay code.

LeechMinimalCount.shortest_vectors_finite and shortest_vectors_card classify and count the entire unbounded norm-thirty-two integer sphere. RootlessLowGrades supplies the oscillator and charged energy decomposition on the actual lattice Fock carrier, and identifies its grades with the literal inverse-Gram Sugawara eigenspaces. Thus the norm-four shell contributes 196560 states at energy two, while the neutral contribution is 24 + choose(25,2) = 324. The total is 196884.

The classical lattice construction and shortest-vector classification retain their Golay and Leech attribution, as recorded in the existing Leech lattice notes. The lattice Fock and conformal-vector context is Bakalov--Kac, section 4.1. This is the untwisted lattice spectrum. It does not construct the reflection orbifold, the Monster action, a full all-state VOA, or string and holographic theories.

**Definition 1.1 (Actual charge-to-integer sphere equivalence).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.normFourEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.normFourEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Acknowledgement.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For any integral charge equivalence e into RealLeech.lattice preserving the full real pairing, the literal NormFour D subtype is equivalent to all integer vectors x : Fin 24 to Int satisfying Admissible code x and squareSum x = 32. The forward map uses e followed by the inverse coordinate-image equivalence. The inverse uses coordinate inclusion followed by e inverse; the two inverse laws follow from those actual linear equivalences.

**Theorem 1.2 (Actual geometric Leech Sugawara low spectrum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.actual_leech_low_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.actual_leech_low_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe and Neil J. A. Sloane (2014). *The Lattice LAMBDA24 (The Leech Lattice)*. URL: <https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html>.

*Acknowledgement.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

With no premises, there exist D and an integral linear equivalence e : Charge D to RealLeech.lattice. They have rank 24, unit Gram determinant, positive definite real Gram form, full pairing compatibility, and no norm-two charges. There exists an equivalence s from NormFour D onto the full admissible squareSum-32 integer subtype such that castLinear(s(a)) = e(a) for every norm-four charge. This charge shell is finite and has cardinality 196560. For every signed integer n the eigenspace at n of the literal sugawaraMode D (gramComplex D) inverse 0 is finite dimensional over Complex; its finranks at zero, one, and two are respectively 1, 24, and 196884. The evenness is part of the supplied LatticeData, rather than an additional premise.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.actual_leech_low_spectrum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum.normFourEquiv`
- Dependency: [D5/S3/Arith/Lattices/Golay/LeechMinimalCount](../../Arith/Lattices/Golay/LeechMinimalCount.md)
- Dependency: [D5/S3/Arith/Lattices/Golay/RealLeech](../../Arith/Lattices/Golay/RealLeech.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/RootlessLowGrades](RootlessLowGrades.md)
