# A one-oscillator tensor in every nonzero invariant submodule

## Abstract

One-oscillator extraction in the actual negative-parity half-Fock space.

**Theorem 1.1 (Native fixed modes extract a nonzero one-oscillator tensor).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction.nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction.nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let D be a lattice datum with unit Gram determinant hu. Let S be a nonzero complex submodule of paritySpace D hu (-1) stable under every integer mode of fixedParitySlice D hu (-1) for every source in FixedCarrier D. Then S contains a nonzero vector x whose underlying actual tensor is X(a) tensor g for an oscillator index a and a nonzero vector g in ActualGround D hu.

A current after an odd current-source coefficient belongs to the fixed-mode span at the same input. The corrected-field current coefficient formula gives stability under every pair of actual tensor currents. The inverse Gram row and reciprocal frequency recover a partial derivative from nonnegative currents. Negative currents act by multiplication by oscillator variables. Thus pairs of partials and each operator X(a) times the partial at a preserve the image of S.

Choose a nonzero vector of S and a monomial of maximal total degree across all its ground-coordinate polynomials. Negative parity forces all supported degrees to be odd. Keep one occurrence of a variable X(a) in the chosen monomial and differentiate in all its other occurrences. The derivative word has even length, and the coefficient of X(a) left by the chosen monomial is nonzero. Every surviving coefficient comes from a source monomial with the derivative multiplicities added to its exponent, so maximality and odd parity force every remaining monomial to have degree one. Applying X(a) times the partial at a isolates X(a) tensor g. The selected nonzero coefficient gives a nonzero coordinate of g.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction.nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator`
- Dependency: [D5/S3/VertexAlgebra/ActualTensorGroundIntersection](../ActualTensorGroundIntersection.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction](LatticeHalfFockFixedCyclicReduction.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](../LatticeHalfFockCurrentBorcherds.md)
