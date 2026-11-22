# Reduction to fixed-source integer modes

## Abstract

Finite current elimination on the actual negative-parity half-Fock module.

**Theorem 1.1 (A current after an odd-source coefficient belongs to the fixed-mode span).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction.current_after_odd_coeff_mem_fixedParitySlice_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction.current_after_odd_coeff_mem_fixedParitySlice_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let data consist of a lattice datum D and a unit witness hu for det(D.G). Take i in Fin D.rank and b in Carrier D with theta D b = -b. For every x in paritySpace D hu (-1) and every pair of integers k and e, there exists y in paritySpace D hu (-1) whose underlying tensor is tensorCurrent D (ActualGround D hu) i k applied to the raw coefficient e of correctedField D hu b at x.val. The vector y belongs to the complex span of (fixedParitySlice D hu (-1) a)[[n]] applied to the same x, with a ranging over FixedCarrier D and n over the integers.

Coordinate monodromy gives zero for even e. For odd e, write e = -2q-3, the coefficient for mode q in the physical slice with shift 1. Choose a current truncation index p for x and put r = k-p. At summation index j, the left Borcherds term has fixed source neutralMode D i (r+j) b and raw exponent -2(p+q-j)-4. This is 2(-n-1) for the integer fixed-source mode n = p+q-j+1.

The second ordering vanishes by truncation at p+j. The first ordering starts with the desired product at j=0 and has only finitely many other terms at q+j. Strong induction on the distance to the Hahn cutoff places those products in the same span. The inclusion of the negative-parity subtype maps this span into the tensor module, and membership in its image supplies y together with its span membership.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockFixedCyclicReduction.current_after_odd_coeff_mem_fixedParitySlice_span`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField](LatticeHalfFockParityField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](../LatticeHalfFockCurrentBorcherds.md)
