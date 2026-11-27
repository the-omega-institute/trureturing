# Fixed Weight-Two States under the P48p Small-Factor Bounds

## Abstract

The small-factor bounds in the P48p analysis force two independent fixed states of actual conformal weight two.

**Theorem 1.1 (Two independent fixed states for the small-factor case).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo.p48p_small_factor_fixed_weight_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo.p48p_small_factor_fixed_weight_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let D have rank 48 and a positive-definite real Gram matrix. The finite group H has a subgroup K of order at most 16 with index dividing 12 and acts on the integral charges by bilinear isometries. A group E acts on the actual carrier by complex linear equivalences preserving every integer vertex mode. Through a homomorphism π from E to H, each e sends the ground state at a to the ground state at the charge prescribed by π(e), multiplied by a unit depending on e and a.

The real irreducible degree bound for the small-factor case gives a proper nonzero invariant subspace in the real Cartan representation of H. Pulling the action back along π gives the invariant subspace required for the Gram projector construction. The theorem gives a complex matrix C with C gramComplex(D) = 1 and a pair of complex-linearly independent states in grade two. Both states are fixed by every e, and mode one of the field of omega(D,C) acts on each by the scalar two.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo.p48p_small_factor_fixed_weight_two`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo](ReducibleActionWeightTwo.md)
