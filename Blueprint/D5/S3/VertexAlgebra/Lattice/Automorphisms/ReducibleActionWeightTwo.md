# Fixed Weight-Two States from a Reducible Charge Action

## Abstract

A proper nonzero invariant real Cartan subspace yields two independent fixed states of actual conformal weight two.

**Definition 1.1 (Real extension of a charge automorphism).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeAction`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For LatticeData D and an additive charge automorphism g, the real linear equivalence has matrix M with column j given by the coordinates of g applied to the j-th unit charge. The matrix for g⁻¹ gives the inverse.

**Definition 1.2 (Real Cartan representation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeRepresentation`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the multiplicative group obtained from the additive automorphism group of the charge lattice, the real extension gives a representation on the real coordinate space. Charge coordinate expansion identifies matrix multiplication with composition of charge automorphisms.

**Theorem 1.3 (Actual quadratic covariance).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.actual_omega_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.actual_omega_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Suppose the additive automorphism g preserves the integral bilinear form and the complex linear equivalence U preserves every actual integer mode. Suppose also that U sends each ground state at charge a to a unit scalar times the ground state at g(a). For every complex matrix A, U sends omega(D,A) to omega(D,MAMᵀ), where M is the complex matrix of g on the unit charges. Opposite-charge products recover the same current action as the canonical lift. Each quadratic is a sum of actual mode-minus-one products of those currents, so its image is determined by that current action.

**Theorem 1.4 (Two independent fixed weight-two states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.reducible_action_fixed_weight_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.reducible_action_fixed_weight_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assume the real Gram matrix is positive definite. Take indexed charge isometries g(t) and compatible complex equivalences U(t) satisfying the mode and ground-line hypotheses above for every t. If a proper nonzero real subspace W is invariant under every real extension of g(t), there are matrices H and P with H gramComplex(D) = 1. The ordered pair omega(D,PH), omega(D,H) lies in grade two, is linearly independent over ℂ and is fixed pointwise by each U(t). Mode one of the field of omega(D,H) multiplies both states by two. The Gram-orthogonal projector onto W provides P, and its commutation and self-adjointness give the required quadratic invariance.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.actual_omega_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeAction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.realChargeRepresentation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ReducibleActionWeightTwo.reducible_action_fixed_weight_two`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantGramProjector](InvariantGramProjector.md)
