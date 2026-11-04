# From raw coefficients to every oscillator and ground vector

## Abstract

Irreducibility of the entire actual tensor module under the corrected field.

Let D be an arbitrary integral symmetric even lattice datum and hu:IsUnit D.G.det. The carrier is the production ActualTensor D hu, namely the polynomial half-Fock oscillator tensored with the selected irreducible ActualGround D hu. Sources lie in the ordinary Carrier D; source and target are different spaces. Let S be any complex submodule of this entire tensor.

**Theorem 1.1 (Every coefficient-stable submodule is zero or the whole tensor).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible.correctedField_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible.correctedField_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assume only that for every source v, every raw integer exponent e and every x in S, (correctedField D hu v).coeff e x lies in S. Then S is bottom or top. No current stability, ground-action stability, cyclicity, target irreducibility, preferred-model identification, rank condition, positive definiteness, norm-four condition, rootlessness or Jacobi identity is assumed.

The source neutralMode i (-1) vacuum has raw coefficient -2*k-3 equal to tensorCurrent i k. Thus the given hypothesis supplies all integer currents, with their half-integer frequency k+1/2. The existing nonzero_current_stable_submodule_meets_ground theorem supplies a nonzero g with 1 tensor g in S whenever S is nonzero. It already proves the simultaneous polynomial-coordinate descent and inverse-Gram transport.

Define the ground intersection by the condition 1 tensor g lies in S, equivalently the inverse image of S under this linear tensor insertion. For the source single charge 1 the corrected field equals the actual charged field coefficientwise. At exponent -chargeNorm the charged vacuum coefficient is chargeScalar times 1 tensor groundAction(charge) g. The existing zero creation coefficient is 1 and chargeScalar=2^(-chargeNorm) is nonzero. Scalar cancellation proves stability of this intersection under every groundAction without projecting any coordinate out of S.

Every quotient representative has a sign and a charge. It is the product of its central sign representative and its zero-sign charge lift. The two central signs act by identity and minus identity. Consequently the intersection is an actual subrepresentation of the production selected groundRepresentation. Its selected irreducibility makes a nonzero intersection the entire ground space. Finally tensorCurrent i (-(k+1)) multiplies the oscillator by X(i,k). Polynomial induction gives every pure tensor in S, and tensor induction gives the whole ActualTensor.

This is the classical algebraic irreducibility mechanism for the production corrected twisted lattice field; no literature novelty is claimed. It is separate from the existing derivative, Ward, current Borcherds and sectorwise all-state Borcherds identities. It does not construct a two-twisted intertwining operator, orbifold gluing, all-grade Ising or Miyamoto fusion, a Monster action, or a complete CFT, string-theory or AdS/CFT bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible.correctedField_irreducible`
- Dependency: [D5/S3/VertexAlgebra/ActualTensorGroundIntersection](../ActualTensorGroundIntersection.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds](../LatticeHalfFockCurrentBorcherds.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
