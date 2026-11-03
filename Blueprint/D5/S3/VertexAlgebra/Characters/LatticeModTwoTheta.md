# Original mod-two charge-fibre theta bridge

## Abstract

Original mod-two charge fibres are identified with the actual discriminant sectors of the doubled Gram form. This classical lattice construction transports the existing sector S and T laws; it does not prove a second Poisson or sector S theorem.

The input is the original even integral LatticeData D, an integral unit determinant, and positive definiteness of gramReal D. All natural ranks, including zero, every original mod-two charge, and the whole upper half-plane remain in scope. The lattice conventions and modular suppliers are those of LatticeDiscriminantTheta and LatticeDiscriminantWeil; the signs are the original cocycle-derived OriginalFourMChargeCoset signs. No novelty claim is made for these classical mathematical statements.

**Definition 1.1 (Doubled original Gram form).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.Gram2G`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.Gram2G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the original rank and multiply the original integral Gram matrix by two. Symmetry and evenness are constructed directly.

**Definition 1.2 (Integral lift of the original parity charge).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.chargeLift`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.chargeLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the actual ZMod 2 value in each original coordinate as an integer. This is a representative, not an additive section.

**Definition 1.3 (Actual additive quotient equivalence).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.phi`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class of G times the integral lift defines an AddEquiv from the original mod-two charges to Z^rank / (2G) Z^rank. The integral inverse of the unimodular Gram matrix proves bijectivity. Equality of classes is exactly equality of the original reductions modulo two.

**Definition 1.4 (Literal unbounded original charge fibre).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.parityTheta`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.parityTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum exp((pi i tau / 2) times bilinear D p p) over the original subtype reduceCharge D p = a. The definition includes negative integer charges and does not use a discriminant-sector theta.

**Theorem 1.5 (Quotient, phases, convergence and exact modular transport).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.original_modTwo_theta_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.original_modTwo_theta_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive unimodularity gives det G = 1 and det(2G) = 2^rank. The rational inverse of 2G sends Gp to p/2; its pairing on Gp,Gq is bilinear D p q divided by two and its quadratic value is bilinear D p p divided by four. Actual two-torsion removes the negative Fourier character, yielding the unchanged original fourierSign; the original cocycle energy yields quadraticSign. The bijection n maps to 2n + lift(a) parametrizes the literal fibre, giving absolute convergence and equality to sectorTheta (Gram2G D) (phi a). Consuming the frozen sector_S and sector_T gives the principal complex factor (-i tau)^(rank/2) / sqrt(2^rank) and the original signs, without an additional phase, branch, parity or positive-rank premise.

This is only the charge-coset modular supplier. OriginalFourMChargeCoset.cosetKernel still contains both chargeScalar factors 2^(-norm p), the half-average with theta reflection, the oscillator kernels and the inverse-Gram/factorial dual oscillator monomial. Their coefficient transport and the homogeneous parity-state premises of the actual fourM/Jacobi use remain work. No unrestricted identityK, original full crossing, Monster realization, full VOA/CFT, string theory or AdS/CFT completion is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.Gram2G`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.chargeLift`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.original_modTwo_theta_bridge`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.parityTheta`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.phi`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil](LatticeDiscriminantWeil.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](../TwistedGround/OriginalFourMChargeCoset.md)
