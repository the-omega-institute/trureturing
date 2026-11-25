# Conformal Ground Transport on a Rootless Lattice VOA

## Abstract

Actual conformal automorphisms recover integral charge isometries and transport charge ground lines.

D is ordinary even integral LatticeData. The physical carrier is the actual finite-support charge direct sum of complex oscillator polynomials. The transport statements assume a real positive-definite Gram matrix hPos and rootlessness hRoot, namely no integral charge has bilinear norm two. For the chosen quadratic state omega(D,H), hHG and hGH state H * gramComplex(D) = 1 and gramComplex(D) * H = 1. A complex-linear automorphism U must preserve every integer vertex mode through hMode and fix omega(D,H) through hOmega.

The grade-one current basis is the rootless energy-one basis. The mode-one calculation reduces the product of two canonical currents to the neutral mode coefficient and gives (Y(currentState D i))[[1]] (currentState D j) = (D.G i j : ℂ) • vacuum D. Bilinearity then identifies arbitrary current mode-one products with the complex Gram form. The mode-zero coefficient theorem reads every coefficient of a state by its Gram pairing with that coefficient's charge, so the joint zero-mode eigenvalues determine the transported integral charge.

**Definition 1.1 (Complex linear combinations of canonical currents).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The state current(D,x) is the finite complex linear combination of the canonical grade-one current states indexed by Fin(rank).

**Theorem 1.2 (Mode-one current Gram identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_one_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_one_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual neutral mode calculation gives the lattice Gram entry times the vacuum for every pair of basis currents. This is the invariant form recovered from the mode-one product.

**Theorem 1.3 (Current zero modes read charge).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_zero_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_zero_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every state coefficient q, the zero mode of current(D,x) multiplies that coefficient by the complex Gram pairing of x with q's integral charge. This supplies the joint spectral readout used below.

**Theorem 1.4 (Recovered additive integral isometry).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_charge_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_charge_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Under hPos, hRoot, hHG, hGH, hMode and hOmega, U induces a unique additive equivalence s of the actual charge lattice preserving bilinear. Every occupied coefficient of U(single(a,p)) has charge s(a), so s is recovered by the current zero-mode spectrum on the actual carrier. The nonzero image of each ground state determines the charge at that input.

**Theorem 1.5 (Charge ground lines are transported).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

With the same hypotheses, each ground state single(a,1) is sent to a nonzero unit scalar times single(s(a),1). Preservation of the Sugawara grade and of the lattice norm forces oscillator energy zero in the image. The charge map is determined by the zero-mode labels, while eta records the remaining line scalar.

**Theorem 1.6 (Conformal group actions project to the integral isometry group).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For groups G and K, an injective additive identification mu from K into charge automorphisms must have range containing every bilinear isometry. A mode-preserving, omega-fixing representation U of G then yields a group homomorphism pi : G →* K and ground-line units eta with charge action mu(pi(g)). Composition of ground-line maps gives the group law for pi, because nonzero ground states at distinct charges have disjoint support.

This projection supplies the ground-line action in finite-group obstructions for the rootless lattice theory. The isometry-group identification and the twisted-sector lowest-weight conditions are separate inputs to those obstructions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_charge_transport`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_projection`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.conformal_ground_transport`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_one_current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Automorphisms/ConformalGroundTransport.current_zero_coeff`
- Dependency: [D5/S3/VertexAlgebra/Lattice/RootlessLowGrades](../RootlessLowGrades.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../../LatticeActualConformalState.md)
