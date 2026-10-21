# Coordinate Monodromy of Every Corrected Source

## Abstract

Coordinate Monodromy of Every Corrected Source

Let D:LatticeData be any finite-rank integral symmetric even lattice and hu:IsUnit D.G.det. The ordinary source Carrier D is the finite charge sum of algebraic oscillator polynomials. The target ActualTensor D hu is the original oscillator algebra tensor the actual quotient ground module. All integer exponents, zero charges, rank zero, indefinite Gram matrices, repeated oscillators, inhomogeneous sources and arbitrary target tensors remain in scope.

The actual quotient ground action identifies charge a and -a by reduction modulo two. The creation logarithm and translated polynomial have only odd coordinate frequencies. Charge negation therefore gives chargedCoefficient(-a,e)=(-1)^e smul chargedCoefficient(a,e), using the even norm B(a,a). No inverse ground-action substitution is used.

**Theorem 1.1 (Normal polynomial parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.normal_polynomial_coordinate_monodromy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.normal_polynomial_coordinate_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, a:Charge D, p:Oscillator D and e:Int, (polynomialField D hu (-a) (sigma D p)).coeff e = ((-1:Complex)^e) smul (polynomialField D hu a p).coeff e, as endomorphisms of ActualTensor D hu. Each word coefficient factors through the charged coefficient at e+2*modeSum+jetShift. The parity of jetShift is the word length. sigma multiplies a monomial by the same word-length sign, and the two signs cancel. The native pointwise finite-support theorem justifies the mode sum separately at every target vector; no finite End-valued mode support is claimed.

**Theorem 1.2 (Equivariance of the original finite correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.Corr_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.Corr_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, a:Charge D and p:Oscillator D, Corr D (-a) (sigma D p) = Finsupp.mapRange.linearMap (sigmaLinear D) (Corr D a p). The correction lift fixes X none and negates X(some i). It fixes the pair polynomial, anticommutes with each pair derivation, and takes insertion at a to minus insertion at -a. Word induction gives exactly the monomial sign of sigma. optionEquivLeft carries the lift to Polynomial.map sigma without a shift-dependent sign. The correction is linear and is not treated as an algebra homomorphism.

**Theorem 1.3 (The full source theta identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.correctedField_theta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.correctedField_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, u:Carrier D and e:Int, (LatticeHalfFockCorrectedField.correctedField D hu (LatticeInvolution.theta D u)).coeff e = ((-1:Complex)^e) smul (LatticeHalfFockCorrectedField.correctedField D hu u).coeff e. This is equality in Module.End Complex (ActualTensor D hu). The field, correctedPolynomial, correctedSum and shiftField are precisely those defined in LatticeHalfFockOriginalTranslation. The canonical shift has coefficient A.coeff(e+2*s), and (-1)^(e+2*s)=(-1)^e for every signed e and natural s. Finite correction extensionality followed by finite-charge linear-map extensionality and theta_single proves the equality. There is no action of theta on the target and no eigenstate or pure-tensor restriction.

Classical provenance: Frenkel-Lepowsky-Meurman (1988); Dong-Nagatomo math/9808088v1 section 3.2, pp.12-14; Bakalov-Kac math/0402315v1 (4.4), (4.23)-(4.38). The normal parity, shift-fixing correction lift and full theta argument follow the preserved CorrectedField proposal; the charged argument is supplied by LatticeHalfFockChargedMonodromy. The canonical original-translation source supplies all field constructors. Inherited half-Fock implementation copyright (c) 2025 Kalle Kytola; additional half-integer implementation copyright (c) 2026; Apache 2.0. Finite support architecture follows VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 and PolynomialFock bfd9ff0f15397a4fb933f36d701a60d325d84b08. No literature novelty is asserted.

This coordinate identity is one ingredient for a twisted vertex-operator construction. All-source locality and source-product identities, twisted Jacobi and Borcherds, conformal and positive-energy structure, analytic sewing, fusion and anomalies, orbifold and Monster/Moonshine realization, complete string dynamics and the AdS/CFT bridge remain further obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.Corr_sigma`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.correctedField_theta`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy.normal_polynomial_coordinate_monodromy`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](LatticeHalfFockChargedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](LatticeInvolution.md)
