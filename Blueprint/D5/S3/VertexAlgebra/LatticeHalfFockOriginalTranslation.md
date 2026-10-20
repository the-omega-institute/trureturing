# Physical Translation of Every Corrected Source

## Abstract

Physical Translation of Every Corrected Source

Let D:LatticeData be arbitrary, hu:IsUnit D.G.det, source:Carrier D, e:Int and v:ActualTensor D hu. Carrier D consists of finite charge support with algebraic oscillator polynomial coefficients. ActualTensor D hu is the original dependent algebraic tensor module. All signed exponents, zero charges, repeated variables, inhomogeneous states, indefinite Gram data and degenerate fibres remain in scope.

Write A_i(F)=wordField D hu F [i] and S_s(F)=shiftField D hu s F. The physical derivative is a genuine Hahn field with coefficient ((e+2)/2) smul F.coeff(e+2). The existing joint pointwise finite support justifies every singleton mode sum. The jet recurrence (k+1)*jetScalar(k+1,m)=(-m-3/2-k)*jetScalar(k,m) gives the Leibniz identity Dphys(A_i F)=(k+1) smul A_successor(i)(F)+A_i(Dphys F). The split remains the original m<0 negative-left and m>=0 nonnegative-right split.

The Hahn shifts satisfy S_s S_t=S_(s+t) and commute with singleton insertion. Physical differentiation satisfies Dphys S_1=S_1 Dphys-S_2. These identities hold coefficientwise for every integer exponent without division by e+2.

Let Q be a polynomial in the option-indexed correction variables, with t=X none and x_i=X(some i). normalEvaluation E_q sends t multiplication to S_1 and x_i multiplication to A_i. It is a linear evaluator, not an algebra homomorphism. The polynomialField_X_mul theorem supplies the oscillator step through monomial occurrences and word permutation.

The oscillator connection sends t to -t^2 and x_i to (i.2+1) smul x_successor(i). Add multiplication by sum_colour q_colour*x_(colour,0) minus chargeNorm(q)/2 times t, obtaining L_q. The pair derivations in correctionConnection cancel the pair terms in the charge-weighted insertions. The sum of singleton corrections is -chargeNorm(q)/2 times t. Thus correctionConnection Q plus the charge-weighted insertions equals L_q Q.

MvPolynomial.induction_on proves E_q(L_q Q)=Dphys(E_q Q). Constants use the canonical all-ActualTensor charged_seed_physical_coefficient theorem. Addition uses linearity. Oscillator variables use the actual singleton Leibniz rule, and the shift variable uses Dphys S_1=S_1 Dphys-S_2. The public Corr_sectorTranslation contract then gives correctedPolynomial translation in every charge sector, without accessing its private correctedSource helpers. Finsupp.induction_linear over source charges yields the exact endpoint.

The jet, shift and evaluator calculation is adapted from the preserved OriginalTranslation source, SHA256 0442324ef84346403888d5faa093adffdd3ec23b77918c37b81252c5404b008a, and its declared TranslationCalculus supplier 8117eb5f8f5d301d5126a8d2fc054d22a1d7d2c314847a8b1699c89f5d123cd7. The charged ground and creation induction is reused from the canonical ChargedSeedPhysical owner. Classical sources are Frenkel-Lepowsky-Meurman (1988), Dong-Nagatomo math/9808088v1 section 3.2, and Bakalov-Kac math/0402315v1 section 4.4. Inherited half-Fock implementation copyright (c) 2025 Kalle Kytola; additional half-integer matrix implementation copyright (c) 2026; Apache 2.0. No mathematical novelty is asserted.

The result concerns every algebraic polynomial and tensor state; it does not construct a completion by infinite oscillator series. Twisted locality, Jacobi and Borcherds identities, full VOA and CFT constructions, anomaly and fusion structures, string dynamics, spacetime reconstruction and AdS/CFT remain further mathematical obligations.

**Theorem 1.1 (The exact canonical Hahn shift).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.shiftField_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.shiftField_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, s:Nat, A:NativeField D hu and e:Int, (shiftField D hu s A).coeff e = A.coeff(e+2*s), as endomorphisms of ActualTensor D hu. Hahn monomial multiplication by t^(-2*s) changes the coordinate by exactly -2*s. Physical translation and full-source theta monodromy both use this same shift.

**Theorem 1.2 (The exact all-source physical translation identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.correctedField_translation_physical`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.correctedField_translation_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, source:Carrier D, e:Int and v:ActualTensor D hu, (correctedField D hu (LatticeSugawaraConformal.translation D source)).coeff e v = (((e+2:Int):Complex)/2) smul (correctedField D hu source).coeff (e+2) v. The source translation is the actual Sugawara translation, the field is the native finite Corr-corrected Hahn field, and the target is the actual dependent tensor module. No derivative or seed law is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.correctedField_translation_physical`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation.shiftField_coefficient`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedSeedPhysical](LatticeHalfFockChargedSeedPhysical.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectionTranslation](LatticeHalfFockCorrectionTranslation.md)
