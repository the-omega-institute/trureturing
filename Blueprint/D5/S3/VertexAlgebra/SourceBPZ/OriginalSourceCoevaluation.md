# Original Source Coevaluation

## Abstract

Explicit original inverse-Wick coefficients and finite theta-projected source coevaluation.

D is the existing integral even lattice datum, of arbitrary natural rank. The oscillator ring is MvPolynomial (Fin D.rank x Nat) Complex and Carrier D is the original finitely supported charge-to-polynomial space. Q is OriginalSourcePairing.sourcePairing D, a complex bilinear form, with opposite-charge pairing. Its oscillator covariance at natural index k is exactly -(k+1) times the complex Gram matrix. The mode is the original integer oscillator mode k+1; no half-frequency covariance is substituted for it.

For a label a=(q,alpha), dualCarrierBasis D a is single(-q,d_alpha), where d_alpha is the monomial X^alpha transformed by inverseOscillator and multiplied by the reciprocal of weight(alpha). The latter is the product of alpha(i,k)! over all occupied variables. inverseOscillator sends X(i,k) to the sum over j of (-(k+1)) inverse times Gcomplex inverse[j,i] times X(j,k). This is the actual matrix inverse, including off-diagonal Gram entries, with the column convention of OriginalCurrentMetric.variableImage. Rank zero and empty occupation are retained.

**Theorem 1.1 (Original coefficient extraction).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, determinant-unit proof hu:IsUnit D.G.det, label a and original v:Carrier D, Q(dualCarrierBasis D a,v)=carrierCoeffEquiv D v a. No energy, positivity or theta hypothesis occurs. The proof composes the original Wick substitution with retune, computes -(k+1)G, cancels its actual inverse and cancels the full occupation factorial.

**Theorem 1.2 (Exact signed energy preservation).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_mem_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_mem_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and label a, dualCarrierBasis D a belongs to grade D (energy D a). There is no determinant-unit or positivity hypothesis. Each substituted variable keeps its mode, so weighted homogeneous degree is preserved; charge reversal keeps the quadratic charge energy.

For every signed integer h, EnergyFiber D h is the entire charge/occupation energy fiber. fixedFrame D h a is plusPart of the original carrier basis vector and fixedDualFrame D h a is plusPart of its explicit dual. Both lie in grade D h intersect fixedSpace D. plusPart is exactly one half of v+theta(v). These are frames indexed by the whole fiber, with no assertion of independence and no theta-orbit representatives. coevaluation D h f is the finite sum of f(fixedFrame a) times fixedDualFrame a. Positive definiteness of the real Gram matrix supplies finiteness whenever this sum is evaluated.

**Theorem 1.3 (Computed finite-grade inverse).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu:IsUnit D.G.det, hD:PosDef of the real Gram matrix, h:Int, f in the full complex dual of grade D h intersect fixedSpace D, and x in that same original submodule, Q((coevaluation D h f).val,x.val)=f(x). The actual carrier coefficient expansion and reflection isometry evaluate this explicit frame. No completion or identification of the algebraic carrier with its full dual is used.

**Theorem 1.4 (Finite native scalar contraction).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, hD, signed h, f and g in the full dual of the original fixed grade, and x in that fixed grade satisfying Q(x,y)=f(y) for every y in it, g(x) is the sum over EnergyFiber D h of f(fixedFrame a)*g(fixedDualFrame a). Existing FixedGradedDuality supplies uniqueness internally. In particular x can be the value of the existing pairing equivalence inverse, using its evaluation law; the theorem computes its coefficients rather than constructing another duality.

**Theorem 1.5 (The original source half-average).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_half_average`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_half_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, hD, signed h, f and g in the full dual of Carrier D, and x in the original fixed grade representing the restriction of f by Q, g(x.val) equals one half of the sum over EnergyFiber D h of [f(carrierBasis a)+f(theta(carrierBasis a))] times g(dualCarrierBasis a). Thus the double projected frame is exactly the original kernel with a single half-average on the first leg. Zero charge and fixed theta orbits are included without further division.

**Theorem 1.6 (Negative integer source grades).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hD:PosDef of the real Gram matrix, h:Int with h<0, and f in the dual of the original fixed grade h, coevaluation D h f is zero. The energy fiber is empty because charge energy and oscillator energy are nonnegative. The claim is over signed integers, before any conversion to a natural cutoff.

**Theorem 1.7 (The genuine zero-grade vacuum).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hD:PosDef of the real Gram matrix and f in the dual of the original fixed grade zero, coevaluation D 0 f is f(gradeVacuum D) times gradeVacuum D. gradeVacuum has value exactly the original single(0,1). The only zero-energy label is (0,0), whose occupation factorial is one and whose inverse polynomial is one; theta fixes this vacuum.

**Theorem 1.8 (Signed native contraction branches).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_signed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, hD, signed h, f in the full dual of the original fixed grade, ambient scalar test g and x representing f by Q, g(x.val) is zero when h<0, f(gradeVacuum)*g(vacuum) when h=0, and the finite frame contraction otherwise. The zero-grade functional is transported along the equality h=0. This computes the actual integer negative and vacuum branches before converting any mode support to natural indices.

OriginalFourMContraction.fourM_contraction consumes both inverse_contraction_half_average and inverse_contraction_signed on the actual native four-M coefficient. It takes h=H+K-k-1, f=normalizedCoefficient D hu k u v h, x=E.symm f for the existing original source-pairing fixed-grade equivalence, and g(a)=actualForm(d,correctedField(a).coeff(-2*t-2) w). Its proved native_kernel_restriction identifies f with the restriction of the actual homogeneous ambient kernel. The single-half-average formula is therefore applied to the actual original scalar functional. The signed companion has this live mathematical consumer, including its negative, vacuum and positive branches.

This is classical algebraic Wick and finite-frame computation, with no literature novelty claim. Existing polynomial, matrix inverse and bilinear machinery retains its Mathlib Apache-2.0 attribution; the original lattice and Wick sources retain their own notices. The analytic Gaussian native-channel supplier, determinant and charge normalizations, common rationality, crossing and three-M Jacobi are further obligations. No fusion, anomaly, complete string theory or AdS/CFT conclusion follows from this coefficient formula.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_negative`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.coevaluation_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_mem_grade`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.dualCarrierBasis_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_half_average`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourceCoevaluation.inverse_contraction_signed`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedGradedDuality](../Lattice/FixedGradedDuality.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws](SourcePairingLaws.md)
