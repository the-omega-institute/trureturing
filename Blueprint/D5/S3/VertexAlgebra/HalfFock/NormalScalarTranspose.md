# Original Normal-Field Scalar Transpose

## Abstract

Original Normal-Field Scalar Transpose

The source is the original finite-charge Carrier and the target is exactly ActualTensor D hu. D is arbitrary LatticeData and hu is the original integer IsUnit D.G.det. Rank zero, indefinite lattices, zero inputs, zero charge, signed norms and exponents, repeated occurrences and empty words remain in scope. The bilinear ground form is kept in its original orientation; no symmetry or new nondegeneracy assumption is used.

The current transpose follows from the existing signed wick_creation and wick_lowering. For any two original tensor inputs, cutoff preservation under same-sign currents gives the true scalar mode rectangle -Uy<=k<Ux. The charged scalar interval uses lower truncation on both inputs and the already constructed same-charge charged transpose. Exact modeSum and jetShift translations and finite unions then give the finite scalar normal/source exponent windows.

Finite lowered-jet choices supply the actual flat, word, polynomial and source transpose. Word weight is the sum of r+1 over occurrences. The exponent is -e-2N-2R-2S=-e-2N-4R+2j, j=R-S. The factor is paritySign(N/2)*(-1)^R*product choose(r+1,s+1). All right-hand coefficient evaluations remain B(x,Y(...)y). No infinite Hahn-vector support is reversed.

The correctedField consumer expands its actual finite Corr coefficients first and obtains exponent -(e+2c)-2N-4Rm+2j. This finite readout does not establish the full corrected exp(L1) formula. The remaining signed substitution fixes u and sends X_(i,r) to (-1)^(r+1)P_u X_(i,r); the needed identity is sigma_u C_a(u)p=C_a(u)((-1)^R E_a(u)p). With exact weight conservation, the unsigned convention is P_u C_a(-u)p=C_a(u)E_a(u)p. The minus sign in C_a(-u) is essential.

Original Corr covariance, exact Corr weight conservation and the source-L1 coefficient identity must be integrated and validated before the full corrected exp(L1) inversion follows. Restricted-dual representability, mixed Jacobi, intertwiner and fusion constructions and the complete Monster, CFT, string-theory, AdS/CFT and local-to-global objective remain open. This is classical algebraic bilinear Fock normalization, with no literature novelty claim.

**Theorem 1.1 (actual current transpose).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_current_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_current_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k, B(h_i(k)x,y)=-B(x,h_i(-k-1)y) on the original ActualTensor. The consumed tensor proof allows any ground bilinear form and never interchanges its arguments.

**Definition 1.2 (scalarModeRectangle).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.scalarModeRectangle`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.scalarModeRectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Original mode tuples in [-Uy,Ux), using actual tensor-current truncation cutoffs of y and x respectively. No charged exponent or derivative order enters these bounds.

**Theorem 1.3 (actual flat scalar mode support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_scalar_mode_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_scalar_mode_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero scalar flatCoefficient forces every original mode into the fixed input-pair rectangle. Same-sign current commutation preserves each cutoff along the normal recursion.

**Theorem 1.4 (actual word scalar rectangle).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original pointwise wordField coefficient pairs as an ordinary finite sum over the input-pair rectangle. The vector support remains pointwise; no operator-space finite support is asserted.

**Definition 1.5 (wordExponentWindow).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordExponentWindow`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordExponentWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite union over the scalar mode rectangle of actual charged scalar intervals translated by minus twice modeSum minus the original jetShift.

**Theorem 1.6 (actual word scalar exponent support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_exponent_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_exponent_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar chargedWordField coefficients have finite exponent support for each pair of actual tensor inputs, including signed norms and exponents.

**Theorem 1.7 (jetScalar reflection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.jetScalar_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.jetScalar_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact original descending-Pochhammer jet scalar reflects through the finite binomial triangle choose(r+1,s+1), retaining every lowered order 0<=s<=r.

**Definition 1.8 (JetTuple).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.JetTuple`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.JetTuple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite independent choices of lowered jet order for each original occurrence. Empty words and repeated letters retain their original multiplicity.

**Definition 1.9 (lowerWord).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.lowerWord`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.lowerWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original word with the same colours and occurrence order, replacing each jet order by its chosen lower order.

**Definition 1.10 (triangleCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.triangleCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.triangleCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Product of (-1)^(r+1)*choose(r+1,s+1) over every occurrence. The original jet reflection supplies these signs.

**Definition 1.11 (transposeExponent).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.transposeExponent`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.transposeExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed original reflected exponent -e-2N-2R-2S, with N=bilinear D a a and R,S the original and lowered word weights.

**Theorem 1.12 (actual flat transpose).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the actual flatCoefficient recursion proves its scalar transpose, exchanging negative-left and nonnegative-right at k -> -k-1. The charged seed supplies paritySign(N/2). No normal-adjoint premise or reflected-field surrogate is introduced.

**Theorem 1.13 (actual word transpose).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine bijection of original ModeTuple types and finite sum exchange identifies the transpose with the original chargedWordField at the exact reflected exponent.

**Definition 1.14 (wordPolynomial).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original oscillator polynomial product of variables in a word. Its normal polynomialField is identified with the original chargedWordField.

**Theorem 1.15 (actual polynomial monomial transpose).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_polynomial_monomial_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_polynomial_monomial_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original polynomialField monomial transposes to a finite lowered-word sum, still evaluated by the original polynomialField.

**Definition 1.16 (weightLoss).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.weightLoss`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.weightLoss` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural weight loss j=R-S, justified by each chosen order being no greater than its original order. Thus -e-2N-2R-2S=-e-2N-4R+2j.

**Definition 1.17 (binomialProduct).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.binomialProduct`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.binomialProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unsigned product of choose(r+1,s+1). The complete coefficient is paritySign(N/2)*(-1)^R times this product.

**Definition 1.18 (sourceExponentWindow).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.sourceExponentWindow`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.sourceExponentWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite unions of the original word exponent windows over the actual charge and polynomial basis supports of the source.

**Theorem 1.19 (actual source scalar exponent support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_exponent_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_exponent_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original finite-charge sourceField has finite scalar exponent support for each pair x,y, without a finite full weight-space assumption.

**Theorem 1.20 (actual source scalar transpose).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual sourceField scalar transpose has coefficient paritySign(N/2)*(-1)^R*product choose(r+1,s+1) and exponent -e-2N-4R+2j. Every right-hand term is B(x,sourceField(original finite source).coeff(...) y); ground orientation is unchanged.

**Definition 1.21 (correctedExponentWindow).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.correctedExponentWindow`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.correctedExponentWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite union of the original source exponent windows for actual Corr coefficients, translated by minus twice the actual correction index.

**Theorem 1.22 (actual corrected scalar exponent support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_exponent_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_exponent_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original correctedField has finite scalar exponent support for each actual input pair, by its actual finite Corr expansion and exact shiftField coefficient law.

**Theorem 1.23 (actual corrected scalar normal readout).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_normal_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_normal_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unconditional original correctedField readout retains Corr D a (v a) at each supported c and monomial weight Rm, with exponent -(e+2c)-2N-4Rm+2j. It assumes no Corr covariance, Corr homogeneity or source-L1 law.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.JetTuple`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_exponent_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_corrected_scalar_normal_readout`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_current_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_scalar_mode_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_flat_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_polynomial_monomial_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_exponent_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_source_scalar_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_exponent_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_scalar_rectangle`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.actual_word_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.binomialProduct`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.correctedExponentWindow`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.jetScalar_reflection`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.lowerWord`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.scalarModeRectangle`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.sourceExponentWindow`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.transposeExponent`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.triangleCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.weightLoss`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordExponentWindow`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormalScalarTranspose.wordPolynomial`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](../LatticeHalfFockFiniteCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField](../LatticeHalfFockFockNormalField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint](../TwistedGround/ActualChargedAdjoint.md)
