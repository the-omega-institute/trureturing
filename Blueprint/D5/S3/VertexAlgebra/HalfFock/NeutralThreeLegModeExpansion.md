# Actual neutral-field finite mode and Laurent expansion

## Abstract

Actual neutral-field coefficients have finite projected mode support and a raw Laurent expansion on arbitrary ground tensors.

The common finite mode set is {-k-1 : k is an output frequency} union {k : k is an input frequency}. Positive currents mix colours only at a fixed frequency. A negative mode outside the output frequency support can create a nonzero full vector, but its specified output coefficient vanishes. The support theorem therefore extracts that coefficient before restricting the sum.

The flat normal recursion is factored into creation multiplication on the left and Gram-weighted annihilation on the right. The proof uses the existing same-sign Heisenberg commutation law, the native monomial derivative and actual pointwise finite-support theorem. Ground vectors are carried by identity; no scalar ground vacuum is chosen.

The existing energy covariance supplies e = 2(E_T(output)-E_T(input)-E_S(source)), in doubled integral twisted-energy coordinates. The actual coefficients are represented by a finitely supported scalar Laurent polynomial. Evaluation is allowed only at a complex unit T and is a finite sum.

**Definition 1.1 (Actual neutral source).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.neutralSource`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.neutralSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge-zero carrier element is Finsupp.single 0 (monomial d 1), with arbitrary finite multiplicities.

**Definition 1.2 (Actual full corrected coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The field is correctedField on the existing ActualTensor carrier; no alternative Gaussian field is defined.

**Theorem 1.3 (Actual Corr and pointwise normal expansion).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_native_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_native_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Corr support and residual polynomial support precede the native pointwise flatTerm finsum.

**Definition 1.4 (Full ground-valued output coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeOutputProjection`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeOutputProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial coefficient map is tensored with identity and composed with the canonical scalar tensor identification. Its result is the entire ground vector.

**Theorem 1.5 (Proved projected frequency support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_projected_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_projected_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word, exponent, repeated input and output occupation, ground vector and mode tuple, a nonzero projected flatTerm implies membership of every mode in the common output-negative/input-positive frequency set. There is no vector-support hypothesis.

**Theorem 1.6 (Common finite projected mode sum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_frequency_projected_mode_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_frequency_projected_mode_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each exponent and arbitrary ground vector, the output coefficient of the actual normal word equals the sum over the finite Cartesian mode box built from the output and input frequency supports.

**Theorem 1.7 (Actual corrected output exponent selection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_output_energy_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_output_energy_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full ground-valued corrected entry vanishes unless e equals oddWeight(output) minus oddWeight(input) minus twice the source weight. The proof consumes existing full-field energy covariance.

**Theorem 1.8 (Finite actual corrected entry).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_finite_projected_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_finite_projected_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact output projection is a finite Corr shift, residual monomial and normal-mode sum. Its integer selector is retained; normal creation and annihilation act on the original polynomial input and the ground identity.

**Definition 1.9 (Finite scalar Laurent entries).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentCoefficients`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finitely supported integer coefficient function collects the actual Corr and normal-mode terms at their literal shifted exponents.

**Theorem 1.10 (Actual full field equals finite scalar entries times ground identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_eq_laurent_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_eq_laurent_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every integer exponent, source occupation, repeated input and output occupation, the actual projected correctedField coefficient is exactly the finite scalar Laurent coefficient multiplied by the arbitrary ground vector.

**Definition 1.11 (Finite evaluation at a nonzero parameter).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evaluation parameter is a complex unit. Only the finite scalar coefficient function is evaluated, never an arbitrary Hahn series.

**Theorem 1.12 (Finite evaluation retains the ground identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_ground_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_ground_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite scalar evaluation times any ground vector equals the finite Laurent-weighted sum of the actual projected correctedField coefficients.

**Theorem 1.13 (Evaluation of the unique actual energy coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_at_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_at_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every repeated occupation and arbitrary ground vector, the finite Laurent evaluation equals T to the forced exponent times the actual corrected coefficient at that exponent. All other entries vanish by the native energy covariance.

**Definition 1.14 (Raw mixed blocks in normal order).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each negative mode uses the raw source-output Laurent coefficient as multiplication; each nonnegative mode uses the raw source-input coefficients as Gram-weighted derivatives. Every annihilation acts before the creation multiplications.

**Theorem 1.15 (Actual Laurent entry consumes both raw mixed blocks).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_raw_normal_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_raw_normal_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full actual finite Laurent entry equals the finite Corr shift and monomial expansion of these raw normal-mode operators. The full Gaussian identity consumes this finite raw expansion.

**Theorem 1.16 (Projected normal-polynomial support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.normalPolynomial_projected_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.normalPolynomial_projected_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native output coefficient vanishes outside the common input/output frequency box; the normal-mode support proof consumes the creation and annihilation support arguments.

**Definition 1.17 (Literal raw mode operator).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Negative modes multiply by the raw source-output coefficient and nonnegative modes apply the Gram-weighted source-input derivative.

**Theorem 1.18 (Raw mode operator identifies the native current).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual current at each mode, weighted by its Laurent power and jet factor, is the literal raw mode operator. The coefficient module consumes this equality in the normal-ordering proofs.

**Theorem 1.19 (Raw normal term identifies native normal action).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite raw normal-mode term is the Laurent-weighted creation polynomial times the native right polynomial. This equality transfers the projected frequency support to the raw normal readout.

**Definition 1.20 (Evaluation of the original correction variables).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionEvaluation`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction variable evaluates to T to minus two and oscillator variables remain the original variables.

**Definition 1.21 (Evaluated original correction lift).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native correction lift at zero charge is composed with correction evaluation, retaining the literal Corr construction.

**Theorem 1.22 (Evaluated correction as a finite shift sum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_shift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_shift_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the original correction lift gives the finite sum of T to minus twice the shift times each actual Corr coefficient.

**Theorem 1.23 (Insertion in the evaluated correction lift).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_X_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_X_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting a source variable into the original correction lift gives its unpaired multiplication term and the raw source-source contractions against all source partial derivatives. This is consumed by actual source insertion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_X_mul`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionAt_shift_sum`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.correctionEvaluation`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_eq_laurent_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_finite_projected_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_frequency_projected_mode_sum`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_native_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_output_energy_selection`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralCoefficient_projected_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentCoefficients`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_at_energy`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_ground_identity`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeNeutralLaurentEntry_raw_normal_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeOutputProjection`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.nativeRawNormalTerm_eq`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.neutralSource`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.normalPolynomial_projected_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegModeExpansion.rawModeOperator_eq`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance](ActualEnergyCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian](../TwistedGround/OriginalCorrectionGaussian.md)
