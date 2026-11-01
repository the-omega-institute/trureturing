# Actual finite neutral-field coefficient bridge

## Abstract

Actual output-projected finite neutral corrected-field coefficients and their raw normal-mode Laurent realization; the full Gaussian coefficient identity remains open.

This unit proves output-projected finite mode restriction and finite scalar Laurent realization for the actual neutral correctedField, on the original tensor carrier. Source, input and output occupations may have arbitrary repetitions. The Gram matrix is the original raw matrix, the only invertibility assumption is the native hu, and rank zero is included.

The common finite mode set is {-k-1 : k is an output frequency} union {k : k is an input frequency}. Positive currents mix colours only at a fixed frequency. A negative mode outside the output frequency support can create a nonzero full vector, but its specified output coefficient vanishes. The support theorem therefore extracts that coefficient before restricting the sum.

The flat normal recursion is factored into creation multiplication on the left and Gram-weighted annihilation on the right. The proof uses the existing same-sign Heisenberg commutation law, the native monomial derivative and actual pointwise finite-support theorem. Ground vectors are carried by identity; no scalar ground vacuum is chosen.

The existing energy covariance supplies e = 2(E_T(output)-E_T(input)-E_S(source)), in doubled integral twisted-energy coordinates. The actual coefficients are represented by a finitely supported scalar Laurent polynomial. Evaluation is allowed only at a complex unit T and is a finite sum.

The raw source-output and source-input blocks are consumed in the actual finite evaluated normal-operator expansion. Source insertion in the actual entry separates the unpaired normal readout from a sum d(b) SS(a,b) times the entry with one b removed. The SS block is therefore also connected to the actual field, with repeated-source multiplicities and diagonal entry p rather than 2p. The remaining bridge identifies the unpaired branch and identity propagation with the factorial coefficient of exp(SS/2 + SO + SI + IO). The actual entry divided by source d! and input h!, with ordinary output coefficient, has not yet been identified with the full block GaussianCoefficient.

The intended remaining combinatorics is classical labelled-position Wick/Isserlis and the exponential formula: equal labels are distinct positions, so diagonal pairing counts have factors 2^m m! and off-diagonal counts m!. Wick (1950, Physical Review 80, 268) and Isserlis (1918, Biometrika 12, 134-139) supply the classical provenance; OriginalCorrectionGaussian supplies the repository actual Corr source-vacuum theorem. No new global novelty, positivity, unitarity, analytic completion, sewing, string-theory completion or AdS/CFT result is asserted.

**Definition 1.1 (Actual neutral source).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge-zero carrier element is Finsupp.single 0 (monomial d 1), with arbitrary finite multiplicities.

**Definition 1.2 (Actual full corrected coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The field is correctedField on the existing ActualTensor carrier; no alternative Gaussian field is defined.

**Theorem 1.3 (Actual Corr and pointwise normal expansion).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Corr support and residual polynomial support precede the native pointwise flatTerm finsum.

**Definition 1.4 (Full ground-valued output coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeOutputProjection`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeOutputProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial coefficient map is tensored with identity and composed with the canonical scalar tensor identification. Its result is the entire ground vector.

**Theorem 1.5 (Proved projected frequency support).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word, exponent, repeated input and output occupation, ground vector and mode tuple, a nonzero projected flatTerm implies membership of every mode in the common output-negative/input-positive frequency set. There is no vector-support hypothesis.

**Theorem 1.6 (Common finite projected mode sum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each exponent and arbitrary ground vector, the output coefficient of the actual normal word equals the sum over the finite Cartesian mode box built from the output and input frequency supports.

**Theorem 1.7 (Actual corrected output exponent selection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_output_energy_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_output_energy_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full ground-valued corrected entry vanishes unless e equals oddWeight(output) minus oddWeight(input) minus twice the source weight. The proof consumes existing full-field energy covariance.

**Theorem 1.8 (Finite actual corrected entry).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_finite_projected_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_finite_projected_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact output projection is a finite Corr shift, residual monomial and normal-mode sum. Its integer selector is retained; normal creation and annihilation act on the original polynomial input and the ground identity.

**Definition 1.9 (Finite scalar Laurent entries).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentCoefficients`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finitely supported integer coefficient function collects the actual Corr and normal-mode terms at their literal shifted exponents.

**Theorem 1.10 (Actual full field equals finite scalar entries times ground identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_eq_laurent_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_eq_laurent_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every integer exponent, source occupation, repeated input and output occupation, the actual projected correctedField coefficient is exactly the finite scalar Laurent coefficient multiplied by the arbitrary ground vector.

**Definition 1.11 (Finite evaluation at a nonzero parameter).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evaluation parameter is a complex unit. Only the finite scalar coefficient function is evaluated, never an arbitrary Hahn series.

**Theorem 1.12 (Finite evaluation retains the ground identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_ground_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_ground_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite scalar evaluation times any ground vector equals the finite Laurent-weighted sum of the actual projected correctedField coefficients.

**Theorem 1.13 (Evaluation of the unique actual energy coefficient).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_at_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_at_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every repeated occupation and arbitrary ground vector, the finite Laurent evaluation equals T to the forced exponent times the actual corrected coefficient at that exponent. All other entries vanish by the native energy covariance.

**Definition 1.14 (Raw mixed blocks in normal order).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeRawNormalTerm`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeRawNormalTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each negative mode uses the raw source-output Laurent coefficient as multiplication; each nonnegative mode uses the raw source-input coefficients as Gram-weighted derivatives. Every annihilation acts before the creation multiplications.

**Theorem 1.15 (Actual Laurent entry consumes both raw mixed blocks).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_raw_normal_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_raw_normal_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full actual finite Laurent entry equals the finite Corr shift and monomial expansion of these raw normal-mode operators. This is not yet the exponential coefficient of the full three-leg block matrix.

**Definition 1.16 (Linear readout of the actual finite normal action).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNormalReadout`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNormalReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial basis extends the finite raw normal-mode coefficient action linearly to source polynomials, using the proved input/output frequency box.

**Theorem 1.17 (Actual corrected coefficient source insertion with SS contractions).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary repeated occupations and any ground vector, T to the forced exponent times the actual corrected-field coefficient after inserting source a equals the unpaired normal readout times that vector plus the sum over b of d(b) SS(a,b) times the native entry with one b removed, acting by ground identity. The proof evaluates the actual correction lift at T to minus two and reuses its source-partial formula. The scalar recurrence is a consumed helper. No Gaussian coefficient equality is assumed. Identification of the unpaired readout with the full three-leg Gaussian recurrence remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_eq_laurent_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_finite_projected_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_output_energy_selection`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_support`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source_insertion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentCoefficients`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_at_energy`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_ground_identity`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralLaurentEntry_raw_normal_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNormalReadout`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeOutputProjection`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeRawNormalTerm`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance](ActualEnergyCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian](../TwistedGround/OriginalCorrectionGaussian.md)
