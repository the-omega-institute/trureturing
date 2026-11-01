# Native finite neutral three-leg coefficient identity

## Abstract

The actual corrected neutral field has a finite three-leg coefficient expansion with the literal Corr correction, repeated occupations, finite normal modes, and the native Gaussian correction readout.

The source is the actual correctedField on the full ActualTensor carrier. For an arbitrary finite repeated oscillator occupation d, coefficient extraction first exposes the literal Corr support and then expands each actual polynomial into the actual charged zero normal word. The pointwise mode sum remains a finsum on the input tensor, so no endomorphism-valued infinite sum is introduced.

The zero-charge seed is the existing identity field. Its flat coefficient is therefore the genuine creation-left, annihilation-right normal product with the integer exponent selector. The correction is the supplied finite Corr, whose repeated labelled occurrences retain all diagonal and off-diagonal matching multiplicities. The source-vacuum linear-form readout is the actual Corr evaluation and gives the factorial Gaussian coefficient for every finite family.

For a mode tuple, negative entries record output frequencies -k-1 and nonnegative entries record input frequencies k. The frequency projection is the finite set {-k-1 | k is in the output support} union {k | k is in the input support}; the Gram matrix only mixes colours at a fixed frequency. The native mode box theorem reduces the actual pointwise finsum to this finite product once the literal support condition is supplied.

The exponent theorem is proved before any scalar evaluation. Corr bidegree supplies shift plus residual source weight equals the original source weight, the flat selector supplies the normal displacement, and the signed mode balance gives e = 2(E_T(output)-E_T(input)-E_S(source)), expressed in Lean with doubled twisted energies. Only after this finite regrouping may a nonzero T be substituted in the resulting Laurent monomial.

The matching argument is the labelled-position Wick/Isserlis expansion: each new insertion either leaves its position unmatched or pairs it with one earlier unmatched position, and the pair derivation vanishes on an already formed pair. This is the finite algebraic bridge for arbitrary repeated occupations; it makes no analytic completion, whitening, damping, unitarity, sewing, string-theory, or AdS/CFT claim.

After the finite projection and exponent regrouping, the raw three-leg generating kernel is the exponential of the four actual finite bilinear pieces: one half of the source-source covariance p_st G_ij T^(-2s-2t), the source-output creation symbol J_s(-k-1) T^(2k-2s+1), the source-input annihilation symbol omega_k G_ij J_s(k) T^(-2k-2s-1), and the identity propagation term eta_jk xi_jk. Source coefficients are divided by d!, input coefficients by h!, while output uses ordinary monomial coefficients; the diagonal source pair contributes p_ss G_ii with no extra factor two.

**Definition 1.1 (Actual neutral source).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source is the full carrier element with the requested arbitrary finite oscillator occupation.

**Theorem 1.2 (Coefficient exposes correctedPolynomial).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual corrected field reduces at charge zero to the literal correctedPolynomial.

**Theorem 1.3 (Finite actual Corr and normal-word expansion).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality keeps Corr support, polynomial support, actual chargedField normal words, repeated occurrences, and pointwise flatTerm mode sums.

**Theorem 1.4 (Actual Corr Gaussian readout).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCorrection_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCorrection_gaussian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing actual Corr source-vacuum readout is the factorial Gaussian coefficient for arbitrary finite linear forms.

**Theorem 1.5 (Signed native mode energy balance).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.native_mode_energy_balance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.native_mode_energy_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative output and nonnegative input occupations of every actual mode tuple satisfy the signed doubled-frequency balance.

**Theorem 1.6 (Native exponent regrouping).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_exponent_regrouping`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_exponent_regrouping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Corr bidegree, the actual flat selector, and the signed mode balance prove the common finite Laurent exponent before evaluation.

**Theorem 1.7 (Finite projected actual mode sum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_mode_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_mode_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pointwise finsum equals the finite native mode box under the literal support condition.

**Theorem 1.8 (Output/input frequency projected mode sum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection is instantiated with the native frequency set {-k-1 from output} union {k from input}; no color support assumption is used.

**Definition 1.9 (Explicit four-piece raw kernel).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source-source, source-output, source-input, and identity-propagation terms are defined directly from pairScalar, jetScalar, frequency, G, and the Laurent powers of T.

**Theorem 1.10 (Source-source kernel is the native covariance).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeSourceSourceKernel_eq_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeSourceSourceKernel_eq_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At T nonzero, the explicit source-source Laurent power is exactly the existing Corr covariance evaluated at T^-2.

**Theorem 1.11 (Raw kernel component equality).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel_components`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four finite bilinear pieces are exposed as an equality, with the source-source diagonal carrying its one-half coefficient.

**Theorem 1.12 (Finite repeated-occupation native Wick identity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralFiniteWickIdentity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralFiniteWickIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite labelled family and arbitrary occupation, the actual sourceVacuum Corr readout equals the exact factorial Gaussian coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_exponent_regrouping`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_frequency_projected_mode_sum`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_native_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_projected_mode_sum`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCoefficient_source`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralCorrection_gaussian`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralFiniteWickIdentity`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeNeutralRawKernel_components`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.nativeSourceSourceKernel_eq_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.native_mode_energy_balance`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient.neutralSource`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance](ActualEnergyCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalCorrectionGaussian](../TwistedGround/OriginalCorrectionGaussian.md)
