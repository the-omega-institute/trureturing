# Original Matter Hermitian Form and Adjoint Modes

## Abstract

The literal frame-free original matter Hermitian supplier on the existing charge and oscillator carrier.

The carrier, source Wick pairing, coefficient conjugation kappa, source reflection theta and original integer currents are the existing definitions. Hm is the literal sourcePairing D (theta D (kappaCarrier x)) y, with no transverse frame, positive metric or desired-result premise. The Gram remains the original indefinite symmetric integral Gram.

The current adjoint is proved for every integer mode m, including zero and the signs plus or minus one. normalSummand_adjoint retains the literal k<0 and k>=0 branches and the k=0 reversal. Hm_sugawaraMode uses both inverse hypotheses for H * gramComplex D and gramComplex D * H, and derives the coefficient conjugation and transpose identities.

The complete public inventory has 38 declarations: 35 theorems, including all 12 inline simp helpers, and 3 definitions. The compiled module has 59 bindings, including 10 private declarations and 11 compiler-generated bindings. Each public declaration has a Describe anchor here; its exact statement identity, full compiled telescope, type hash and standard axiom binding are accounted for in https://github.com/the-omega-institute/trureturing/issues/25777. This source currently has no Reg registration mirror: source selection and reconstruction, actual bridge, readout and law, family variation and sensitivity, observational dependence and registration remain unfinished. Empty inventory, records and registered fields do not establish declared_validated. The complete Monster/VOA/CFT/anomaly/fusion/BRST/string/AdS objective remains unfinished.

**Definition 1.1 (Coefficient conjugation on oscillators).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps polynomial coefficients by complex conjugation and fixes the original oscillator variables.

**Definition 1.2 (Coefficient conjugation on the carrier).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applies kappaOsc on each existing finite-charge oscillator component.

**Theorem 1.3 (Conjugation of oscillator constants).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_C`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient conjugation sends the oscillator constant C c to C (conj c).

**Theorem 1.4 (Conjugation fixes oscillator variables).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient conjugation fixes every original oscillator variable X x.

**Theorem 1.5 (Conjugation preserves oscillator addition).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient conjugation of p + q equals kappaOsc p + kappaOsc q.

**Theorem 1.6 (Conjugation preserves oscillator multiplication).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient conjugation of p * q equals kappaOsc p * kappaOsc q.

**Theorem 1.7 (Conjugate scalar action on oscillators).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating c times an oscillator conjugates c and applies kappaOsc to the oscillator.

**Theorem 1.8 (Conjugation of every oscillator coefficient).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient of kappaOsc p is the complex conjugate of the corresponding coefficient of p.

**Theorem 1.9 (Conjugation preserves the zero carrier).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient conjugation sends the zero original carrier state to zero.

**Theorem 1.10 (Conjugation preserves carrier addition).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Carrier coefficient conjugation preserves the sum of any two original carrier states.

**Theorem 1.11 (Conjugate scalar action on the carrier).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_smul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Carrier coefficient conjugation conjugates a complex scalar multiplying any original carrier state.

**Theorem 1.12 (Conjugation of a single charge component).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation preserves every charge label, including zero, and conjugates its oscillator component.

**Theorem 1.13 (Conjugation commutes with pderiv).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_pderiv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_pderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original coefficient conjugation commutes with every oscillator partial derivative.

**Theorem 1.14 (Conjugation commutes with annihilation).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_annihilate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_annihilate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Gram-weighted annihilation operator is preserved under coefficient conjugation.

**Theorem 1.15 (Conjugation commutes with every polynomial mode).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_neutralPolynomialMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_neutralPolynomialMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative, zero and positive original integer mode branches are preserved by kappaOsc.

**Theorem 1.16 (Conjugation commutes with every carrier mode).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_neutralMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_neutralMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier lift intertwines each original neutral current at every integer frequency.

**Theorem 1.17 (Oscillator conjugation is involutive).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the coefficient conjugation twice returns the original oscillator.

**Theorem 1.18 (Conjugation of the source Wick pairing).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.integerWick_kappa`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.integerWick_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual retuned signed Wick pairing conjugates under kappaOsc in both slots.

**Theorem 1.19 (Conjugation and oscillator reflection).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_sigma`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original sigma reflection commutes with coefficient conjugation.

**Theorem 1.20 (Conjugation and source reflection).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_theta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier coefficient conjugation commutes with the existing source theta.

**Theorem 1.21 (Conjugation of the source pairing).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.sourcePairing_kappa`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.sourcePairing_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite opposite-charge source pairing conjugates under kappaCarrier in both inputs.

**Theorem 1.22 (Inverse Gram conjugation symmetry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.conjugateH_eq_H`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.conjugateH_eq_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse hypotheses, the matrix H is fixed by entrywise complex conjugation.

**Theorem 1.23 (Inverse Gram transpose symmetry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.transposeH_eq_H`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.transposeH_eq_H` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse hypotheses, the matrix H is fixed by transpose using the original symmetric Gram.

**Theorem 1.24 (Carrier conjugation is involutive).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying kappaCarrier twice returns every original carrier state.

**Theorem 1.25 (Source reflection is involutive).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.theta_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.theta_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing source theta squares to the identity on the carrier.

**Definition 1.26 (Literal frame-free Hermitian form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Defines Hm x y as sourcePairing D (theta D (kappaCarrier x)) y on the original carrier.

**Theorem 1.27 (Reflected second-slot form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_alt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_alt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrites Hm by moving the existing source reflection to the second input.

**Theorem 1.28 (Hermitian symmetry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal source form satisfies Hm x y = conj (Hm y x).

**Theorem 1.29 (All-integer current adjoint).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index and every integer m, neutralMode at m in the first slot transposes to neutralMode at -m in the second slot.

**Theorem 1.30 (Composed current adjoint).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode_comp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two original neutral modes transpose with reversed order and negated integer frequencies.

**Theorem 1.31 (Normal summand adjoint).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.normalSummand_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.normalSummand_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal normalSummand branches k<0 and k>=0 transpose to the reversed pair with negated frequencies, including the k=0 reversal.

**Theorem 1.32 (Zero in the first Hermitian slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal Hm form vanishes when its first carrier input is zero.

**Theorem 1.33 (Zero in the second Hermitian slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal Hm form vanishes when its second carrier input is zero.

**Theorem 1.34 (Additivity in the first slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hm is additive in its first carrier input.

**Theorem 1.35 (Additivity in the second slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hm is additive in its second carrier input.

**Theorem 1.36 (Conjugate scalar action in the first slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar in the first slot acts by its complex conjugate.

**Theorem 1.37 (Scalar action in the second slot).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar in the second slot acts directly.

**Theorem 1.38 (All-mode Sugawara adjoint).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_sugawaraMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_sugawaraMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m, the original matrix Sugawara mode at m transposes to the mode at -m under both inverse Gram hypotheses.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_left`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_add_right`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_alt`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_neutralMode_comp`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_left`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_smul_right`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_sugawaraMode`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_left`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.Hm_zero_right`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.conjugateH_eq_H`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.integerWick_kappa`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_add`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_neutralMode`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_single`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_smul`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_theta`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaCarrier_zero`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_C`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_X`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_add`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_annihilate`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_mul`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_neutralPolynomialMode`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_pderiv`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_sigma`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.kappaOsc_smul`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.normalSummand_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.sourcePairing_kappa`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.theta_square`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian.transposeH_eq_H`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](../LatticeSugawaraCurrents.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws](SourcePairingLaws.md)
