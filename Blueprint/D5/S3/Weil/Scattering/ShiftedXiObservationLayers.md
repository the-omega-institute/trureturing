# Shifted Xi Observation Layers

## Abstract

Opposite shifted-xi observations are sharp reflections linked by the frozen scattering quotient.

**Definition 1.1 (Positive shifted-xi observation).**

Lean statement: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservation`

*Formalization.* `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive layer evaluates the frozen xi reading at one half plus the real observation depth minus i times the spectral coordinate.

**Definition 1.2 (Sharp shifted-xi observation).**

Lean statement: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservationSharp`

*Formalization.* `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservationSharp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sharp reflection conjugates the value of the positive observation at the conjugate spectral coordinate.

**Theorem 1.3 (The two shifted-xi observation layers).**

$$\forall \omega \in \mathbb{R}, \forall z \in \mathbb{C},\\{}(\omega > 0 \land \operatorname{shiftedXiObservation}(\omega, z) \neq 0) \Rightarrow\\{}\operatorname{shiftedXiObservationSharp}(\omega, z) = \operatorname{xiReading}(\frac{1}{2} - \omega - i \cdot z) \land\\{}\operatorname{shiftedXiScattering}(\omega, z) = \frac{\operatorname{shiftedXiObservationSharp}(\omega, z)}{\operatorname{shiftedXiObservation}(\omega, z)} \land\\{}\operatorname{shiftedXiScattering}(\omega, z) \cdot \operatorname{shiftedXiObservation}(\omega, z) = \operatorname{shiftedXiObservationSharp}(\omega, z).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shifted_xi_observation_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive real depth, xi reflection identifies the sharp positive observation with the negative shifted layer. The existing shifted-xi scattering reading is exactly the quotient of these two layers.

The positive layer is assumed nonzero before quotient multiplication is cancelled. This excludes Lean's totalized division-by-zero value.

This is the self-contained algebraic observation-layer closure of the source. The Suzuki meromorphic-inner criterion and the associated de Branges claims require external analytic definitions and results and are not asserted here.

**Theorem 1.4 (A regular observation at depth one half).**

$$0 < \frac{1}{2} \land\\{}\operatorname{shiftedXiObservation}(\frac{1}{2}, 0) \neq 0 \land\\{}\operatorname{shiftedXiObservationSharp}(\frac{1}{2}, 0) = \operatorname{xiReading}(\frac{1}{2} - \frac{1}{2} - i \cdot 0) \land\\{}\operatorname{shiftedXiScattering}(\frac{1}{2}, 0) = \frac{\operatorname{shiftedXiObservationSharp}(\frac{1}{2}, 0)}{\operatorname{shiftedXiObservation}(\frac{1}{2}, 0)} \land\\{}\operatorname{shiftedXiScattering}(\frac{1}{2}, 0) \cdot \operatorname{shiftedXiObservation}(\frac{1}{2}, 0) = \operatorname{shiftedXiObservationSharp}(\frac{1}{2}, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.positive_depth_observation_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Depth one half and spectral coordinate zero give a concrete positive-depth instance whose positive layer is nonzero and satisfies all three laws.

**Theorem 1.5 (A zero denominator breaks transition recovery).**

$$numerator := 1, denominator := 0,\\{}denominator = 0 \land \frac{numerator}{denominator} \cdot denominator \neq numerator.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.zero_denominator_breaks_transition_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete numerator one and denominator zero show that quotient multiplication cannot recover a nonzero numerator without the regularity premise.

## References

- Truth anchor: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.positive_depth_observation_witness`
- Truth anchor: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservation`
- Truth anchor: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shiftedXiObservationSharp`
- Truth anchor: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.shifted_xi_observation_layers`
- Truth anchor: `D5/S3/Weil/Scattering/ShiftedXiObservationLayers.zero_denominator_breaks_transition_recovery`
- Dependency: [D5/S3/Weil/Scattering/FiniteScatteringCascade](FiniteScatteringCascade.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../../Zeros/Symmetry/ZetaConjugationCovariance.md)
