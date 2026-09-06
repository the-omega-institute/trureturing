# Localized Stieltjes-to-Weil Quadratic Interface

## Abstract

An explicit exact-readout interface isolates the analytic obligation needed to turn an active localized Stieltjes orbit into a negative Weil quadratic test.

**Definition 1.1 (Exact localized Stieltjes-Weil transport).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.ExactLocalizedStieltjesWeilTransport`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.ExactLocalizedStieltjesWeilTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structure contains an orbit-to-test realization, a real target quadratic functional, and an exact equality with each localized atomic weight.

**Theorem 1.2 (An active orbit produces a negative Weil value).**

$$\operatorname{Active}(a) \land 0 < m_{a} \implies \operatorname{Q}(f_{a}) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.active_orbit_gives_negative_weil_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof substitutes the exact readout identity and applies the positive-mass barcode sign theorem. All analytic realization work is confined to the transport structure.

**Theorem 1.3 (An active orbit produces some negative Weil test).**

$$(\exists a, \operatorname{Active}(a)) \implies (\exists f, \operatorname{Q}(f) < 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.exists_negative_weil_test_of_active_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This packages the selected orbit's realized test as an existential negative direction in the target quadratic domain.

**Theorem 1.4 (A nonnegative Weil form rules out active orbits).**

$$(\forall f, 0 \leq \operatorname{Q}(f)) \implies \forall a, \neg\operatorname{Active}(a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.no_active_orbit_of_nonnegative_weil_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under an exact positive-mass transport, target nonnegativity contradicts the negative value forced by any active orbit.

## References

- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.ExactLocalizedStieltjesWeilTransport`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.active_orbit_gives_negative_weil_value`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.exists_negative_weil_test_of_active_orbit`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesToWeilQuadraticInterface.no_active_orbit_of_nonnegative_weil_form`
- Dependency: [D5/S3/Weil/Pick/ObserverSignedSupportBarcode](ObserverSignedSupportBarcode.md)
