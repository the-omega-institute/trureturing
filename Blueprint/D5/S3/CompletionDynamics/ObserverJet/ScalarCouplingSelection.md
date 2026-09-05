# Scalar Coupling Selection

## Abstract

Rotation and reflection invariance force every second-order scalar regulator mode to be radial.

**Theorem 1.1 (Invariant second-order modes are radial).**

$$\forall linearX \in \mathbb{R}, linearY \in \mathbb{R}, quadraticXX \in \mathbb{R}, quadraticXY \in \mathbb{R}, quadraticYY \in \mathbb{R},\; \left(\left(\forall theta \in \mathbb{R}, u \in RegulatorMode,\; \operatorname{secondOrderMode}(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, \operatorname{regulatorRotation}(theta, u)) = \operatorname{secondOrderMode}(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, u)\right) \land \left(\forall u \in RegulatorMode,\; \operatorname{secondOrderMode}(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, \operatorname{regulatorReflection}(u)) = \operatorname{secondOrderMode}(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, u)\right)\right) \Rightarrow \left(\forall u \in RegulatorMode,\; \operatorname{secondOrderMode}(linearX, linearY, quadraticXX, quadraticXY, quadraticYY, u) = quadraticXX \times \left\lVert u \right\rVert^{2}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection.invariant_second_order_mode_is_radial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed secondOrderMode is the general real degree-at-most-two polynomial in a two-coordinate regulator mode, with the constant term kept outside the mode. Invariance under every standard plane rotation and the generating reflection removes both linear coefficients and the mixed quadratic coefficient, and equates the two diagonal quadratic coefficients.

**Theorem 1.2 (Completed scalar coupling begins quadratically).**

$$\forall F0 \in \mathbb{R}, linearX \in \operatorname{PNat} \to \mathbb{R}, linearY \in \operatorname{PNat} \to \mathbb{R}, quadraticXX \in \operatorname{PNat} \to \mathbb{R}, quadraticXY \in \operatorname{PNat} \to \mathbb{R}, quadraticYY \in \operatorname{PNat} \to \mathbb{R}, higherInvariant \in \operatorname{PNat} \to \left(RegulatorMode \to \mathbb{R}\right), delta \in \mathbb{R}, gamma \in \mathbb{R},\; \left(\left(\forall n \in \operatorname{PNat}, theta \in \mathbb{R}, u \in RegulatorMode,\; \operatorname{secondOrderMode}(linearX\left(n\right), linearY\left(n\right), quadraticXX\left(n\right), quadraticXY\left(n\right), quadraticYY\left(n\right), \operatorname{regulatorRotation}(theta, u)) + higherInvariant\left(n\right)\left(\operatorname{regulatorRotation}(theta, u)\right) = \operatorname{secondOrderMode}(linearX\left(n\right), linearY\left(n\right), quadraticXX\left(n\right), quadraticXY\left(n\right), quadraticYY\left(n\right), u) + higherInvariant\left(n\right)\left(u\right)\right) \land \left(\left(\forall n \in \operatorname{PNat}, theta \in \mathbb{R}, u \in RegulatorMode,\; higherInvariant\left(n\right)\left(\operatorname{regulatorRotation}(theta, u)\right) = higherInvariant\left(n\right)\left(u\right)\right) \land \left(\left(\forall n \in \operatorname{PNat}, u \in RegulatorMode,\; \operatorname{secondOrderMode}(linearX\left(n\right), linearY\left(n\right), quadraticXX\left(n\right), quadraticXY\left(n\right), quadraticYY\left(n\right), \operatorname{regulatorReflection}(u)) + higherInvariant\left(n\right)\left(\operatorname{regulatorReflection}(u)\right) = \operatorname{secondOrderMode}(linearX\left(n\right), linearY\left(n\right), quadraticXX\left(n\right), quadraticXY\left(n\right), quadraticYY\left(n\right), u) + higherInvariant\left(n\right)\left(u\right)\right) \land \left(\left(\forall n \in \operatorname{PNat}, u \in RegulatorMode,\; higherInvariant\left(n\right)\left(\operatorname{regulatorReflection}(u)\right) = higherInvariant\left(n\right)\left(u\right)\right) \land delta \ne 0\right)\right)\right)\right) \Rightarrow \left(\exists kappa \in \operatorname{PNat} \to \mathbb{R},\; \left(\forall modes \in \operatorname{PNat} \to RegulatorMode,\; F0 + \sigma_{n: \operatorname{PNat}} {\operatorname{secondOrderMode}(linearX\left(n\right), linearY\left(n\right), quadraticXX\left(n\right), quadraticXY\left(n\right), quadraticYY\left(n\right), modes\left(n\right)) + higherInvariant\left(n\right)\left(modes\left(n\right)\right)} = F0 + \sigma_{n: \operatorname{PNat}} {kappa\left(n\right) \times \left\lVert modes\left(n\right) \right\rVert^{2} + higherInvariant\left(n\right)\left(modes\left(n\right)\right)}\right) \land \operatorname{let} right: \mathbb{C} := \frac{1}{2} + delta + i \times gamma; \operatorname{let} left: \mathbb{C} := \frac{1}{2} -delta + i \times gamma;\\{}\operatorname{let} center: \mathbb{C} := \frac{1}{2} + i \times gamma; \frac{right + left}{2} = center \land \left(\frac{delta + {-delta}}{2} = 0 \land \left(\frac{delta^{2} + {-delta}^{2}}{2} = delta^{2} \land 0 < \frac{delta^{2} + {-delta}^{2}}{2}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection.scalar_coupling_selection_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive-indexed family of second-order regulator modes and higher invariant remainders, the completed and higher terms are assumed invariant under all standard rotations and under the generating reflection. The modal contribution then reduces termwise to kappa(n) times the squared regulator norm, with the arbitrary higher invariant retained.

For every nonzero real displacement delta and every real height gamma, the explicitly displayed reflected complex pair has center one-half plus i gamma, zero signed first moment, second moment delta squared, and strictly positive second moment.

## References

- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection.invariant_second_order_mode_is_radial`
- Truth anchor: `D5/S3/CompletionDynamics/ObserverJet/ScalarCouplingSelection.scalar_coupling_selection_rule`
- Dependency: [D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation](PairedOddJetCancellation.md)
