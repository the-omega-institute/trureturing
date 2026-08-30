# Finite Error-Class Half-Life

## Abstract

Finite same-class capture histories have an executable least stable gate suffix, while the ink-not-dry recurrence remains unconverged.

**Theorem 1.1 (Half-life is computable and the ink-not-dry trace is nontrivial).**

$$\begin{aligned}\forall C, I: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(C\right)],\\tau: \operatorname{OperationalTrajectory}\left(C, I\right),\\c: C, n: Nat,\\(\operatorname{gateHalfLife}\left(tau, c\right) = \operatorname{some}\left(n\right) \iff (\operatorname{StableAtGate}\left(\operatorname{classMaturity}\left(tau, c\right), n\right) \land \forall m: Nat, m < n \Rightarrow \neg \operatorname{StableAtGate}\left(\operatorname{classMaturity}\left(tau, c\right), m\right))) \land\\{}(\operatorname{classMaturity}\left(inkNotDryTrajectory, unit\right) = [wall, wall, wall]) \land\\{}\operatorname{gateHalfLife}\left(inkNotDryTrajectory, unit\right) = none.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/HalfLifeWellDefined.half_life_computable_and_ink_not_dry_nontrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen operational trajectory supplies a finite event list and its same-class capture history. The executable half-life searches the finite list of suffixes and rejects the empty suffix.

A returned index is characterized independently: its nonempty suffix is entirely gate-or-higher, and every earlier suffix fails that condition. Thus the value is the first stable capture index, not merely any successful suffix.

The ink-not-dry witness contains three occurrences of one error class, all captured at wall level. Its compiled maturity list is exactly three walls and its executable half-life is none.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/HalfLifeWellDefined.half_life_computable_and_ink_not_dry_nontrivial`
- Dependency: [D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration](InstitutionalMappingAndCaptureFiltration.md)
