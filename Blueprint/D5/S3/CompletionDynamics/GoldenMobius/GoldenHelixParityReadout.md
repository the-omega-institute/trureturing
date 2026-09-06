# Golden Helix Parity Readout

## Abstract

Golden helix orientation is flipped at odd depth and restored at even depth while the lifted state continues to advance.

**Theorem 1.1 (Odd helix depth breaks the orientation readout).**

$$\operatorname{Odd}(n) \Rightarrow \operatorname{orientation}(\operatorname{goldenHelixStep}^n(state)) \neq \operatorname{orientation}(state).$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.golden_helix_odd_orientation_breaking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every odd iterate of the golden helix lies on the opposite Boolean orientation sheet.

The result concerns the orientation observer and makes no universal claim about parity in arbitrary projection towers.

**Theorem 1.2 (Two steps complete orientation without returning the state).**

$$(\operatorname{orientation}(\operatorname{goldenHelixStep}^2(state)) = \operatorname{orientation}(state)) \land\\\operatorname{goldenHelixStep}^2(state) \neq state.$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.golden_helix_two_step_orientation_complete_state_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two helix steps restore the orientation coordinate because the orientation flip is involutive.

The completion is observer-relative: the level coordinate has advanced twice, so the complete helix state is distinct.

## References

- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.golden_helix_odd_orientation_breaking`
- Truth anchor: `D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.golden_helix_two_step_orientation_complete_state_distinct`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix](GoldenScaleHelix.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion](../../ObserverMemory/Refinement/InvolutiveReadoutCompletion.md)
