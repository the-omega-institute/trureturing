# Soundness, Liveness, and Shape-Only Tests

## Abstract

A concrete judge model separates soundness, liveness, and shape-only tests.

**Theorem 1.1 (Soundness and liveness are independent of shape-only tests).**

$$\begin{gathered}sound((true, false)) \land \neg live((true, false)) \land live((false, true)) \land \neg sound((false, true)) \land\\{}shape((true, false)) = shape((true, true)) \land \neg(live((true, false)) \Leftrightarrow live((true, true))) \land\\{}\neg{\forall j: Judge, sound(j) \Rightarrow live(j)} \land \neg{\forall j: Judge, live(j) \Rightarrow sound(j)} \land\\{}{\forall T: Judge \to Prop, {\forall j1, j2: Judge, shape(j1) = shape(j2) \Rightarrow (T(j1) \Leftrightarrow T(j2))} \Rightarrow \neg{\forall j: Judge, (T(j) \Leftrightarrow live(j))}} \land \operatorname{GeneralSameShapeLivenessSplitLaw}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/SoundnessLivenessShapeOnlyIndependence.soundness_liveness_independent_of_shape_only_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Judge is Bool x Bool. Soundness reads the first coordinate, liveness reads the second, and shape is the first coordinate itself.

The judges (true,false) and (false,true) witness both failed implications. The judges (true,false) and (true,true) have equal shape but opposite liveness.

Consequently every test family constant on equal-shape fibers fails to characterize liveness. The declaration also includes the general version for every model with a same-shape liveness split.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/SoundnessLivenessShapeOnlyIndependence.soundness_liveness_independent_of_shape_only_tests`
