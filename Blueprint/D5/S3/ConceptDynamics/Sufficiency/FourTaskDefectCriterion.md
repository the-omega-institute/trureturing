# Four-Task Defect Criterion

## Abstract

A finite four-task defect vanishes exactly when all four named tasks descend.

**Theorem 1.1 (Zero defect is equivalent to four task-relative conditions).**

$$\begin{gathered}\forall X, B, Y, C, Z: \operatorname{Type},\\{}Finite\left(X\right), q: X \to B, T: X \to Z,\\{}qY: Y \to C, F: X \to Y,\\{}A: X \to Prop, a: X,\\{}fourTaskDefect\left(q, T, qY, F, A, a\right) = 0 \Leftrightarrow \left(\left(\exists Tbar \in B \to Z,\; T = Tbar \circ q\right) \land \left(\left(\exists Fbar \in B \to C,\; qY \circ F = Fbar \circ q\right) \land \left(\left(\exists Abar \in B \to Prop,\; \forall x \in X,\; A\left(x\right) \Leftrightarrow Abar\left(q\left(x\right)\right)\right) \land \left(\forall x \in X,\; q\left(x\right) = q\left(a\right) \Rightarrow x = a\right)\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/FourTaskDefectCriterion.four_task_defect_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numeric defect is the sum of four finite cardinalities: target disagreements, transported-flow disagreements, admissibility disagreements, and extra states in the anchor fiber.

A zero sum makes every defect set empty and yields the three descended maps plus a singleton anchor fiber. Conversely, the four conditions exclude every listed defect.

This is completeness only for the specified target, flow, admissibility predicate, and anchor. It makes no absolute ontological completeness claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/FourTaskDefectCriterion.four_task_defect_zero_iff`
