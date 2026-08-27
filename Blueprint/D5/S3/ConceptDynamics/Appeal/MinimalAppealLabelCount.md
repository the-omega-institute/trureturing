# Minimal Appeal Label Count

## Abstract

Maximum target diversity in a record fiber is the exact appeal label count.

**Theorem 1.1 (Fiber diversity gives the exact number of appeal labels).**

$$\begin{gathered}\forall X, B, Y: Type,\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(B)],\\{}r: X \to B, t: X \to Y,\\{}(\exists ell_{exact}: X \to \operatorname{Fin}(\operatorname{worstFiberDiversity}(r, t)), \operatorname{AppealDetermines}(r, t, ell_{exact})) \land \\{}(\forall m: \mathbb{N}, ell_{candidate}: X \to \operatorname{Fin}(m),\\{}\operatorname{AppealDetermines}(r, t, ell_{candidate}) \Rightarrow \operatorname{worstFiberDiversity}(r, t) \leq m).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount.minimal_appeal_label_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be the largest number of distinct target outcomes realized in any one record fiber. The state and record carriers are finite, while the target carrier itself need not be finite.

There is a label with d possible values that makes the target exact once the original record is fixed. It is obtained by indexing the realized target outcomes inside each fiber, and the same labels may be reused in different fibers.

Conversely, any exact label with m possible values is injective on one representative of each realized target outcome in every fiber. Each fiber therefore has at most m target outcomes, so d is at most m. Together the two directions make d the exact minimum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount.minimal_appeal_label_count`
- Dependency: [D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification](../Coding/FiberBinaryIdentification.md)
