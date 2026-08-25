# Target-Conditioned Admission Audit

## Abstract

Target-conditioned admission can erase defects only by deleting states.

**Theorem 1.1 (Restricted closure records deletion and target dependence).**

$$\begin{gathered}(\forall X, B, Y: \operatorname{Type}, [\operatorname{Finite}\left(X\right)],\\{}C: X \to B, T: X \to Y,\\{}\operatorname{Nonempty}\left(\operatorname{Defect}\left(C, T\right)\right) \Rightarrow \exists z: X \times X,\\{}z \in \operatorname{Defect}\left(C, T\right) \land \operatorname{Defect}\left(\operatorname{restrict}\left(C, \operatorname{singleton}\left(\operatorname{fst}\left(z\right)\right)\right), \operatorname{restrict}\left(T, \operatorname{singleton}\left(\operatorname{fst}\left(z\right)\right)\right)\right) = \emptyset \land 0 < \operatorname{ncard}\left(\operatorname{compl}\left(\operatorname{singleton}\left(\operatorname{fst}\left(z\right)\right)\right)\right)) \land\\{}(C_{0}: Bool \to Unit = \operatorname{constant}\left(unit\right),\\{}A: (Bool \to Bool) \to \operatorname{Set}\left(Bool\right), A(U) = \{x \mid U(x) = false\}:\\{}\operatorname{Nonempty}\left(\operatorname{Defect}\left(C_{0}, id\right)\right) \land \operatorname{Defect}\left(\operatorname{restrict}\left(C_{0}, A(id)\right), \operatorname{restrict}\left(id, A(id)\right)\right) = \emptyset \land\\{}A(id) \neq A(not) \land \operatorname{ncard}\left(\operatorname{compl}\left(A(id)\right)\right) = 1) \land\\{}(\forall S: \operatorname{Type}, M: \mathbb{N} \to \operatorname{Set}\left(S\right), e: \mathbb{N} \to S,\\{}(\forall n, e(n) \in M(n)) \Rightarrow\\{}(\forall n, M(n + 1) = \operatorname{diff}\left(M(n), \operatorname{singleton}\left(e(n)\right)\right)) \Rightarrow\\{}\forall n, \neg (e(n) \in M(n + 1)) \land M(n + 1) \subset M(n)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/TargetConditionedAdmissionAudit.target_conditioned_admission_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target collision supplies two distinct states. Restricting both channels to the singleton containing the first state removes all target defects, but the complement has positive cardinality.

In the Boolean contrast, the readout stays constant. Its whole-domain defect is nonempty, its target-conditioned singleton domain has no defect, and changing the target from identity to negation changes the admitted set.

The final clause takes admission domains as independent inputs. When an admitted counterexample is removed at each update, that state is absent at the next stage and the domain shrinks strictly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/TargetConditionedAdmissionAudit.target_conditioned_admission_audit`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
