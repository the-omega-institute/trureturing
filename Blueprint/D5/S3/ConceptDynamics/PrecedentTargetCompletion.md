# Target Completion and Noncircular Distinction

## Abstract

Target completion preserves old cases but need not supply an independent permitted reason.

**Theorem 1.1 (Formal target completion does not supply a noncircular reason).**

$$(\forall X, C, Y: \operatorname{Type},\ A: \operatorname{Set}(X), q: X \to C, J_{0}, J_{1}: X \to Y,\ \operatorname{EqOn}(J_{1}, J_{0}, A) \Rightarrow \exists d: C \times Y \to Y, J_{1} = d \circ \operatorname{conceptJoin}(q, J_{1}) \land \operatorname{EqOn}(d \circ \operatorname{conceptJoin}(q, J_{1}), J_{0}, A)) \land\ (\exists E: \operatorname{Set}(Bool \to Bool),\ (\lambda b: Bool, false) \in E \land (\forall D: Bool \to Bool, D \in E \Rightarrow D(false) = D(true)) \land \operatorname{EqOn}(id, (\lambda b: Bool, false), \{false\}) \land (\exists d: Bool \times Bool \to Bool, id = d \circ \operatorname{conceptJoin}((\lambda b: Bool, false), id) \land \operatorname{EqOn}(d \circ \operatorname{conceptJoin}((\lambda b: Bool, false), id), (\lambda b: Bool, false), \{false\})) \land\ (\neg (\exists D: Bool \to Bool, D \in E \land \operatorname{Refines}(id, \operatorname{conceptJoin}((\lambda b: Bool, false), D)))) \land \neg ((\operatorname{EqOn}(id, (\lambda b: Bool, false), \{false\}) \land \exists d: Bool \times Bool \to Bool, id = d \circ \operatorname{conceptJoin}((\lambda b: Bool, false), id) \land \operatorname{EqOn}(d \circ \operatorname{conceptJoin}((\lambda b: Bool, false), id), (\lambda b: Bool, false), \{false\})) \Rightarrow \exists D: Bool \to Bool, D \in E \land \operatorname{Refines}(id, \operatorname{conceptJoin}((\lambda b: Bool, false), D)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PrecedentTargetCompletion.target_completion_formal_distinction_not_noncircular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary case states, old facts, and verdicts, agreement on the old case set yields a decision through the canonical join of the old facts with the new verdict. The resulting decision still agrees with the old verdict on every old case.

The public countermodel uses Boolean cases. The permitted doctrine is nonempty and every permitted fact has the same value on the two cases, so it is specified without consulting the target verdict.

The target-completed interface decides the identity verdict, while no permitted fact joined with the constant old fact can do so. The final public conjunct is the resulting failure of the implication from formal distinction to a permitted noncircular reason.

The formal-completion clause directly applies the repository theorem `concept_join_universal`; repository and pinned-library searches found no theorem packaging it with old-case preservation and the doctrine countermodel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PrecedentTargetCompletion.target_completion_formal_distinction_not_noncircular`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](ConceptJoinUniversal.md)
