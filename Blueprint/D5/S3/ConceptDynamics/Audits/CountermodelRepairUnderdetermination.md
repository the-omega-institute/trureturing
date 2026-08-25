# Countermodel Repair Underdetermination

## Abstract

One countermodel supports assumption restriction and conclusion enlargement without selecting between them.

**Theorem 1.1 (A countermodel diagnoses failure without uniquely prescribing repair).**

$$\forall M: \operatorname{Type}, A, P: \operatorname{Set}\left(M\right), R: \operatorname{Set}\left(M\right) \to \operatorname{Set}\left(M\right) \to Prop, m: M,\\{}m \in A \setminus P \Rightarrow\\{}(\neg (m \in P) \lor\\{}\neg (A \subseteq P) \lor\\{}(\exists Aprime: \operatorname{Set}\left(M\right), Aprime \subset A \land \neg (m \in Aprime)) \lor\\{}(\operatorname{Derives}\left(R, A, P\right) \land \neg (A \subseteq P))) \land\\{}(\{x \mid x \in A \land x \neq m\} \subset A \land\\{}(\{x \mid x \in A \land x \neq m\} \setminus P) \subset A \setminus P \land\\{}P \subset \{x \mid x \in P \lor x = m\} \land\\{}(A \setminus \{x \mid x \in P \lor x = m\}) \subset A \setminus P).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/CountermodelRepairUnderdetermination.countermodel_diagnosis_is_underdetermined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state in the assumption-minus-conclusion set witnesses the advertised four-way diagnosis: the conclusion fails there, the assumptions do not entail it, the state may be excluded by a stricter assumption set, or a purported derivation of the invalid entailment is refuted.

Restricting the assumptions away from the witness and enlarging the conclusion to include it are both strict changes. Each construction strictly reduces the corresponding countermodel set, so the original countermodel alone does not choose the repair direction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/CountermodelRepairUnderdetermination.countermodel_diagnosis_is_underdetermined`
