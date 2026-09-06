# Query Family Identification

## Abstract

A dependent query family identifies exactly the targets constant on its joint kernel, equivalently those descending uniquely to the query quotient.

**Definition 1.1 (The query kernel is simultaneous answer equality).**

$$\begin{gathered}\forall M, I: \operatorname{Type},\\{}A: I \to \operatorname{Type}, Q: (i: I) \to M \to A(i), m, n: M,\\{}queryKernel(Q, m, n) \iff \forall i: I, Q(i, m) = Q(i, n).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.queryKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a dependent query family Q, two models lie in its kernel exactly when Q_i gives equal answers on the two models for every index i.

**Theorem 1.2 (Identification is query-kernel inclusion).**

$$\begin{gathered}\forall M, I, Z: \operatorname{Type},\\{}A: I \to \operatorname{Type}, Q: (i: I) \to M \to A(i), T: M \to Z,\\{}IdentifiedBy(Q, T) \Leftrightarrow \forall m, n: M, queryKernel(Q, m, n) \Rightarrow T(m) = T(n).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_kernel_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint answer to a dependent query family is a dependent function whose component at an index is the answer to that query. Two models have the same joint answer exactly when every component answer agrees.

Consequently the family identifies a target exactly when agreement under every query forces agreement under the target. This is the inclusion of the simultaneous query kernel in the target kernel, with no nonemptiness assumption.

**Lemma 1.3 (The dependent joint connects to single-interface sufficiency).**

$$\begin{gathered}\forall M, I, Z: \operatorname{Type},\\{}A: I \to \operatorname{Type}, Q: (i: I) \to M \to A(i), T: M \to Z,\\{}Nonempty(M) \Rightarrow (IdentifiedBy(Q, T) \Leftrightarrow Refines(canonicalTargetReadout(T), jointQuery(Q))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_joint_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the model space is nonempty, the whole dependent answer tuple is an ordinary single interface. The existing universal sufficiency factorization theorem applied to that joint interface identifies its fiber criterion with refinement of the canonical target readout.

This bridge is the reuse point from the earlier single-interface result. The dependent answer type causes no obstruction because a dependent function space is still one Lean type.

**Lemma 1.4 (Nonempty models are necessary for global joint refinement).**

$$\begin{gathered}Q: (i: \emptyset) \to \emptyset \to Unit, T: \emptyset \to \emptyset,\\{}IdentifiedBy(Q, T) \land\\{}\neg Refines(canonicalTargetReadout(T), jointQuery(Q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.nonempty_is_necessary_for_joint_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let both the model type and query index type be empty, use Unit as the answer type, and take the target value type to be empty. Kernel identification is vacuous because there are no models.

The joint answer type is nevertheless inhabited by its unique empty function, while the canonical target image is empty. No map from all joint answers to that target image can exist, so refinement fails. This isolates the exact role of the nonempty hypothesis.

**Lemma 1.5 (Factorization through the query quotient is unique).**

$$\begin{gathered}\forall M, I, Z: \operatorname{Type},\\{}A: I \to \operatorname{Type}, Q: (i: I) \to M \to A(i), T: M \to Z,\\{}f, g: QueryQuotient(Q) \to Z,\\{}(T = f \circ queryQuotientProjection(Q) \land T = g \circ queryQuotientProjection(Q)) \Rightarrow f = g.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.quotient_factorization_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose two maps from the query quotient recover the same target after composition with the canonical projection. Every quotient class has a model representative, so evaluation at a representative shows the two maps agree on that class.

The proof needs no identification hypothesis once both factorizations are supplied. Surjectivity of the quotient projection alone gives uniqueness, including for an empty model space.

**Theorem 1.6 (Identification is unique query-quotient factorization).**

$$\begin{gathered}\forall M, I, Z: \operatorname{Type},\\{}A: I \to \operatorname{Type}, Q: (i: I) \to M \to A(i), T: M \to Z,\\{}IdentifiedBy(Q, T) \Leftrightarrow \exists! f: QueryQuotient(Q) \to Z, T = f \circ queryQuotientProjection(Q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_unique_quotient_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel inclusion makes the target constant on every query-equivalence class, so the library quotient lift defines a target readout on the quotient. Its composition with the projection is the original target.

Conversely, any such factorization sends query-equivalent models to the same target value because their quotient classes agree. The surjectivity lemma supplies uniqueness, yielding the claimed unique factorization without extra instances.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_joint_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_kernel_inclusion`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.identification_iff_unique_quotient_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.nonempty_is_necessary_for_joint_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.queryKernel`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification.quotient_factorization_unique`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](UniversalSufficiencyFactorization.md)
