# Information Value Monotonicity

## Abstract

Free ignorable refinement with unchanged actions cannot lower optimal value.

**Theorem 1.1 (Free information refinement cannot lower optimal value).**

$$\begin{gathered}\forall X, C, D, U: \operatorname{Type},\\{}\mathbb{E}: \operatorname{Concept}\left(X \to \mathbb{R}, \mathbb{R}\right), q_{C}: \operatorname{Concept}\left(X, C\right),\\{}q_{D}: \operatorname{Concept}\left(X, D\right), T: D \to X \to X,\\{}V: \operatorname{Concept}\left(X, U \to \mathbb{R}\right), c: \mathbb{R},\\{}U_{C}: C \to \operatorname{Set}\left(U\right), U_{D}: D \to \operatorname{Set}\left(U\right),\\{}\pi_{C}: \operatorname{Set}\left(C \to U\right), \pi_{D}: \operatorname{Set}\left(D \to U\right),\\{}W_{C}, W_{D}: \mathbb{R},\\{}c = 0,\\{}\forall d: D, x: X, T(d)(x) = x,\\{}\exists p: D \to C, q_{C} = p \circ q_{D} \land\\{}(\forall d: D, U_{D}(d) = U_{C}(p(d))) \land\\{}(\forall p_{C}: C \to U, p_{C} \in \pi_{C} \Rightarrow p_{C} \circ p \in \pi_{D}),\\{}W_{C} = \max_{p_{C} \in \operatorname{admissiblePolicies}\left(\pi_{C}, U_{C}\right)} \operatorname{informedExpectedValue}\left(\mathbb{E}, q_{C}, \operatorname{idWorld}, V, 0, p_{C}\right),\\{}W_{D} = \max_{p_{D} \in \operatorname{admissiblePolicies}\left(\pi_{D}, U_{D}\right)} \operatorname{informedExpectedValue}\left(\mathbb{E}, q_{D}, T, V, c, p_{D}\right)\\{}\Rightarrow W_{D} \geq W_{C}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity.free_information_refinement_value_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coarse and fine policy values use the same expectation and utility. The fine value additionally evaluates the post-information world and subtracts the information cost.

The public factor witness states concept refinement. Its remaining public clauses say that action sets are exactly preserved through the factor and every coarse candidate policy can ignore the added information by composition.

Lift a policy attaining the coarse optimum along the forgetting map. Exact action preservation makes it admissible; zero cost and the unchanged world make its fine value equal to the coarse optimum. Fine optimality then supplies the comparison.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity.free_information_refinement_value_monotone`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue](FreeInformationValue.md)
