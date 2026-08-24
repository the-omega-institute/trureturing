# Information Value Monotonicity

## Abstract

Free ignorable refinement with unchanged actions cannot lower optimal value.

**Theorem 1.1 (Free information refinement cannot lower optimal value).**

$$c = 0,\\{}\forall d, x, T(d)(x) = x,\\{}\exists p: D \to C, q_{C} = p \circ q_{D} \land\\{}(\forall d, U_{D}(d) = U_{C}(p(d))) \land\\{}(\forall p_{C} \in \pi_{C}, p_{C} \circ p \in \pi_{D}),\\{}W_{C} = \max_{p_{C} \in \operatorname{admissiblePolicies}\left(\pi_{C}, U_{C}\right)} \operatorname{informedExpectedValue}\left(\mathbb{E}, q_{C}, \operatorname{idWorld}, V, 0, p_{C}\right),\\{}W_{D} = \max_{p_{D} \in \operatorname{admissiblePolicies}\left(\pi_{D}, U_{D}\right)} \operatorname{informedExpectedValue}\left(\mathbb{E}, q_{D}, T, V, c, p_{D}\right)\\{}\Rightarrow W_{D} \geq W_{C}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity.free_information_refinement_value_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coarse and fine policy values use the same expectation and utility. The fine value additionally evaluates the post-information world and subtracts the information cost.

The public factor witness states concept refinement. Its remaining public clauses say that action sets are exactly preserved through the factor and every coarse candidate policy can ignore the added information by composition.

Lift a policy attaining the coarse optimum along the forgetting map. Exact action preservation makes it admissible; zero cost and the unchanged world make its fine value equal to the coarse optimum. Fine optimality then supplies the comparison.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity.free_information_refinement_value_monotone`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue](FreeInformationValue.md)
