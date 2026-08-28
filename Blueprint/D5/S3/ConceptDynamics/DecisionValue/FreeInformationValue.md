# Nonnegative Value of Free Information

## Abstract

A free ignorable observation cannot lower optimal expected value.

**Theorem 1.1 (Free ignorable information has nonnegative value).**

$$\forall X, E, U: \operatorname{Type},\\{}\mathbb{E}: \operatorname{Concept}\left(X \to \mathbb{R}, \mathbb{R}\right), observe: \operatorname{Concept}\left(X, E\right), worldAfterObservation: E \to \left(X \to X\right), V: \operatorname{Concept}\left(X, U \to \mathbb{R}\right), informationCost: \mathbb{R}, A0: \operatorname{Set}\left(U\right), A1: E \to \operatorname{Set}\left(U\right), P: \operatorname{Set}\left(E \to U\right), W_{0}, W_{E}: \mathbb{R},\\{}\pi_{adm} = \{p \in \pi \mid \forall e, p(e) \in U_{e}\},\\{}W_{0} = \max_{u \in U_{0}} \mathbb{E}(V(X)(u)),\\{}W_{E} = \max_{p \in \pi_{adm}} (\mathbb{E}(V(T(E)(X))(p(E))) - c_{E}),\\{}\operatorname{IsGreatest}\left(\operatorname{Image}\left(\mathbb{E}, V, A0\right), W_{0}\right), \operatorname{IsGreatest}\left(\operatorname{Image}\left(\mathbb{E}, V, \pi_{adm}\right), W_{E}\right),\\{}c_{E} = 0, \forall e, x, worldAfterObservation(e)(x) = x,\\{}\forall u \in U_{0}, \operatorname{const}(u) \in \pi,\\{}\forall e, U_{0} \subseteq U_{e}\\{}\Rightarrow W_{E} \geq W_{0}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue.free_ignorable_information_value_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uninformed value is the greatest expected utility obtained by choosing one available action. The informed value is the greatest net expected utility of an admissible observation-dependent policy.

The four safeguards are public. Information has zero cost, observation leaves the state unchanged, every constant policy is a permitted way to ignore the observation, and every previously available action remains available after each observation.

Choose an action attaining the uninformed optimum. Its constant policy is both permitted and pointwise available by the last two safeguards. The first two safeguards make its informed net value equal to the uninformed optimum, so informed optimality gives the inequality.

The expectation functional, observation, world transition, utility, costs, action sets, and policy set are independent source inputs. Repository and pinned-library searches found no exact theorem combining them.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue.free_ignorable_information_value_nonnegative`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
