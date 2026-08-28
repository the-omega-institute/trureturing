# Finite Future Congruence

## Abstract

Finite future refinement stabilizes at the maximal invariant observation congruence.

**Theorem 1.1 (Finite future refinement is the maximal invariant congruence).**

$$\begin{gathered}\forall Y, O: \operatorname{Type},\\{}[\operatorname{Fintype}(Y)], \tau: Y \to Y, q: Y \to O,\\\forall m\in \mathbb{N}, E_{m+1} = \operatorname{Phi}(E_{m}) \land E_{0} = \ker q,\\E_{\infty} = \operatorname{Inf}_{m \geq 0} E_{m} = \operatorname{finiteFutureRelation}\left(\tau, q, \operatorname{stabilizationIndex}\left(\tau, q\right)\right),\\\operatorname{Equivalence}\left(E_{\infty}\right) \land E_{\infty} \subseteq \ker q \land \forall y, z, (y, z) \in E_{\infty} \Rightarrow (\tau(y), \tau(z)) \in E_{\infty},\\\forall R, R \subseteq \ker q \land (\forall y, z, (y, z) \in R \Rightarrow (\tau(y), \tau(z)) \in R) \Rightarrow R \subseteq E_{\infty},\\E_{\infty} = \nu R. \operatorname{Phi}(R).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FiniteFutureCongruence.finite_future_maximal_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier Y, update tau, and observation q, let E_m relate states whose observations agree from time zero through time m. Let E_infinity require agreement at every finite time, and let Phi retain the current observation kernel while pulling a relation back through one update.

The index m_star is the maximum, over all state pairs, of their first separation time, with zero assigned to pairs that never separate. The proof shows that E_infinity equals E_m_star and that m_star is no larger than any index where consecutive refinements agree. Thus this explicit index has the least-stabilization meaning used by the theorem.

The stabilized relation is an equivalence relation inside the kernel of q, is preserved by tau, and contains every relation with those two containment and preservation properties. This stronger relation-level maximality immediately includes the stated maximality among equivalence relations.

The repository fixed-point theorem supplies the exact greatest fixed point extremality result, backed by the pinned library OrderHom fixed-point declarations. Local and web searches found no theorem combining the recurrence, finite stabilization, maximality, and greatest-fixed-point clauses.

The surrounding source assumes a nonempty carrier and a surjective observation map after replacing the output by its image. None of this theorem's clauses needs either restriction, so the checked statement proves the complete claim for every finite carrier and every observation map without adding a hypothesis.

## References

- Truth anchor: `D5/S3/Observer/Separation/FiniteFutureCongruence.finite_future_maximal_congruence`
- Dependency: [D5/S1/Dynamics/KnasterTarski](../../../S1/Dynamics/KnasterTarski.md)
