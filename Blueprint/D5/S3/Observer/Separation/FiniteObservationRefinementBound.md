# Finite Observation Refinement Bound

## Abstract

Finite observation relations refine monotonically and reach their first stable depth within the available quotient-class budget.

**Theorem 1.1 (Finite observation refinement and stability bound).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(O)] [\operatorname{Nonempty}(Y)],\\\tau: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\c_{m} = \lvert Y / E_{m} \rvert, m_{*} = \operatorname{sInf} \{m \in \mathbb{N} \mid E_{m} = E_{m+1}\},\\(\forall m, E_{m+1} \subseteq E_{m}) \land\\(\forall m, c_{m} \leq c_{m+1}) \land\\E_{m_{*}} = E_{m_{*}+1} \land\\(\forall n, E_{n} = E_{n+1} \Rightarrow m_{*} \leq n) \land\\m_{*} \leq c_{m_{*}} - c_{0} \land\\c_{m_{*}} - c_{0} \leq \lvert Y \rvert - \lvert O \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FiniteObservationRefinementBound.finite_observation_refinement_and_stability_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y and O be finite types, let Y be nonempty, let tau update the state, and let q map Y surjectively onto the actual readout image. Write E_m for equality of readout words through depth m, c_m for the number of E_m classes, and m_star for the least depth where E_m and E_(m+1) agree.

Forgetting the latest readout gives a surjection from the depth-(m+1) quotient to the depth-m quotient, proving that the relations decrease and their class counts increase. Equality of consecutive class counts makes this forgetting map bijective and therefore forces equality of the two relations.

The repository theorem infinite_relation_stabilizes supplies an inhabited set of stable depths. Pinned Mathlib then supplies Nat.sInf_mem for attainment of the least one, together with Fintype.bijective_iff_surjective_and_card and Fintype.card_le_of_surjective for the strict-growth count.

Every depth before m_star consumes at least one new quotient class. Surjectivity identifies c_0 with the size of O, while every observation quotient has at most the size of Y. These facts yield both displayed inequalities without assuming a bound beyond the finite, nonempty state carrier and surjective readout fixed by the source section.

## References

- Truth anchor: `D5/S3/Observer/Separation/FiniteObservationRefinementBound.finite_observation_refinement_and_stability_bound`
