# Observation Rank Submodularity

## Abstract

Finite observation-subspace rank is submodular and has diminishing returns.

**Theorem 1.1 (Observation rank is submodular).**

$$\begin{aligned}\forall K, V, iota: \operatorname{Type},\\{}[\operatorname{DivisionRing}(K)], [\operatorname{AddCommGroup}(V)], [\operatorname{Module}(K, V)],\\{}[\operatorname{FiniteDimensional}(K, V)], [\operatorname{DecidableEq}(iota)],\\\forall U: iota \to \operatorname{Submodule}(K, V), r(A: \operatorname{Finset}(iota)) := \operatorname{finrank}(K, \operatorname{finsetSup}(A, U));\\(\forall A, B: \operatorname{Finset}(iota), r\left(\operatorname{union}(A, B)\right) + r\left(\operatorname{inter}(A, B)\right) \leq r\left(A\right) + r\left(B\right)) \land\\(\forall A, B: \operatorname{Finset}(iota), x: iota, A \subseteq B \Rightarrow r\left(\operatorname{union}(B, \operatorname{singleton}(x))\right) - r\left(B\right) \leq r\left(\operatorname{union}(A, \operatorname{singleton}(x))\right) - r\left(A\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ObservationRankSubmodularity.observation_rank_submodularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U assign a subspace of a finite-dimensional module to every observation index. For a finite selection A, its observation rank is the scalar dimension of the supremum of the selected subspaces.

The finite-supremum union identity identifies the combined selected space with a subspace supremum. The selected intersection embeds into the intersection of the two selected spaces, so the exact dimension formula for a supremum and infimum gives submodularity.

Applying the same inequality to A with the new index adjoined and to B yields the displayed diminishing-return form.

## References

- Truth anchor: `D5/S3/Observer/Linear/ObservationRankSubmodularity.observation_rank_submodularity`
