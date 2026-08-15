# Finite-Time Tomography

## Abstract

A complete finite-dimensional observation tower separates states within its rank budget.

**Theorem 1.1 (A complete observation tower separates states within its rank budget).**

$$\operatorname{CompleteProgressiveTower}((V_k)_{k\in\mathbb{N}}) \Rightarrow \exists m\in\mathbb{N}, m\leq\operatorname{dim}(V)-\operatorname{dim}(V_0) \land \operatorname{Injective}(q_m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/FiniteTimeTomography.finite_time_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V_k be an increasing tower of subspaces in a finite-dimensional space. Assume their supremum is the whole space and every proper stage grows strictly at the next step. Also assume that the accumulated readout q_k is injective whenever V_k is the whole space.

Finite generation first gives some complete stage. Choose the earliest one. Every preceding inclusion is strict, so strict monotonicity of subspace dimension spends at least one rank at each step. The earliest complete stage is therefore at most dim V minus dim V_0, and its accumulated readout separates all states.

LeanSearch found and the proof applies the exact mathlib chain theorem Submodule.FG.stabilizes_of_iSup_eq. Loogle supplied the exact finrank strict-monotonicity and maximal-rank lemmas; repository and formalization searches found no existing finite-time result.

## References

- Truth anchor: `D5/S3/Observer/Tomography/FiniteTimeTomography.finite_time_tomography`
