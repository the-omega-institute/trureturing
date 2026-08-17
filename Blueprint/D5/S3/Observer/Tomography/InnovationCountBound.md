# Large-Innovation Count Bound

## Abstract

Fixed-size innovations are bounded in count by the total information budget.

**Theorem 1.1 (Fixed-size innovations have bounded count).**

$$\forall h: \mathbb{N} \to \mathbb{R},\ \forall H, epsilon\in \mathbb{R},\ (\forall k\in \mathbb{N}, 0 \leq h_{k}) \land \operatorname{Summable}(h) \land \sum_{k=0}^{\infty} h_{k} \leq H \land 0 < epsilon \Rightarrow \operatorname{ncard}(\{k\in \mathbb{N} \mid epsilon \leq h_{k}\}) \leq \frac{H}{epsilon}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/InnovationCountBound.large_innovation_count_le_budget_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be a nonnegative summable real sequence of innovation sizes. Assume its infinite sum is at most the information budget H, and fix a positive threshold epsilon.

Summability makes h tend to zero, so only finitely many indices can carry innovation at least epsilon. On that finite superlevel set, each term contributes at least epsilon. Its cardinality times epsilon is therefore bounded by the full series and hence by H.

Two natural-language smart-search queries found no declaration-name match in pinned Mathlib. Local type-and-name search found and the proof applies Finset.card_nsmul_le_sum, Summable.sum_le_tsum, and Summable.tendsto_atTop_zero. Repository searches found no equivalent D5 declaration.

This closes qdo-v1 corollary/38.3, atom qdo-residual-e5dbac2b7c4a0f3d76c61ebda4f98553c6d853ad567ef180d4d256371ca1771c. It formalizes the displayed count bound for an abstract innovation sequence. It does not define the source's specific entropy H(P) or identify a concrete observation tower's increments with h.

## References

- Truth anchor: `D5/S3/Observer/Tomography/InnovationCountBound.large_innovation_count_le_budget_div`
