# Trace and Rank Combinatorics

## Abstract

Transfer-operator traces and range ranks count finite-map combinatorics.

**Theorem 1.1 (Trace counts fixed points and rank counts the iterated image).**

$$\forall Y, \operatorname{Finite}(Y), \forall \tau: Y \to Y, \forall r, k \in \mathbb{N},\ 1 \leq r \Rightarrow 
(\operatorname{Tr}(transferOperator(\tau)^{r}) = \operatorname{card}(\operatorname{Fix}(\tau^{r})) \land 
\operatorname{finrank}(\operatorname{range}(transferOperator(\tau)^{k})) = \operatorname{card}(\operatorname{image}(\tau^{k}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics.trace_rank_combinatorial_meaning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a self-map act on the standard basis of the finite complex vector space by sending the basis vector at a state to the basis vector at its image.

The diagonal entry of a positive operator power is one exactly at a fixed point of the corresponding iterate, so the trace is the number of those fixed points.

The range of an arbitrary natural power is spanned by the distinct basis vectors indexed by the iterated image. Their linear independence makes the range dimension equal its cardinality.

Repository search found no equal or stronger combined theorem. Pinned Mathlib supplies trace_eq_matrix_trace, range_lmapDomain, lmapDomain_comp, basisSingleOne, and finrank_span_set_eq_card; the proof applies those declarations directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics.trace_rank_combinatorial_meaning`
