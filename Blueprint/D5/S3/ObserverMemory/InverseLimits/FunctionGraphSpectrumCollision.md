# Function-Graph Spectrum Collision

## Abstract

Equal trace and rank spectra do not determine an eight-state functional graph.

**Theorem 1.1 (The complete spectra agree while the functional graphs do not).**

$$tauA(0) = 0 \land tauA(1) = 0 \land tauA(2) = 0 \land tauA(3) = 0 \land tauA(4) = 1 \land tauA(5) = 1 \land tauA(6) = 1 \land tauA(7) = 2 \land 
tauB(0) = 0 \land tauB(1) = 0 \land tauB(2) = 0 \land tauB(3) = 0 \land tauB(4) = 1 \land tauB(5) = 1 \land tauB(6) = 2 \land tauB(7) = 2 \land 
(\forall x, tauA(x) = x \iff x = 0) \land (\forall x, tauB(x) = x \iff x = 0) \land 
\operatorname{card}(Fin(8)) = 8 \land rankSpectrumValue(tauA, 1) = 3 \land rankSpectrumValue(tauB, 1) = 3 \land 
(\forall k, 2 \leq k \Rightarrow rankSpectrumValue(tauA, k) = 1) \land (\forall k, 2 \leq k \Rightarrow rankSpectrumValue(tauB, k) = 1) \land 
(\forall k, traceSpectrumValue(tauA, k) = traceSpectrumValue(tauB, k)) \land (\forall k, rankSpectrumValue(tauA, k) = rankSpectrumValue(tauB, k)) \land 
depthOneLeafMultiset(tauA) = \{3, 1, 0\} \land depthOneLeafMultiset(tauB) = \{2, 2, 0\} \land depthOneLeafMultiset(tauA) \neq depthOneLeafMultiset(tauB) \land 
\neg \exists e: Equiv.Perm(Fin(8)),\ \operatorname{Semiconj}(e, tauA, tauB).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision.same_trace_rank_spectra_not_function_graph_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identify 0,a,b,c,d,e,f,g with Fin 8 in that order. The displayed sixteen equations are the complete tables of tauA and tauB. The rank value is the cardinality of the iterated image, and the trace value is the number of fixed points of the iterate.

A leaf has no predecessor. The depth-one leaf multiset collects the leaf counts at the non-root children mapped directly to 0. Its values are {3,1,0} and {2,2,0}.

A functional-graph isomorphism is expressed without a new classifier: it is a permutation semiconjugating tauA to tauB. Such a map would preserve every fiber cardinality, but tauA has a fiber of size three and tauB has none, so no conjugacy exists.

This theorem certifies only the collision (negative) half of proposition 8.5. The positive half, linear similarity of the two transition matrices, is certified by D5/S3/ObserverMemory/InverseLimits/FunctionGraphLinearSimilarity.transition_matrices_linearly_similar.

Repository and pinned-Mathlib searches found no equal or stronger statement. Mathlib supplies Semiconj, iterate_add_apply, image_const, and card_congr; GitHub Lean-code search found only those building blocks and mirrors.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision.same_trace_rank_spectra_not_function_graph_conjugate`
