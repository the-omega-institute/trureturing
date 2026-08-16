# Pure Record Distinguishability and Coherence

## Abstract

Normalized pure records obey exact distinguishability-coherence complementarity.

**Theorem 1.1 (Pure-record distinguishability and coherence are complementary).**

$$\forall E: \operatorname{InnerProductSpace}_{\mathbb{C}},\ e_{L}, e_{R}\in E,\ \Vert e_{L} \Vert = 1 \land \Vert e_{R} \Vert = 1,\\c = \langle e_{L}, e_{R} \rangle, V = \lvert c \rvert, D = \sqrt{1 - V^{2}} \Rightarrow\\D^{2} + V^{2} = 1 \land\\(c = 0 \Rightarrow D = 1 \land V = 0) \land\\(V = 1 \Rightarrow D = 0 \land V = 1) \land\\(D = 1 \Rightarrow V = 0 \land \forall \rho\in \mathbb{C},\ c\rho = 0) \land\\(V = 1 \Rightarrow D = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/RecordCoherenceComplementarity.pure_record_distinguishability_coherence_complementarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let eL and eR be normalized pure record vectors. Their overlap is c, the retained coherence is V = |c|, and the optimal equal-prior distinguishability is D = sqrt(1 - V^2).

The theorem retains the exact identity D^2 + V^2 = 1 and both overlap endpoints. Zero overlap gives perfect distinguishability and zero visibility; unit visibility gives zero distinguishability.

The operational consequence is explicit: perfect distinguishability forces c to annihilate every unread off-diagonal amplitude. Conversely, complete retained coherence leaves no distinguishability.

Loogle, LeanSearch, and the pinned Mathlib tree identify norm_inner_le_norm and Real.sq_sqrt as the exact declarations applied by the Lean proof.

## References

- Truth anchor: `D5/S3/Quantum/PureState/RecordCoherenceComplementarity.pure_record_distinguishability_coherence_complementarity`
