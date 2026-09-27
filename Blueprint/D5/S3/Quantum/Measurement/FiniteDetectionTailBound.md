# Finite Detection Tail Bound

## Abstract

Finite-dimensional repeated detection has a geometric survival tail above its dark subspace.

**Theorem 1.1 (Survival beyond the dark weight has a finite geometric tail).**

$$\forall d \in \mathbb{N}, X \in \operatorname{Type}, fintype \in \operatorname{Fintype}\left(X\right), Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), L \in X \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; Q^{*} \cdot Q + \sum_{x \in X} L\left(x\right)^{*} \cdot L\left(x\right) = I_{d} \Rightarrow \left(\exists g \in \mathbb{R},\; \left(\left(0 < g \land g \le 1\right) \land \left(\forall m \in \mathbb{N},\; 0 \le {Q^{*}}^{m \cdot d} \cdot {Q}^{m \cdot d} - \operatorname{darkProjection}\left(Q, L\right) \land {Q^{*}}^{m \cdot d} \cdot {Q}^{m \cdot d} - \operatorname{darkProjection}\left(Q, L\right) \le \operatorname{smul}\left({1 - g}^{m}, I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right)\right)\right) \land \left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{PosSemidef}\left(rho\right) \Rightarrow \left(\operatorname{Tr}\left(rho\right) = 1 \Rightarrow \left(\operatorname{darkProjection}\left(Q, L\right) \cdot rho = 0 \Rightarrow \left(\operatorname{Summable}\left(N \mapsto \operatorname{Re}\left(\operatorname{Tr}\left(rho \cdot {Q^{*}}^{N} \cdot {Q}^{N}\right)\right)\right) \land \operatorname{tsum}\left(N \mapsto \operatorname{Re}\left(\operatorname{Tr}\left(rho \cdot {Q^{*}}^{N} \cdot {Q}^{N}\right)\right)\right) \le \frac{d}{g}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteDetectionTailBound.finite_detection_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the no-click operator, let L_x be the finite family of click operators, and let P be the orthogonal projection onto the vectors that never click. Completeness forces survival on the orthogonal complement of that dark space to contract uniformly within one dimension block.

There is a real gap g strictly between zero and one inclusive. At every block endpoint, the survival operator above P is positive and is bounded in the Loewner order by the corresponding geometric multiple of I-P.

For every positive semidefinite trace-one matrix supported orthogonally to the dark space, the real survival probabilities form a summable sequence. Their total is at most the dimension divided by g.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionTailBound.finite_detection_tail_bound`
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit](FiniteDetectionSurvivalLimit.md)
