# Weighted crown moment certificate

## Abstract

A feasible level-one moment certificate with a strict value gap.

**Definition 1.1 (Crown interval boundary L).**

$$\forall (n:\mathbb{N}), \operatorname{L}\left(n\right) = \frac{\left((n:\mathbb{R}) + 2\right)^{2}}{4 \cdot \left((n:\mathbb{R}) + 1\right)}$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.L` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The lower boundary in Appendix C.1 is (n+2)^2/(4(n+1)).

**Definition 1.2 (Crown interval boundary U).**

$$\forall (n:\mathbb{N}), \operatorname{U}\left(n\right) = \frac{(n:\mathbb{R}) + 2}{3}$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.U` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The upper boundary of the interval left open in Appendix C.1 is (n+2)/3.

**Definition 1.3 (The crown edge weights).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{R}), \forall (e:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}), \operatorname{crownWeight}\left(n, x, e\right) = \operatorname{ite}\left((\operatorname{a}\left(n\right) \in \operatorname{val}\left(e\right)) \land (\operatorname{b}\left(n\right) \in \operatorname{val}\left(e\right)), x, \operatorname{ite}\left((\operatorname{a}\left(n\right) \in \operatorname{val}\left(e\right)) \lor (\operatorname{b}\left(n\right) \in \operatorname{val}\left(e\right)), 1, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.crownWeight` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The central edge has weight x, each spoke has weight 1, and every pair of leaves has weight 0.

**Definition 1.4 (Real level-one projector moments).**

$$\forall (n:\mathbb{N}), \forall (M:\operatorname{Matrix}\left(\operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \mathbb{R}\right)), \operatorname{npa1Feasible}\left(M\right) = \left((\operatorname{Matrix}.\operatorname{IsSymm}\left(M\right)) \land ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(M\right)) \land ((M\left(none, none\right) = 1) \land ((\forall (e:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}), M\left(\operatorname{some}\left(e\right), \operatorname{some}\left(e\right)\right) = M\left(none, \operatorname{some}\left(e\right)\right)) \land (\forall (e:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}), \forall (f:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}), \forall (g:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}), (\operatorname{card}\left(\operatorname{Finset}.\operatorname{inter}\left(\operatorname{val}\left(e\right), \operatorname{val}\left(f\right)\right)\right) = 1) \Rightarrow ((\operatorname{val}\left(g\right) = \operatorname{symmDiff}\left(\operatorname{val}\left(e\right), \operatorname{val}\left(f\right)\right)) \Rightarrow (M\left(\operatorname{some}\left(e\right), \operatorname{some}\left(f\right)\right) + M\left(\operatorname{some}\left(f\right), \operatorname{some}\left(e\right)\right) = \frac{M\left(none, \operatorname{some}\left(e\right)\right) + M\left(none, \operatorname{some}\left(f\right)\right) - M\left(none, \operatorname{some}\left(g\right)\right)}{2}))))))\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.npa1Feasible` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Section III defines NPA_l by positive semidefinite Hermitian moment matrices, identity normalization and the truncated operator relations. At the real first level these are exactly symmetry, the idempotent diagonals and the displayed adjacent-pair anticommutator. Disjoint commutation follows from symmetry.

**Definition 1.5 (The moment objective).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{R}), \forall (M:\operatorname{Matrix}\left(\operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \mathbb{R}\right)), \operatorname{objective}\left(x, M\right) = \sum_{e:\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}}(\operatorname{crownWeight}\left(n, x, e\right) \cdot M\left(none, \operatorname{some}\left(e\right)\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.objective` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The objective sums each unordered pair once, with the literal crown weights.

**Definition 1.6 (The real first-level optimum).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{R}), \operatorname{npa1Value}\left(n, x\right) = \operatorname{sSup}\left(\{r:\mathbb{R}\mid\exists (M:\operatorname{Matrix}\left(\operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \operatorname{Option}\left(\{s:\operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\mid\operatorname{card}\left(s\right) = 2\}\right), \mathbb{R}\right)), (\operatorname{npa1Feasible}\left(M\right)) \land (r = \operatorname{objective}\left(x, M\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.npa1Value` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The source proves NPA_1 = NPA_1^R for any weighted graph. The encoding takes the real supremum of exactly the feasible objective values.

**Theorem 1.7 (A strict moment-value gap).**

$$\forall (n:\mathbb{N}), (3 \le n) \Rightarrow (\forall (x:\mathbb{R}), (\operatorname{L}\left(n\right) < x) \Rightarrow ((x < \operatorname{U}\left(n\right)) \Rightarrow ((n:\mathbb{R}) + 1 < \operatorname{npa1Value}\left(n, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.constructed_value_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

An explicit Gram matrix supplies a feasible moment matrix throughout L < x < U. Its objective is n+1+(x-L)^2/(32n), which is strictly above n+1. Positive rank-one summands and positive scalar block coefficients certify the matrix.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.L`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.U`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.constructed_value_gap`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.crownWeight`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.npa1Feasible`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.npa1Value`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.objective`
- Dependency: [D5/S3/Quantum/Optimization/WeightedCrownSpectralBound](WeightedCrownSpectralBound.md)
