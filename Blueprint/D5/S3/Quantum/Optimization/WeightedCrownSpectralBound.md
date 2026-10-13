# Weighted crown spectral bound

## Abstract

The singlet-sector and star bounds control the literal crown Hamiltonian.

**Definition 1.1 (Crown vertex a).**

$$\forall (n:\mathbb{N}), \operatorname{a}\left(n\right) = none$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.a` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Appendix C.1, p. 33: "Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n ≥ 3." The two Option constructors distinguish the hubs and the n leaves.

**Definition 1.2 (Crown vertex b).**

$$\forall (n:\mathbb{N}), \operatorname{b}\left(n\right) = \operatorname{some}\left(none\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.b` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Appendix C.1, p. 33: "Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n ≥ 3." The two Option constructors distinguish the hubs and the n leaves.

**Definition 1.3 (Crown vertex leaf).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Fin}\left(n\right)), \operatorname{leaf}\left(i\right) = \operatorname{some}\left(\operatorname{some}\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.leaf` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Appendix C.1, p. 33: "Note that the n + 2 vertices in total are labeled as a, b, 1, 2, 3, . . . , n and we assume n ≥ 3." The two Option constructors distinguish the hubs and the n leaves.

**Definition 1.4 (A matrix acting at one site).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (A:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), \forall (s:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \operatorname{Fin}\left(2\right)), \forall (t:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \operatorname{Fin}\left(2\right)), \operatorname{site}\left(i, A\right)\left(s, t\right) = \prod_{k:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)}(\operatorname{ite}\left(k = i, A\left(s\left(k\right), t\left(k\right)\right), \operatorname{ite}\left(s\left(k\right) = t\left(k\right), 1, 0\right)\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.site` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The computational-basis entry is the product of the local matrix entry at i and identity entries at all other sites. This is the tensor action used in the singlet definition.

**Definition 1.5 (The singlet projection).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (j:\operatorname{Option}\left(\operatorname{Option}\left(\operatorname{Fin}\left(n\right)\right)\right)), \operatorname{singlet}\left(i, j\right) = (\frac{(1:\mathbb{C})}{(4:\mathbb{C})})\cdot(1 - \operatorname{site}\left(i, \operatorname{FiniteDimensional}.\operatorname{qubitX}\right) \cdot \operatorname{site}\left(j, \operatorname{FiniteDimensional}.\operatorname{qubitX}\right) - \operatorname{site}\left(i, (\operatorname{Complex}.\operatorname{I})\cdot(\operatorname{FiniteDimensional}.\operatorname{qubitX} \cdot \operatorname{FiniteDimensional}.\operatorname{qubitZ})\right) \cdot \operatorname{site}\left(j, (\operatorname{Complex}.\operatorname{I})\cdot(\operatorname{FiniteDimensional}.\operatorname{qubitX} \cdot \operatorname{FiniteDimensional}.\operatorname{qubitZ})\right) - \operatorname{site}\left(i, \operatorname{FiniteDimensional}.\operatorname{qubitZ}\right) \cdot \operatorname{site}\left(j, \operatorname{FiniteDimensional}.\operatorname{qubitZ}\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.singlet` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The source projector is (1 - X_i X_j - Y_i Y_j - Z_i Z_j)/4. FiniteDimensional.qubitX and qubitZ are the Pauli owners; Y is the inline expression Complex.I • (qubitX * qubitZ).

**Theorem 1.6 (The first hub differs from every leaf).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Fin}\left(n\right)), \operatorname{a}\left(n\right) \ne \operatorname{leaf}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.a_ne_leaf` (`✓ std3`). ∎

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The two hubs and the leaves are distinct vertices in Appendix C.1's labeling.

**Theorem 1.7 (The second hub differs from every leaf).**

$$\forall (n:\mathbb{N}), \forall (i:\operatorname{Fin}\left(n\right)), \operatorname{b}\left(n\right) \ne \operatorname{leaf}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.b_ne_leaf` (`✓ std3`). ∎

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The two hubs and the leaves are distinct vertices in Appendix C.1's labeling.

**Definition 1.8 (The weighted crown Hamiltonian).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{R}), \operatorname{crownH}\left(n, x\right) = ((x:\mathbb{C}))\cdot(\operatorname{singlet}\left(\operatorname{a}\left(n\right), \operatorname{b}\left(n\right)\right)) + \sum_{i:\operatorname{Fin}\left(n\right)}(\operatorname{singlet}\left(\operatorname{a}\left(n\right), \operatorname{leaf}\left(i\right)\right) + \operatorname{singlet}\left(\operatorname{b}\left(n\right), \operatorname{leaf}\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.crownH` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Appendix C.1, p. 33, Eq. (C1): H = x h_ab + sum from j = 1 to n of (h_aj + h_bj). The coefficient x is cast from real to complex and the n spokes are counted once.

**Definition 1.9 (The largest Rayleigh value).**

$$\forall (iota:Type), [\operatorname{Fintype}\left(iota\right)]\forall (H:\operatorname{Matrix}\left(iota, iota, \mathbb{C}\right)), \operatorname{lambdaMax}\left(H\right) = \operatorname{sSup}\left(\{r:\mathbb{R}\mid\exists (v:\operatorname{EuclideanSpace}\left(\mathbb{C}, iota\right)), (v \ne 0) \land (r = \frac{\operatorname{Complex}.\operatorname{re}\left(\sum_{i:iota}(\operatorname{star}\left(v\left(i\right)\right) \cdot \operatorname{Matrix}.\operatorname{mulVec}\left(H, v\right)\left(i\right))\right)}{\left\lVert v \right\rVert^{2}})\}\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.lambdaMax` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The largest value is the real supremum of nonzero-vector Rayleigh quotients. For the Hermitian crown Hamiltonian, this supremum is the largest eigenvalue.

**Theorem 1.10 (The crown spectral bound).**

$$\forall (n:\mathbb{N}), \forall (x:\mathbb{R}), (x \le 1 + \frac{(n:\mathbb{R})}{2}) \Rightarrow (\operatorname{lambdaMax}\left(\operatorname{crownH}\left(n, x\right)\right) \le (n:\mathbb{R}) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.crown_spectral_bound` (`✓ std3`). ∎

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The star-square relation bounds each hub star by (n+1)/2. The hub singlet is a projection P with PK = KP = (n/2)P. The identity (n+1)I-H = (I-P)((n+1)I-K)(I-P)+(1+n/2-x)P is positive semidefinite on the displayed range. P and K here describe the singlet and the sum of the two stars.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.a`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.a_ne_leaf`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.b`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.b_ne_leaf`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.crownH`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.crown_spectral_bound`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.lambdaMax`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.leaf`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.singlet`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownSpectralBound.site`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
