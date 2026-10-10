# PrincipalIdeals

## Abstract

Priority-forest interval structure and counting.

**Theorem 1.1 (forest_ideal_shape_iff).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , (\exists (\operatorname{m} : \operatorname{Nat}) , \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Iic} (\operatorname{P} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m}))) \iff \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 1 \lor (\operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 2 \land \operatorname{LowRankForests.OneLong} \operatorname{P}) \lor (\operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 3 \land \operatorname{LowRankForests.OneLong} \operatorname{P})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.forest_ideal_shape_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.2 (gamma_formula).**

$$\forall (\operatorname{n} : \mathbb{N}) , 1 \leq \operatorname{n} \to \operatorname{IntervalForestBasic.idealCount} \operatorname{n} = \operatorname{n}^{2} - \operatorname{n} + 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gamma_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.3 (gammaPos_formula).**

$$\forall (\operatorname{n} : \mathbb{N}) , 1 \leq \operatorname{n} \to \operatorname{IntervalForestBasic.positiveIdealCount} \operatorname{n} = \operatorname{n}^{2} + 2 - 2 \cdot \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gammaPos_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.4 (gamma).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{gamma} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{Pi} \operatorname{n} \mid \exists (\operatorname{m} : \operatorname{Nat}) , \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Iic} \operatorname{x} \equiv_{o} \operatorname{Pi} \operatorname{m})\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : Pi n // ∃ m ≤ n, Nonempty (Set.Iic x ≃o Pi m)}.

**Definition 1.5 (gammaPos).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{gammaPos} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{Pi} \operatorname{n} \mid \exists (\operatorname{m} : \operatorname{Nat}) , 1 \leq \operatorname{m} \land \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Iic} \operatorname{x} \equiv_{o} \operatorname{Pi} \operatorname{m})\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gammaPos` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : Pi n // ∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o Pi m)}.

**Definition 1.6 (claimGamma).**

$$\operatorname{claimGamma} \iff \forall (\operatorname{n} : \operatorname{Nat}) , 1 \leq \operatorname{n} \to \operatorname{gamma} \operatorname{n} = \operatorname{n}^{2} - \operatorname{n} + 2 \land \operatorname{gammaPos} \operatorname{n} = \operatorname{n}^{2} + 2 - 2 \cdot \operatorname{n}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.claimGamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Section 6, item 3, p. 24: How many principal ideals of Π(n) are isomorphic to Π(m), for some 1≤ m≤ n? Let γₙ denote the number of principal ideals of Π(n) that are isomorphic to Π(m) with m ≤ n. The sequence (γₙ)ₙ≥₁ begins as 2, 4, 8, 14, 22 ,32, 44, … This sequence seems to be https://oeis.org/A014206, which is given by the formula γₙ = n² + n + 2. The data give n² − n + 2, with m = 0 allowed. The positive-parameter reading gives n² + 2 − 2n. Both counts include the greatest element's ideal; natural subtraction is taken in the displayed order. These are the counting conventions of Lillo and Rosas; the count formulas resolve their final-section questions.

**Theorem 1.7 (result).**

$$\operatorname{claimGamma}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.claimGamma`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.forest_ideal_shape_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gamma`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gammaPos`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gammaPos_formula`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.gamma_formula`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.result`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/LowRankForests](LowRankForests.md)
- Dependency: [D5/S3/Combinatorics/PriorityLattice/PrincipalFilters](PrincipalFilters.md)
