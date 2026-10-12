# LowRankForests

## Abstract

Priority-forest interval structure and counting.

**Definition 1.1 (OneLongAt).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForest} \operatorname{n}) (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{OneLongAt} \operatorname{P} \operatorname{v} \iff (\exists (\operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{P.parent} \operatorname{v} = \operatorname{some} \operatorname{p} \land \operatorname{val}(\operatorname{p}) + 2 = \operatorname{val}(\operatorname{v})) \land (\forall (\operatorname{w} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{w} \neq \operatorname{v} \to \operatorname{P.parent} \operatorname{w} = \operatorname{some} \operatorname{p} \to \operatorname{val}(\operatorname{p}) + 1 = \operatorname{val}(\operatorname{w}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/LowRankForests.OneLongAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

OneLongAt means that v has a parent two labels below it, and every other non-root has a parent one label below it.

**Definition 1.2 (OneLong).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForest} \operatorname{n}) , \operatorname{OneLong} \operatorname{P} \iff \exists (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{OneLongAt} \operatorname{P} \operatorname{v}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/LowRankForests.OneLong` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is ∃ v, OneLongAt P v.

**Definition 1.3 (CodeOneStep).**

$$\forall (\operatorname{k} : \operatorname{Nat}) (\operatorname{t} : ((\operatorname{v} : \operatorname{Fin} \operatorname{k}) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1))) , \operatorname{CodeOneStep} \operatorname{t} \iff \exists \operatorname{i} \operatorname{j} : \operatorname{Fin} \operatorname{k} , \operatorname{val}(\operatorname{i}) + 1 = \operatorname{val}(\operatorname{j}) \land \operatorname{val}((\operatorname{t} \operatorname{j})) = \operatorname{val}(\operatorname{i}) \land (\forall (\operatorname{z} : \operatorname{Fin} \operatorname{k}) , \operatorname{z} \neq \operatorname{j} \to \operatorname{val}((\operatorname{t} \operatorname{z})) = \operatorname{val}(\operatorname{z}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/LowRankForests.CodeOneStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

CodeOneStep has one pair of adjacent indices i and j with val(t j) = val(i); every other index z has val(t z) = val(z).

**Theorem 1.4 (IntervalForest / one_long_iff_code_one_step).**

$$\forall \{\operatorname{n} \operatorname{k} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) , \operatorname{LowRankForests.OneLong} \operatorname{P} \iff \operatorname{LowRankForests.CodeOneStep} (\operatorname{IdealCompression.IntervalForest.compressCode} \operatorname{P} \operatorname{h})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.one_long_iff_code_one_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.5 (SmallIdealCodes / oneStep_two_iff).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 2) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{LowRankForests.CodeOneStep} \operatorname{t} \iff \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t20}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.oneStep_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.6 (SmallIdealCodes / oneStep_three_iff).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 3) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{LowRankForests.CodeOneStep} \operatorname{t} \iff \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t3} 0 2 \lor \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t3} 1 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.oneStep_three_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.7 (long_two_card).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{Nat.card} \{\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 2 \land \operatorname{LowRankForests.OneLong} \operatorname{P}\} = \operatorname{n} - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.long_two_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.8 (long_three_card).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{Nat.card} \{\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 3 \land \operatorname{LowRankForests.OneLong} \operatorname{P}\} = (\operatorname{n} - 1) \cdot (\operatorname{n} - 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.long_three_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.9 (single_edges_card).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{Nat.card} \{\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = 1\} = \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/LowRankForests.single_edges_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.CodeOneStep`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.OneLong`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.OneLongAt`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.long_three_card`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.long_two_card`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.oneStep_three_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.oneStep_two_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.one_long_iff_code_one_step`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/LowRankForests.single_edges_card`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/IdealCompression](IdealCompression.md)
