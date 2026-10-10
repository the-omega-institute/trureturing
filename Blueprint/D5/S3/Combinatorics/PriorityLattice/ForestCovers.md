# ForestCovers

## Abstract

Priority-forest interval structure and counting.

**Definition 1.1 (IntervalForest / support).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{support} \operatorname{P} = \operatorname{Finset.univ.filter} (\operatorname{fun} (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{P.parent} \operatorname{v} \neq \operatorname{none})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/ForestCovers.support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is by classical exact Finset.univ.filter (fun v => P.parent v ≠ none).

**Theorem 1.2 (IntervalForest / mem_support).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{v} \in \operatorname{ForestCovers.IntervalForest.support} \operatorname{P} \iff \operatorname{P.parent} \operatorname{v} \neq \operatorname{none}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.mem_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.3 (IntervalForest / le_iff_parent).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{P} \leq \operatorname{Q} \iff \forall (\operatorname{v} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{P.parent} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{Q.parent} \operatorname{v} = \operatorname{some} \operatorname{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.le_iff_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.4 (IntervalForest / support_mono).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}\} , \operatorname{P} \leq \operatorname{Q} \to \operatorname{ForestCovers.IntervalForest.support} \operatorname{P} \subseteq \operatorname{ForestCovers.IntervalForest.support} \operatorname{Q}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.support_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.5 (IntervalForest / edgeCount).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForest} \operatorname{n}) , \operatorname{edgeCount} \operatorname{P} = (\operatorname{support} \operatorname{P}) . \operatorname{card}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is (support P).card.

**Theorem 1.6 (IntervalForest / covBy_iff_edgeCount).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}\} , \operatorname{P} \operatorname{CovBy} \operatorname{Q} \iff \operatorname{P} < \operatorname{Q} \land \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{Q} = \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.covBy_iff_edgeCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.7 (IntervalForest / edgeCount_le).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} \leq \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.8 (IntervalForest / edgeCount_eq_iff_tree).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{n} \iff \operatorname{IntervalForestBasic.IsTree} \operatorname{P}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount_eq_iff_tree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.9 (rank).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) , \operatorname{rank} \operatorname{x} = \operatorname{Option.elim} (\operatorname{x} : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) (\operatorname{n} + 1) \operatorname{ForestCovers.IntervalForest.edgeCount}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/ForestCovers.rank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is (x : Option (IntervalForest n)).elim (n+1) IntervalForest.edgeCount.

**Theorem 1.10 (coatom_iff_tree).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{IsCoatom} (\operatorname{P} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) \iff \operatorname{IntervalForestBasic.IsTree} \operatorname{P}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.coatom_iff_tree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.11 (covBy_rank).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{x} \operatorname{y} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})\} , \operatorname{x} \operatorname{CovBy} \operatorname{y} \to \operatorname{ForestCovers.rank} \operatorname{y} = \operatorname{ForestCovers.rank} \operatorname{x} + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.covBy_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.12 (atom_card_orderIso).**

$$\forall \{\operatorname{A} : \operatorname{Type}\} \{\operatorname{B} : \operatorname{Type}\} [\operatorname{PartialOrder} \operatorname{A}] [\operatorname{PartialOrder} \operatorname{B}] [\operatorname{OrderBot} \operatorname{A}] [\operatorname{OrderBot} \operatorname{B}] , (\operatorname{A} \equiv_{o} \operatorname{B}) \to \operatorname{Nat.card} \{\operatorname{a} : \operatorname{A} \mid \operatorname{IsAtom} \operatorname{a}\} = \operatorname{Nat.card} \{\operatorname{b} : \operatorname{B} \mid \operatorname{IsAtom} \operatorname{b}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.atom_card_orderIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.13 (IntervalForest / eq_of_same_support_below).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{P} \operatorname{Q} \operatorname{R} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}\} , \operatorname{Q} \leq \operatorname{P} \to \operatorname{R} \leq \operatorname{P} \to \operatorname{ForestCovers.IntervalForest.support} \operatorname{Q} = \operatorname{ForestCovers.IntervalForest.support} \operatorname{R} \to \operatorname{Q} = \operatorname{R}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.eq_of_same_support_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.14 (IntervalForest / lower_covers_card_le).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{Nat.card} \{\operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{Q} \operatorname{CovBy} \operatorname{P}\} \leq \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.lower_covers_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.15 (ideal_iso_rank).**

$$\forall \{\operatorname{n} \operatorname{m} : \mathbb{N}\} \{\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})\} , (\operatorname{CoeSort.coe}\left(\operatorname{Set.Iic} \operatorname{x}\right) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m})) \to \operatorname{ForestCovers.rank} \operatorname{x} = \operatorname{m} + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.ideal_iso_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.16 (filter_iso_rank).**

$$\forall \{\operatorname{n} \operatorname{m} : \mathbb{N}\} \{\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})\} , (\operatorname{CoeSort.coe}\left(\operatorname{Set.Ici} \operatorname{x}\right) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m})) \to \operatorname{m} + 1 = \operatorname{n} + 1 - \operatorname{ForestCovers.rank} \operatorname{x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.filter_iso_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.17 (top_filter_not_iso).**

$$\forall (\operatorname{n} \operatorname{m} : \operatorname{Nat}) , \neg \operatorname{Nonempty} (\operatorname{Set.Ici} (\operatorname{Top.top} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.top_filter_not_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.18 (forest_ideal_index_le_two).**

$$\forall (\operatorname{n} \operatorname{m} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , (\operatorname{Set.Iic} (\operatorname{P} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m})) \to \operatorname{m} \leq 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.forest_ideal_index_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.19 (IntervalForest / cover_adjacent_roots).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}\} , \operatorname{P} \operatorname{CovBy} \operatorname{Q} \to \exists (\operatorname{v} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{P.parent} \operatorname{v} = \operatorname{none} \land \operatorname{Q.parent} \operatorname{v} = \operatorname{some} \operatorname{p} \land \operatorname{p} < \operatorname{v} \land (\forall (\operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{p} < \operatorname{w} \to \operatorname{w} < \operatorname{v} \to \operatorname{P.parent} \operatorname{w} \neq \operatorname{none}) \land (\forall (\operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{w} \neq \operatorname{v} \to \operatorname{Q.parent} \operatorname{w} = \operatorname{P.parent} \operatorname{w})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/ForestCovers.cover_adjacent_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.atom_card_orderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.coatom_iff_tree`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.covBy_iff_edgeCount`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.covBy_rank`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.cover_adjacent_roots`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount_eq_iff_tree`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.edgeCount_le`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.eq_of_same_support_below`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.filter_iso_rank`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.forest_ideal_index_le_two`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.ideal_iso_rank`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.le_iff_parent`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.lower_covers_card_le`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.mem_support`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.rank`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.support`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.support_mono`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/ForestCovers.top_filter_not_iso`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic](IntervalForestBasic.md)
