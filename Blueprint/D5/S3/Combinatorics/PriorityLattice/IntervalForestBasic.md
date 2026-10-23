# IntervalForestBasic

## Abstract

Priority-forest interval structure and counting.

**Definition 1.1 (IntervalForest).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{parent} : \operatorname{Fin} (\operatorname{n} + 1) \to \operatorname{Option} (\operatorname{Fin} (\operatorname{n} + 1))) (\operatorname{increasing} : \forall (\operatorname{v} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{parent} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{p} < \operatorname{v}) (\operatorname{intervals} : \forall (\operatorname{u} \operatorname{v} \operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{u} \leq \operatorname{v} \to \operatorname{v} \leq \operatorname{w} \to \operatorname{Relation.EqvGen} (\operatorname{fun} (\operatorname{a} \operatorname{b} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{parent} \operatorname{b} = \operatorname{some} \operatorname{a}) \operatorname{u} \operatorname{w} \to \operatorname{Relation.EqvGen} (\operatorname{fun} (\operatorname{a} \operatorname{b} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{parent} \operatorname{b} = \operatorname{some} \operatorname{a}) \operatorname{u} \operatorname{v}) , (\operatorname{IntervalForest.mk} \operatorname{parent} \operatorname{increasing} \operatorname{intervals}) . \operatorname{parent} = \operatorname{parent}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.IntervalForest` (`✓ std3`).

*Citation.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Section 2.1, pp. 3–4: a priority forest (labeled with [n]₀ and with m edges) is a rooted forest (T₀, T₁, …, Tₙ₋ₘ) with all component trees increasing and ordered according to the root's labels, and where for all j<k, every label in Tⱼ is smaller than every label in Tₖ. Thus, the vertex set of each tree is an interval of integers. The parent-function fields use Fin (n + 1), a smaller parent for each non-root, and Relation.EqvGen for connected components.

**Theorem 1.2 (IntervalForest / ext).**

$$\forall \{\operatorname{n} : \mathbb{N}\} \{\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}\} , \operatorname{P.parent} = \operatorname{Q.parent} \to \operatorname{P} = \operatorname{Q}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.3 (IntervalForest / edges).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{edges} \operatorname{P} = \{\operatorname{e} : \operatorname{Fin} (\operatorname{n} + 1) \times \operatorname{Fin} (\operatorname{n} + 1) \mid \operatorname{P.parent} \operatorname{e.2} = \operatorname{some} \operatorname{e.1}\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is {e | P.parent e.2 = some e.1}.

**Theorem 1.4 (IntervalForest / edges_injective).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{Function.Injective} (\operatorname{fun} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) \mapsto \operatorname{IntervalForestBasic.IntervalForest.edges} \operatorname{P})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.edges_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.5 (IntervalForest / forestPartialOrder).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} \operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{P} \leq \operatorname{Q} \iff \operatorname{IntervalForestBasic.IntervalForest.edges} \operatorname{P} \subseteq \operatorname{IntervalForestBasic.IntervalForest.edges} \operatorname{Q}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.forestPartialOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is PartialOrder.lift edges edges_injective.

**Definition 1.6 (filterCount).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{filterCount} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{n}) \mid \exists (\operatorname{m} : \operatorname{Nat}) , \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Ici} \operatorname{x} \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{m}))\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.filterCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Ici x ≃o (WithTop (IntervalForest m)))}.

**Definition 1.7 (idealCount).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{idealCount} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{n}) \mid \exists (\operatorname{m} : \operatorname{Nat}) , \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Iic} \operatorname{x} \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{m}))\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.idealCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}.

**Definition 1.8 (positiveIdealCount).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{positiveIdealCount} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{n}) \mid \exists (\operatorname{m} : \operatorname{Nat}) , 1 \leq \operatorname{m} \land \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Iic} \operatorname{x} \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForest} \operatorname{m}))\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.positiveIdealCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // exists m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}.

**Definition 1.9 (IntervalForest / empty).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , (\operatorname{IntervalForest.empty} \operatorname{n}) . \operatorname{parent} \operatorname{v} = \operatorname{none}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.empty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is parent := fun _ => none increasing := by simp intervals := by intro u v w huv hvw h have hempty : forall a b : Fin (n+1), Relation.EqvGen (fun a _ => (none : Option (Fin (n+1))) = some a) a b -> a = b := by intro a b hab induction hab with | rel x y h => cases h | refl x => rfl | symm x y _ ih => exact ih.symm | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2 have huw : u = w := hempty u w h have huv' : u = v := le_antisymm huv (huw ▸ hvw) subst v exact Relation.EqvGen.refl _.

**Theorem 1.10 (IntervalForest / parent_zero).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{P.parent} 0 = \operatorname{none}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.parent_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.11 (IntervalForest / card_zero).**

$$\operatorname{Nat.card} (\operatorname{IntervalForestBasic.IntervalForest} 0) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.card_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.12 (IntervalForest / no_skipped_root).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) \{\operatorname{v} \operatorname{p} \operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)\} , \operatorname{P.parent} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{p} < \operatorname{w} \to \operatorname{w} \leq \operatorname{v} \to \operatorname{P.parent} \operatorname{w} \neq \operatorname{none}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.no_skipped_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.13 (forestOfLocal).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{f} : \operatorname{Fin} (\operatorname{n} + 1) \to \operatorname{Option} (\operatorname{Fin} (\operatorname{n} + 1))) (\operatorname{inc} : \forall (\operatorname{v} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{f} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{p} < \operatorname{v}) (\operatorname{nskip} : \forall (\operatorname{v} \operatorname{p} \operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{f} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{p} < \operatorname{w} \to \operatorname{w} \leq \operatorname{v} \to \operatorname{f} \operatorname{w} \neq \operatorname{none}) , (\operatorname{forestOfLocal} \operatorname{f} \operatorname{inc} \operatorname{nskip}) . \operatorname{parent} = \operatorname{f}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.forestOfLocal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The literal parent function and increasing-parent proof, together with the no-skipped-root condition, construct the forest whose parent field is displayed.

**Definition 1.14 (IsTree).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForest} \operatorname{n}) , \operatorname{IsTree} \operatorname{P} \iff \forall (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{P.parent} \operatorname{v} = \operatorname{none} \to \operatorname{v} = 0$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.IsTree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is forall v, P.parent v = none -> v = 0.

**Definition 1.15 (treeEquivCode).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{T} : \{\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{IsTree} \operatorname{P}\}) (\operatorname{i} : \operatorname{Fin} \operatorname{n}) , \operatorname{Option.map} (\operatorname{fun} \operatorname{p} \mapsto \operatorname{val}(\operatorname{p})) (\operatorname{parent}(\operatorname{val}(\operatorname{T})) \operatorname{i.succ}) = \operatorname{some} (\operatorname{val}((\operatorname{treeEquivCode} \operatorname{n} \operatorname{T} \operatorname{i})))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.treeEquivCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The equivalence sends each vertex i + 1 to its parent label, which is at most i. The inverse attaches each non-root vertex to its prescribed parent.

**Theorem 1.16 (increasing_tree_card).**

$$\forall (\operatorname{n} : \mathbb{N}) , \operatorname{Nat.card} \{\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n} \mid \operatorname{IntervalForestBasic.IsTree} \operatorname{P}\} = \operatorname{n.factorial}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.increasing_tree_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.IntervalForest`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.IsTree`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.card_zero`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.edges`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.edges_injective`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.empty`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.ext`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.filterCount`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.forestOfLocal`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.forestPartialOrder`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.idealCount`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.increasing_tree_card`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.no_skipped_root`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.parent_zero`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.positiveIdealCount`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.treeEquivCode`
