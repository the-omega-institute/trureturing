# PrincipalFilters

## Abstract

Priority-forest interval structure and counting.

**Definition 1.1 (IntervalForest / roots).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{roots} \operatorname{P} = \operatorname{Finset.univ.filter} (\operatorname{fun} (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{P.parent} \operatorname{v} = \operatorname{none})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.roots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is by classical exact Finset.univ.filter (fun v => P.parent v = none).

**Theorem 1.2 (IntervalForest / roots_nonempty).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , (\operatorname{PrincipalFilters.IntervalForest.roots} \operatorname{P}) . \operatorname{Nonempty}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.roots_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.3 (IntervalForest / lastRoot).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , \operatorname{lastRoot} \operatorname{P} = \operatorname{Finset.max} ' (\operatorname{roots} \operatorname{P}) (\operatorname{roots_{nonempty}} \operatorname{P})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.lastRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is (roots P).max' (roots_nonempty P).

**Definition 1.4 (SingletonPrefix).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{a} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{SingletonPrefix} \operatorname{P} \operatorname{a} \iff (\forall (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{v} \leq \operatorname{a} \to \operatorname{P.parent} \operatorname{v} = \operatorname{none}) \land (\forall (\operatorname{v} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{a} < \operatorname{v} \to \operatorname{P.parent} \operatorname{v} \neq \operatorname{none})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.SingletonPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is (forall v, v <= a -> P.parent v = none) ∧ (forall v, a < v -> P.parent v ≠ none).

**Definition 1.5 (principalFilterContraction).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{a} : \operatorname{Fin} (\operatorname{n} + 1)) (\operatorname{hP} : \operatorname{SingletonPrefix} \operatorname{P} \operatorname{a}) (\operatorname{x} : \operatorname{Set.Ici} (\operatorname{P} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}))) , \operatorname{Option.map} (\operatorname{fun} (\operatorname{R} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{val}(\operatorname{a})) \mapsto \operatorname{fun} (\operatorname{v} : \operatorname{Fin} (\operatorname{val}(\operatorname{a}) + 1)) \mapsto \operatorname{Option.map} (\operatorname{fun} \operatorname{p} \mapsto \operatorname{val}(\operatorname{p})) (\operatorname{R.parent} \operatorname{v})) (\operatorname{principalFilterContraction} \operatorname{P} \operatorname{a} \operatorname{hP} \operatorname{x} : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{val}(\operatorname{a}))) = \operatorname{Option.map} (\operatorname{fun} (\operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) \mapsto \operatorname{fun} (\operatorname{v} : \operatorname{Fin} (\operatorname{val}(\operatorname{a}) + 1)) \mapsto \operatorname{Option.map} (\operatorname{fun} \operatorname{p} \mapsto \operatorname{val}(\operatorname{p})) (\operatorname{Q.parent} (\operatorname{Fin.castLE} (\operatorname{Nat.\left(\left(succ_{le}\right)_{of}\right)_{lt}} \operatorname{a.isLt}) \operatorname{v}))) (\operatorname{val}(\operatorname{x}) : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.principalFilterContraction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The isomorphism fixes the adjoined top and restricts the parent function to labels 0 through a. Its inverse restores the fixed final tree.

**Theorem 1.6 (filter_iso_singleton_prefix).**

$$\forall (\operatorname{n} \operatorname{m} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) , (\operatorname{Set.Ici} (\operatorname{P} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) \equiv_{o} \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{m})) \to \operatorname{PrincipalFilters.SingletonPrefix} \operatorname{P} (\operatorname{PrincipalFilters.IntervalForest.lastRoot} \operatorname{P}) \land \operatorname{m} = \operatorname{val}((\operatorname{PrincipalFilters.IntervalForest.lastRoot} \operatorname{P}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.filter_iso_singleton_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.7 (PriorityForest).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{parent} : \operatorname{Fin} (\operatorname{n} + 1) \to \operatorname{Option} (\operatorname{Fin} (\operatorname{n} + 1))) (\operatorname{increasing} : \forall (\operatorname{v} \operatorname{p} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{parent} \operatorname{v} = \operatorname{some} \operatorname{p} \to \operatorname{p} < \operatorname{v}) (\operatorname{intervals} : \forall (\operatorname{u} \operatorname{v} \operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1)) , \operatorname{u} \leq \operatorname{v} \to \operatorname{v} \leq \operatorname{w} \to \operatorname{Relation.EqvGen} (\operatorname{fun} (\operatorname{a} \operatorname{b} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{parent} \operatorname{b} = \operatorname{some} \operatorname{a}) \operatorname{u} \operatorname{w} \to \operatorname{Relation.EqvGen} (\operatorname{fun} (\operatorname{a} \operatorname{b} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{parent} \operatorname{b} = \operatorname{some} \operatorname{a}) \operatorname{u} \operatorname{v}) , (\operatorname{PriorityForest.mk} \operatorname{parent} \operatorname{increasing} \operatorname{intervals}) . \operatorname{parent} = \operatorname{parent}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.PriorityForest` (`✓ std3`).

*Citation.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Section 2.1, pp. 3–4: a priority forest (labeled with [n]₀ and with m edges) is a rooted forest (T₀, T₁, …, Tₙ₋ₘ) with all component trees increasing and ordered according to the root's labels, and where for all j<k, every label in Tⱼ is smaller than every label in Tₖ. Thus, the vertex set of each tree is an interval of integers. The parent-function fields use Fin (n + 1), a smaller parent for each non-root, and Relation.EqvGen for connected components.

**Definition 1.8 (PriorityForest / edges).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{PriorityForest} \operatorname{n}) , \operatorname{edges} \operatorname{P} = \{\operatorname{e} : \operatorname{Fin} (\operatorname{n} + 1) \times \operatorname{Fin} (\operatorname{n} + 1) \mid \operatorname{P.parent} \operatorname{e.2} = \operatorname{some} \operatorname{e.1}\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.edges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is {e | P.parent e.2 = some e.1}.

**Definition 1.9 (PriorityForest / forestPartialOrder).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} \operatorname{Q} : \operatorname{PriorityForest} \operatorname{n}) , \operatorname{P} \leq \operatorname{Q} \iff \operatorname{PriorityForest.edges} \operatorname{P} \subseteq \operatorname{PriorityForest.edges} \operatorname{Q}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.forestPartialOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is PartialOrder.lift edges edges_injective.

**Definition 1.10 (Pi).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{Pi} \operatorname{n} = \operatorname{WithTop} (\operatorname{PriorityForest} \operatorname{n})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.Pi` (`✓ std3`).

*Citation.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Section 3.1, p. 4: The underlying set of Π(n) consists of all priority forests labeled with [n]₀, together with an extra element 1̂. The order relation ≤ on Π(n) is defined as follows. Given two priority forests P and P', P ≤ P' if and only if E(P) ⊆ E(P'). On the other hand, 1̂ is set to be the top element of Π(n). Pi uses WithTop and the forest order is inclusion of the displayed edge sets.

**Definition 1.11 (theta).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{theta} \operatorname{n} = \operatorname{Nat.card} \{\operatorname{x} : \operatorname{Pi} \operatorname{n} \mid \exists (\operatorname{m} : \operatorname{Nat}) , \operatorname{m} \leq \operatorname{n} \land \operatorname{Nonempty} (\operatorname{Set.Ici} \operatorname{x} \equiv_{o} \operatorname{Pi} \operatorname{m})\}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.theta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is Nat.card {x : Pi n // ∃ m ≤ n, Nonempty (Set.Ici x ≃o Pi m)}.

**Definition 1.12 (claimTheta).**

$$\operatorname{claimTheta} \iff \forall (\operatorname{n} : \operatorname{Nat}) , 1 \leq \operatorname{n} \to \operatorname{theta} \operatorname{n} = \sum (\operatorname{k} : \operatorname{Nat}) \in \operatorname{Finset.range} (\operatorname{n} + 1) , \operatorname{k.factorial}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.claimTheta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Section 6, item 3, pp. 24–25: We could also modify this question and ask the number θₙ of principal filters of Π(n) (this is, intervals of the form [P, 1̂]) that are isomorphic to Π(m) with m ≤ n. This sequence begins as 2, 4, 10, 34 ,154 ,874, … and seems to be https://oeis.org/A003422, the sequence of left factorials, given by θₙ = ∑ᵢ₌₀ⁿ⁻¹ k!. The printed index is mismatched; the stated data give the sum from k = 0 through n. The encoding permits m = 0 and excludes no forest filter. These are the counting conventions of Lillo and Rosas; the count formulas resolve their final-section questions.

**Definition 1.13 (coreOrderIso).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{x} : \operatorname{Pi} \operatorname{n}) , \operatorname{coreOrderIso} \operatorname{n} \operatorname{x} = \operatorname{Option.map} (\operatorname{fun} (\operatorname{P} : \operatorname{PriorityForest} \operatorname{n}) \mapsto \operatorname{IntervalForestBasic.IntervalForest.mk} \operatorname{P.parent} \operatorname{P.increasing} \operatorname{P.intervals}) \operatorname{x}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.coreOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is (PriorityForest.forestToCoreOrderIso n).withTopCongr.

**Theorem 1.14 (result).**

$$\operatorname{claimTheta}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result` (`✓ std3`). ∎

*Resolves.* `Problems/lillo-rosas-2026-priority-lattice-principal-filters` (proved) by `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lillo-rosas-2026-priority-lattice-principal-filters","declaration_gid":"D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.Pi`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.PriorityForest`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.SingletonPrefix`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.claimTheta`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.coreOrderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.edges`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.filter_iso_singleton_prefix`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.forestPartialOrder`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.lastRoot`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.principalFilterContraction`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.result`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.roots`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.roots_nonempty`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/PrincipalFilters.theta`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/ForestCovers](ForestCovers.md)
