# A sublattice obstruction in the priority lattice

## Abstract

The priority lattice is not always sublattice dismantlable.

**Definition 1.1 (Closure under ambient extrema).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.AmbientClosed`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.AmbientClosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

For every two members x and y of a set, an ambient greatest lower bound and an ambient least upper bound must exist and belong to the set. Bounds are tested against every element of the ambient partial order. This expresses binary sublattice closure without choosing operations or requiring the ambient bottom and top to belong to the subset.

**Definition 1.2 (Recursive disjoint sublattice subdivision).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.Dismantlable`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.Dismantlable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

A singleton is dismantlable. A closed set is dismantlable when it is the disjoint union of two nonempty closed sets, each dismantlable by the same rule. An inductive proof is exactly a finite binary subdivision tree ending in singletons. The word subdivision in Section 6, item 4 is read as a partition, consistently with the cited Sage implementation. An overlapping-cover interpretation is outside this statement.

**Lemma 1.3 (Restriction to a nonempty sublattice).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.hereditary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.hereditary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Intersect a dismantling tree with a nonempty ambient sublattice. Uniqueness of greatest lower bounds and least upper bounds makes every intersection closed. If one child intersection is empty, retain the other child; if both are nonempty, retain their disjoint split. Singleton leaves restrict to singleton leaves. Thus every nonempty sublattice of a dismantlable set is dismantlable.

**Lemma 1.4 (Transport by the source order isomorphism).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.dismantlable_image`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.dismantlable_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

An order isomorphism transports all ambient extrema, closed sets, disjoint partitions, nonemptiness and recursive subdivision trees. In particular the existing coreOrderIso at n = 6 connects the literal PriorityForest carrier and its adjoined top to the IntervalForest carrier used below.

**Definition 1.5 (Sixteen forests and the actual top).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.embed`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.embed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Put F = {(0,1),(0,2),(3,4),(3,5)}. The sixteen forests are F, A_i = F union {(i,3)}, B_j = F union {(3+j,6)}, and C_ij = F union {(i,3),(3+j,6)}, with i and j in {0,1,2}. The code some(a,b), with a and b in Fin 4, selects no extra edge when a coordinate is zero and selects the corresponding parent when it is positive. Code none denotes the actual adjoined ambient top. The parent functions satisfy increasingness and the local interval condition of forestOfLocal; hence these are actual source forests. Reading the parents at vertices 3 and 6 proves injectivity, giving seventeen distinct elements.

**Lemma 1.6 (All ambient greatest lower bounds).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.meet_extremum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.meet_extremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

On two forest codes, retain each optional extra parent exactly when both forests contain it. Their edge intersection is one of the sixteen valid forests. Parent preservation proves it is below both forests and above every common lower bound in the whole ambient order. Meeting with top returns the other argument. Thus every one of the seventeen-by-seventeen ambient meets lies in the displayed set.

**Lemma 1.7 (All ambient least upper bounds).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.join_extremum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.join_extremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Compatible optional parents combine to give another displayed valid forest. Its edges are the union, so it is below every common upper bound. Incompatible codes give two different parents to vertex 3 or vertex 6. No ambient forest can contain both assignments, and the only common upper bound is the actual adjoined top. Joining with top returns top. These conclusions follow from the defining order and do not require a general intersection or union formula for arbitrary priority forests.

**Lemma 1.8 (The incidence obstruction has no first split).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.no_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.no_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The seventeen-element sublattice is the incidence lattice of K3,3. If F and top occupy different parts, C_00, C_11 and C_22 have pairwise meet F and join top, so neither part can hold two of them. If both bounds occupy one part, the other part has at most one atom and one coatom. A lone coatom is forced by the join of its two endpoint atoms. If that other part contains an atom, at least two of its three incident coatoms occupy the first part and their meet forces the atom there too. The formal finite Boolean argument uses exactly these ambient operation tables and excludes every nontrivial two-part sublattice partition.

**Definition 1.9 (The whole universal question).**

$$claim \iff \forall n \in \mathbb{N} , 1 \leq n \to \operatorname{Dismantlable} (\operatorname{univ} : \operatorname{Set} (\operatorname{Pi} n))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

Lillo and Rosas ask whether Pi(n) is sublattice dismantlable for every positive n, after reporting Sage checks for n from 1 through 5. Pi is the existing source carrier of all increasing interval forests on labels 0 through n, ordered by edge inclusion, with an extra top.

**Theorem 1.10 (A negative answer at n = 6).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result` (`✓ std3`). ∎

*Resolves.* `Problems/lillo-rosas-2026-priority-lattice-sublattice-dismantling` (refuted) by `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lillo-rosas-2026-priority-lattice-sublattice-dismantling","declaration_gid":"D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

If the actual Pi(6) were dismantlable, order transport followed by restriction would dismantle its displayed seventeen-element ambient sublattice. That sublattice has neither a singleton carrier nor a first split, a contradiction. The positive parameter 6 therefore refutes the entire universal question. The abstract incidence obstruction and the existing principal-interval results are background; the source-specific conclusion follows from the explicit forests and ambient extrema. No assertion about the authors' historical Sage version or an overlapping-cover meaning is needed, and no exhaustive publication priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.AmbientClosed`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.Dismantlable`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.claim`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.dismantlable_image`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.embed`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.hereditary`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.join_extremum`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.meet_extremum`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.no_partition`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/PrincipalFilters](PrincipalFilters.md)
