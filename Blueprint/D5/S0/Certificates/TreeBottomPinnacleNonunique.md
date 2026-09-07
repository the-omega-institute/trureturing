# A Tree with Nonunique Bottom Pinnacle Sets

## Abstract

A six-vertex tree has no minimum among its size-three pinnacle sets.

Section 6 of Bozeman, Cheng, Harris, Lasinis and Walker, The Pinnacle Sets of a Graph, arXiv:2406.19562v1, asks one to consider the bottom pinnacle set(s) of trees and determine whether there is a unique bottom element. This module exhibits a six-vertex tree whose size-three pinnacle sets have no minimum.

Figure 10 of that same paper already exhibits a graph with the two bottom size-three pinnacle sets {2,5,6} and {3,4,6}, but that graph contains cycles. The poset is not claimed to be new; what is established here is its realization by a tree. The paper supplies the question and comparison; the declarations below are repository constructions.

No classification for other cardinalities is formalized, and no claim is made about which trees on more vertices behave this way. Fin(6) contains the vertices 0, 1, 2, 3, 4, 5; pinnacle labels are one-based natural numbers.

**Definition 1.1 (The six-vertex graph).**

$$\begin{aligned}tree: \operatorname{SimpleGraph}(\operatorname{Fin}(6)),\\\operatorname{E}(tree) = \{\{0,1\},\{1,2\},\{1,3\},\{1,4\},\{2,5\}\}\end{aligned}$$

*Formalization.* `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed edge set consists of unordered pairs. There are no other edges. IsTree(tree) below is Lean's tree.IsTree.

**Definition 1.2 (Pinnacle labels).**

$$\begin{aligned}\forall label: \operatorname{Fin}(6) \to \operatorname{Fin}(6),\\\operatorname{pinnacleSet}(label) = \{\operatorname{val}(\operatorname{label}(vertex))+1 \mid vertex: \operatorname{Fin}(6),\\\forall neighbor: \operatorname{Fin}(6), \operatorname{Adj}(tree, vertex, neighbor) \Rightarrow \operatorname{label}(neighbor) < \operatorname{label}(vertex)\}\end{aligned}$$

*Formalization.* `D5/S0/Certificates/TreeBottomPinnacleNonunique.pinnacleSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any function label, retain exactly the vertices whose every neighbor has strictly smaller label, then take the finite image under vertex maps to val(label(vertex)) + 1. This definition itself does not require bijectivity; repeated image values are counted only once.

**Definition 1.3 (Attainability by a bijective labeling).**

$$\begin{aligned}\forall pinnacles: \operatorname{Finset}(Nat),\\\operatorname{Attainable}(pinnacles) \iff (\exists label: \operatorname{Fin}(6) \to \operatorname{Fin}(6), \operatorname{Bijective}(label) \land \operatorname{pinnacleSet}(label) = pinnacles)\end{aligned}$$

*Formalization.* `D5/S0/Certificates/TreeBottomPinnacleNonunique.Attainable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bijective is Function.Bijective. The existential quantifier ranges over every bijective labeling, not only the two witnesses exhibited below.

**Definition 1.4 (Coordinatewise comparison).**

$$\begin{aligned}\forall left, right: \operatorname{Finset}(Nat),\\\operatorname{CoordinateLE}(left, right) \iff \operatorname{ForallTwo}(\leq, \operatorname{sort}(\leq, left), \operatorname{sort}(\leq, right))\end{aligned}$$

*Formalization.* `D5/S0/Certificates/TreeBottomPinnacleNonunique.CoordinateLE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sort uses the natural-number less-than-or-equal relation and lists the elements increasingly. ForallTwo denotes Lean's List.Forall₂: the lists have equal lengths and each corresponding pair satisfies the displayed relation.

**Theorem 1.5 (The graph is a tree).**

$$\operatorname{IsTree}(tree)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree_isTree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean proves connectivity by paths from vertex 1, and verifies the edge count required by the finite-tree characterization.

**Theorem 1.6 (Every attainable size-three set is one of four cases).**

$$\begin{aligned}\forall pinnacles: \operatorname{Finset}(Nat), \operatorname{Attainable}(pinnacles) \Rightarrow \operatorname{card}(pinnacles) = 3 \Rightarrow\\(pinnacles = \{2,5,6\} \lor pinnacles = \{3,4,6\} \lor\\pinnacles = \{3,5,6\} \lor pinnacles = \{4,5,6\})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_three_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both hypotheses are essential: pinnacles is attainable and its cardinality is three. Kernel reduction checks all 720 permutations; the proof shows that every bijective labeling appears in that enumeration. This theorem gives a necessary case list, not a classification for any other cardinality.

**Theorem 1.7 (The set {2,5,6} is attainable).**

$$\operatorname{Attainable}(\{2,5,6\})$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_256` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-based label vector in vertex order is [2,3,0,4,5,1]. Lean checks its bijectivity and exact one-based pinnacle set.

**Theorem 1.8 (The set {3,4,6} is attainable).**

$$\operatorname{Attainable}(\{3,4,6\})$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_346` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-based label vector in vertex order is [0,1,4,2,3,5]. Lean checks its bijectivity and exact one-based pinnacle set.

**Theorem 1.9 (A tree without a minimum size-three pinnacle set).**

$$\begin{aligned}\operatorname{IsTree}(tree) \land \neg (\exists least: \operatorname{Finset}(Nat),\\\operatorname{card}(least) = 3 \land \operatorname{Attainable}(least) \land\\\forall other: \operatorname{Finset}(Nat), \operatorname{card}(other) = 3 \Rightarrow \operatorname{Attainable}(other) \Rightarrow \operatorname{CoordinateLE}(least, other))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree_no_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion includes tree.IsTree and denies a least set that has cardinality three, is attainable, and lies coordinatewise below every other attainable cardinality-three set. Such a least set would lie below both exhibited witnesses, but each of the four exhaustive cases contradicts one of these comparisons. The restriction on other is part of the theorem, not an implicit convention.

## References

- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.Attainable`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.CoordinateLE`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_256`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_346`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.attainable_three_cases`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.pinnacleSet`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree_isTree`
- Truth anchor: `D5/S0/Certificates/TreeBottomPinnacleNonunique.tree_no_minimum`
