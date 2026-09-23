# Disjoint-union uniqueness and intersecting links

## Abstract

Let H be a finite family of subsets of an arbitrary finite vertex type with n vertices. The definitions apply to every such H; three-uniformity, DUF, and the cap are assumptions only where stated. Unordered pairs range over the whole ground set, so absent pairs are included. The pair extension relation is directed; a common link is obtained by transposing that relation.

**Definition 1.1 (All ground pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.pairs`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ground pairs are all two-element subsets of the finite vertex type. Their number is binom(n,2), independently of which pairs occur in H.

**Definition 1.2 (Uniqueness of disjoint unions).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.DUF`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.DUF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Whenever A, B, C, and D belong to H, A and B are disjoint, C and D are disjoint, and their unions agree, either A=C and B=D or A=D and B=C.

**Definition 1.3 (Exact neighborhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.neighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(p) consists of vertices x outside p for which inserting x into p gives a member of H. For pairs in a triple family, uniformity already excludes vertices of p.

**Definition 1.4 (Common links).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.common`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.common` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(q) consists of ground pairs p such that q is contained in N(p). The containment goes in this direction and is not asserted to be symmetric.

**Definition 1.5 (Exact neighborhood fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.fiber`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.fiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(S) consists of all ground pairs whose neighborhood is exactly S.

**Definition 1.6 (Maximum pair codegree four).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.CapFour`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.CapFour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ground pair, including every absent pair, has at most four neighbors.

**Definition 1.7 (Stars).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.star`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.star` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write cA for the star with center c and leaf set A, consisting of the sets {c,x} for x in A. The definition permits any c and A; the structural conclusions explicitly exclude c from A, so their star edges are two-element sets.

**Definition 1.8 (Intersecting edge families).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.Intersecting`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFStructure.Intersecting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every two members of the edge family have nonempty intersection.

**Theorem 1.9 (Star or triangle).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.intersecting_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFStructure.intersecting_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty finite intersecting family of two-element sets is a star or the full pair family on a three-element set. In the star case the center is outside its leaf set and the number of leaves equals the number of edges. A singleton edge may have either endpoint as center.

**Theorem 1.10 (The forbidden common-link matching).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.common_intersecting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFStructure.common_intersecting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and every two-element set q, K(q) is intersecting. Two disjoint common-link edges would give two unequal unordered decompositions of the same union into members of H.

**Theorem 1.11 (Equivalence for triple families).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.duf_iff_common_intersecting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFStructure.duf_iff_common_intersecting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-uniform family, DUF is equivalent to every two-vertex common link being intersecting. In the reverse direction, unequal decompositions of a six-element union give a two-plus-one intersection pattern and hence a disjoint pair of common-link edges.

**Theorem 1.12 (Four-edge common links).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.common_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFStructure.common_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and CapFour, every two-element set q has card(K(q))<=4. If card(K(q))=4, there are a center c and a four-element set S with c outside both q and S, K(q)=cS, and N({c,u})=S for every u in q.

**Theorem 1.13 (Four-neighborhood fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFStructure.fiber_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFStructure.fiber_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and CapFour and each four-element set S, F(S) is intersecting and has at most four edges. If F(S) is nonempty, either F(S)=cA with c outside A and S, A disjoint from S, card(A)=card(F(S)), and A contained in N({c,s}) for every s in S, or F(S) is the full pair family on a three-element set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.CapFour`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.DUF`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.Intersecting`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.common`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.common_intersecting`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.common_structure`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.duf_iff_common_intersecting`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.fiber`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.fiber_structure`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.intersecting_classification`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.pairs`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFStructure.star`
