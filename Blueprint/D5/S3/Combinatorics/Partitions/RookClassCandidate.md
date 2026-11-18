# The exact weighted-root candidate and its fiber assembly

## Abstract

The registered weighted-root sum is evaluated on a finite disjoint family; its identification with the full native rook class remains open.

**Definition 1.1 (Ordered source padding).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.sourcePadding`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.sourcePadding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the existing lOperator to the arbitrary normalized input board, retaining its ordered top-down nonempty level totals and its explicit empty-board extension. Prepend zeros to the requested common length. The padding theorem derives the length bound from literal source cells and does not assume rook-number preservation.

**Definition 1.2 (The registered root multiset).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.seedRoots`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.seedRoots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero-based position i take mi minus the corresponding entry of sourcePadding, in the integers. The common-padding theorem proves that every registered length has exactly that many entries and the first root is zero.

**Definition 1.3 (Fully evaluated fiber weights).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.weight`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return zero if any target entry is nonpositive. Otherwise use the existing count recurrence with r=m-1, the reversed target list and its first bottom-up entry U, defaulting to zero for the empty list. The recurrence sums over v from zero through U, uses the guarded coefficient of the q-Pascal Gaussian polynomial in transition, and has empty-list value one. This is the exact evaluated weight of the registration. It is an ordinary count of shapes, not the file-placement weight in the paper's separate weighted question.

**Definition 1.4 (The fixed candidate).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.Q`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum weight(m,board(m,a)) over the finite subtype of distinct admissible root indices of seedRoots(m,N,B). A normalized representative is used exactly once. This definition enumerates root-multiset sequences and evaluates the finite Gaussian recurrence; it does not enumerate the original class of Ferrers boards. The first position, nonnegativity, Ferrers order and conditional floor test are all retained in indices.

**Definition 1.5 (The native class cardinality).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.K`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is Nat.card of the class defined by equality of every literal rook-subset count. The separate rookClass_finite theorem proves this carrier finite using an explicit injection into the powerset of the area-square. Thus the infinite-carrier convention of Nat.card is not used to assert class finiteness.

**Definition 1.6 (The unproved universal target).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.UniversalFormula`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.UniversalFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UniversalFormula asserts K(m,B)=Q(m,N,B) for every positive m, every normalized positive-column input including the empty board, and every N at least area(B)+1. This declaration defines a proposition. No proof of it or its negation is provided here. In particular, the fiber-assembly theorem below does not identify its RootFamily with the native rook class.

**Definition 1.7 (The actual root-selected source family).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.RootFamily`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.RootFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A normalized source shape belongs precisely when its actual lOperator value equals board(m,a) for some index a of the fixed seed z. The quantifier ranges over the same arbitrary-width, arbitrary-height positive-column shapes as the native class. It imposes no singleton restriction on these original source shapes.

**Definition 1.8 (A disjoint union on the same actual shapes).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookClassCandidate.rootFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookClassCandidate.rootFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum over root indices of the actual lOperator fibers maps to RootFamily by forgetting the index. Injectivity of root reconstruction forces equal indices whenever the underlying source shape agrees. Surjectivity uses the very witness of family membership. This is a bijection of the same shapes, with no replacement by independently achievable marginal counts.

**Theorem 1.9 (Finite family and evaluated ordinary cardinality).**

$$\forall m \in Nat,\; 0 < m \Rightarrow \left(\forall n \in Nat,\; \forall z \in \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; \operatorname{Finite}\left(\operatorname{RootFamily}\left(m, z\right)\right) \land (\operatorname{int}\left(\operatorname{card}\left(\operatorname{RootFamily}\left(m, z\right)\right)\right) = \operatorname{sumWeights}\left(m, z\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassCandidate.rootFamily_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every lOperator fiber is finite: the existing operatorFiberEquiv and the publicly reusable original sourceShapeEquiv transport it to ShapeFiber, then normalizedPaddingEquiv transports it to the existing finite NativeFiber. Invalid positive-target data give an empty fiber. The finite index therefore gives a finite dependent sum and a finite RootFamily. Nat.card_sigma and the direct application of BarreseSourceNormalization.lOperator_count evaluate every fiber with the exact guarded recurrence. In the displayed formula, sumWeights(m,z) denotes the sum over a in indices(m,z) of weight(m,board(m,a)); board is read as its underlying positive list. Applying this theorem to z=seedRoots(m,N,B) gives cardinality Q for RootFamily, while the native-class identification remains open.

**Theorem 1.10 (Every registered common length).**

$$\forall m \in Nat,\; 0 < m \Rightarrow \left(\forall b \in PositiveColumns,\; \forall n \in Nat,\; \operatorname{area}\left(b\right) + 1 \le n \Rightarrow \left(\operatorname{length}\left(\operatorname{lOperator}\left(m, b\right)\right) < n \land (\operatorname{length}\left(\operatorname{sourcePadding}\left(m, n, b\right)\right) = n \land (\operatorname{head}\left(\operatorname{sourcePadding}\left(m, n, b\right)\right) = \operatorname{some}\left(0\right) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{val}\left(i\right) = 0 \Rightarrow \operatorname{seedRoots}\left(m, n, b, i\right) = 0)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookClassCandidate.candidate_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive m, arbitrary normalized B and N at least area(B)+1, lOperator(m,B) has length below N, sourcePadding has length N and a zero head, and seedRoots is zero at its first coordinate. To bound the number of levels, inspect the last nonempty level. Its positive total supplies an actual occupied cell in some column. That column's height is at most the area and exceeds m times the level index, so the number of nonempty levels is at most the area. This includes the empty board without an extra premise.

The first unresolved mathematical interface is the level-total factorization for the native rookCount on every arbitrary input: the sum of r(k,m,B) times the m-step falling factorial of length N-k must equal the product over i of X minus seedRoots(m,N,B,i). The source is Theorem 26 of arXiv:1508.05944v1; its proof uses the arbitrary-board reduction through Lemmas 3 and 5 and singleton factorization. Those literature statements have not been imported as assumptions. A complete result still needs this native bridge or an equivalent bijection, the complete singleton image and inverse, area preservation of the actual l-operator, and all-length class identification. The root-selected family count and finite probes do not prove any of those missing interfaces. The exact full target remains issue #31465.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.K`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.Q`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.RootFamily`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.UniversalFormula`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.candidate_padding`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.rootFamily_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.rootFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.seedRoots`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.sourcePadding`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookClassCandidate.weight`
- Dependency: [D5/S3/Combinatorics/Partitions/RookRootIndex](RookRootIndex.md)
