# Whole-Block Avoidance in a Transitive Linear Incidence Geometry

## Abstract

Transitive finite linear incidence partitions admit a whole block outside each closure.

**Theorem 1.1 (Two uniform incidence counts cannot coexist).**

$$\forall (b : \mathbb{N}) , \forall (m : \mathbb{N}) , \forall (d : \mathbb{N}) , 2 \le b \land 2 \le m \land (b \cdot (d - 1)) = (m - 1) \land (((b + m) - 1) \cdot (d - 1)) = (m - 1) \implies False.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/RankThreeBlockAvoidance.incidence_count_contradiction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the distinct-closure branch, b is the size of an original block, m is the number of blocks, and d is the common number of closures through a point. The two counts are b(d-1)=m-1 and (b+m-1)(d-1)=m-1. If b and m are both at least two, subtracting the equations forces (m-1)(d-1)=0; each factor is then handled by the corresponding positivity hypothesis. This is the arithmetic last step of the geometric avoidance proof below.

**Theorem 1.2 (Each closure avoids an entire original block).**

$$\forall (G : \operatorname{Type}), \forall (P : \operatorname{Type}), \forall (I : \operatorname{Type}), [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(P\right)] [\operatorname{Finite}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{MulAction}\left(G, P\right)] [\operatorname{MulAction}\left(G, I\right)] [\operatorname{MulActionIsPretransitive}\left(G, P\right)] \forall (o : P \to I), \forall (L : I \to \operatorname{Finset}\left(P\right)), ((\forall (i : I), 2 \le \lvert \{x : P \mid \operatorname{o}\left(x\right) = i\} \rvert) \land (\forall (x : P), x \in \operatorname{L}\left(\operatorname{o}\left(x\right)\right)) \land (\forall (g : G), \forall (x : P), \operatorname{o}\left((g \cdot x)\right) = (g \cdot \operatorname{o}\left(x\right))) \land (\forall (g : G), \forall (i : I), \forall (x : P), (g \cdot x) \in \operatorname{L}\left((g \cdot i)\right) \iff x \in \operatorname{L}\left(i\right)) \land (\forall (i : I), \forall (j : I), (\operatorname{L}\left(i\right) \neq \operatorname{L}\left(j\right)) \implies \forall (x : P), \forall (y : P), ((x \in \operatorname{L}\left(i\right)) \land (y \in \operatorname{L}\left(i\right)) \land (x \in \operatorname{L}\left(j\right)) \land (y \in \operatorname{L}\left(j\right))) \implies x = y) \land (\exists (i : I), \exists (j : I), \operatorname{L}\left(i\right) \neq \operatorname{L}\left(j\right))) \implies \forall (i : I), \exists (j : I), \forall (x : P), (\operatorname{o}\left(x\right) = j) \implies \neg (x \in \operatorname{L}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/RankThreeBlockAvoidance.exists_block_disjoint_of_transitive_linear_closures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite point type is P and the finite block-label type is I. The owner map o partitions P into its fibers, each of size at least two. The finite set L(i) contains the entire fiber over i. A group G acts transitively on points, acts on block labels, and preserves both ownership and closure incidence. Distinct assigned closures have at most one common point, and at least two assigned closures differ. The conclusion keeps the original owner fibers: for every i, some whole fiber over j misses L(i).

Suppose a closure meets every original block. Point transitivity and equivariance first give transitivity on block labels, then transport this intersection property to every closure. If two original blocks have the same closure, a different closure must meet both blocks. The two intersection points have different owners, contradicting the one-point intersection bound. This treats repeated closures without identifying or replacing the original blocks.

Closures are therefore distinct under the supposition. Every off-diagonal block-closure intersection and every pair of distinct closures has exactly one point. Counting the owner fibers inside L(i) gives its size b+m-1, where b is the size of the fiber over i and m is the number of block labels. The group action gives a bijection between the incident closure labels at any two points, so their common degree is d. Double counting incidences with all closures except L(i), first over the original fiber and then over L(i), gives b(d-1)=m-1 and (b+m-1)(d-1)=m-1. The arithmetic result above contradicts these equations. Multiple incidences at the same point are counted separately; distinct intersections need not be distinct points.

For a simple rank-three matroid with rank-two partition blocks, the intended interpretation is L(i)=cl(B(i)). Applying this theorem requires proofs that the matroid ground set and invariant partition induce the stated finite actions and owner map, that automorphisms preserve these closures, that simple rank-two closures satisfy the one-point intersection bound, that rank three excludes a single common closure, and that rank-two blocks have at least two points. Those matroid bridges are not proved here. The conditional incidence theorem does not assert the full matroid statement or the subsequent field-rank comparison.

## References

- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.exists_block_disjoint_of_transitive_linear_closures`
- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.incidence_count_contradiction`
