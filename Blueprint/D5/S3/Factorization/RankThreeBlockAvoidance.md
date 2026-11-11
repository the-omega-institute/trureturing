# Whole-Block Avoidance for Transitive Rank-Three Matroids

## Abstract

Transitive finite simple rank-three matroids admit whole-original-block avoidance.

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

The matroid theorem below supplies all these incidence hypotheses from a simple rank-three matroid and its original invariant partition.

**Theorem 1.3 (Original rank-two matroid blocks avoid each closure).**

$$\forall (A : \operatorname{Type}), \forall (G : \operatorname{Type}), [\operatorname{Group}\left(G\right)] \forall (M : \operatorname{Matroid}\left(A\right)), [\operatorname{Finite}\left(\operatorname{Ground}\left(M\right)\right)] [\operatorname{MulAction}\left(G, \operatorname{Ground}\left(M\right)\right)] [\operatorname{MulActionIsPretransitive}\left(G, \operatorname{Ground}\left(M\right)\right)] \forall (blocks : \operatorname{Set}\left(\operatorname{Set}\left(\operatorname{Ground}\left(M\right)\right)\right)), ((\operatorname{eRank}\left(M\right) = 3) \land (\forall (S : \operatorname{Set}\left(\operatorname{Ground}\left(M\right)\right)), (\operatorname{encard}\left(S\right) \le 2) \implies \operatorname{Indep}\left(M, \operatorname{image}\left(\operatorname{v}\left(M\right), S\right)\right)) \land (\forall (g : G), \forall (S : \operatorname{Set}\left(\operatorname{Ground}\left(M\right)\right)), \operatorname{Indep}\left(M, \operatorname{image}\left(\operatorname{v}\left(M\right), \operatorname{actimage}\left(g, S\right)\right)\right) \iff \operatorname{Indep}\left(M, \operatorname{image}\left(\operatorname{v}\left(M\right), S\right)\right)) \land (\forall (x : \operatorname{Ground}\left(M\right)), \exists (B : blocks), (x \in \operatorname{U}\left(B\right)) \land (\forall (C : blocks), (x \in \operatorname{U}\left(C\right)) \implies C = B)) \land (\forall (g : G), \forall (B : blocks), \operatorname{actimage}\left(g, \operatorname{U}\left(B\right)\right) \in blocks) \land (\forall (B : blocks), \operatorname{eRk}\left(M, \operatorname{image}\left(\operatorname{v}\left(M\right), \operatorname{U}\left(B\right)\right)\right) = 2)) \implies \forall (B : blocks), \exists (C : blocks), \operatorname{Disjoint}\left(\operatorname{image}\left(\operatorname{v}\left(M\right), \operatorname{U}\left(C\right)\right), \operatorname{closure}\left(M, \operatorname{image}\left(\operatorname{v}\left(M\right), \operatorname{U}\left(B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/RankThreeBlockAvoidance.exists_original_block_disjoint_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M is a matroid on an arbitrary ambient type A. Its actual ground subtype P consists of the elements of M.E; only P is finite. The map v from P to A is subtype inclusion. The group G, which may be infinite, acts transitively on P. Simplicity means that every subset of P of cardinality at most two has independent image under v. An automorphism means a permutation preserving independence of every actual ground subset: the displayed independence equivalence is precisely this condition. The rank function is mathlib's extended natural rank, with eRank(M)=3.

The collection blocks is a set of subsets of P, and B:blocks denotes an original member of this collection. Write U(B) for its underlying subset of P and V(B)=v[U(B)] for the corresponding original subset of A. The partition hypothesis says each x in P belongs to exactly one B. Invariance says only that g[U(B)] is again in blocks. Here actimage(g,S) means the image of S under x mapped to g acting on x, and image(v,S) is the ordinary set image. No label action, closed blocks, distinct closures or incidence counts are assumed.

Unique membership constructs the owner map. Set image under the point action constructs the action on the original block subtype, and the action laws follow from the point action laws. Membership in an owner fiber is equivalent to membership in that original block. The label type is finite because it is a subtype of the power set of finite P. Rank two and the rank-cardinality bound give at least two points in each owner fiber. Containment follows from the closure axiom. Pulling M back along v gives a matroid on P; pulling it back again along any group permutation gives the same matroid by independence preservation. The comap closure identity therefore proves closure incidence equivariance.

Two distinct ground points form an independent rank-two pair. If both lie in a rank-two block closure, the finite equal-rank closure lemma identifies that closure with the pair closure. Thus distinct assigned closures share at most one point. If every assigned closure were equal, the partition would put all of M.E in a single rank-two closure, contradicting rank three. Applying the incidence theorem now supplies an original owner fiber avoiding each closure. Translating the fiber back by v gives the displayed disjointness for original C. Repeated closures are retained throughout. Uniform block size is unnecessary as an input: point transitivity transports any original block bijectively to any other. The subsequent field-rank comparison is a separate result.

## References

- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.exists_block_disjoint_of_transitive_linear_closures`
- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.exists_original_block_disjoint_closure`
- Truth anchor: `D5/S3/Factorization/RankThreeBlockAvoidance.incidence_count_contradiction`
