# Ancestor Area and Complete Leaf Intervals

## Abstract

An interval sum of native ancestor coordinates equals its binomial lower bound exactly at an actual complete subtree occurrence.

Source is FreeMagma Bool, the existing nonempty ordered binary tree algebra. Leaves are numbered from one in the actual left-to-right leaf-address enumeration. False in an address means left and true means right. Labels need not be distinct, and no substitution-image restriction is imposed.

**Definition 1.1 (Actual gap coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.coordinates`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf has the empty coordinate list. For pair(l,r), the list is coordinates(l), followed by length(l)*length(r), followed by coordinates(r). Its entries are A(i) at gaps i=1,...,length(t)-1: the root gap follows all left-child gaps, and its coordinate is the product of the actual child leaf counts.

**Definition 1.2 (Consecutive gap sum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.area`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.area` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

area(t,a,b) is the sum of take(b-a,drop(a-1,coordinates(t))). Thus it is exactly the sum of A(i) for i=a,...,b-1. At a=b the sum is empty and equals zero.

**Definition 1.3 (Ambient position of an occurrence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.offset`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

offset(t,u) counts leaves before the addressed subtree. The empty root address has offset zero. A left step preserves the child offset; a right step adds the entire left-child leaf count. Navigation past a leaf has no subtree and cannot satisfy CompleteSubtree.

**Definition 1.4 (Actual complete subtree interval).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.CompleteSubtree`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.CompleteSubtree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CompleteSubtree(t,a,b) means that there are an actual address u and tree s with subtree(u,t)=some(s), a=offset(t,u)+1, and b=offset(t,u)+length(s). In addition, take(b-a+1,drop(a-1,leaves(t))) equals the list leaves(s) with u prefixed to every address. This identifies every ambient leaf occurrence in order, rather than only its label, subtree value, or cardinality.

**Theorem 1.5 (The Complete Interval Bound and Equality Criterion).**

$$\forall t: \operatorname{Source}, (\forall a: \mathbb{N}, (\forall b: \mathbb{N}, ((1 \leq a) \implies ((a \leq b) \implies ((b \leq \operatorname{length}\left(t\right)) \implies ((\operatorname{choose}\left(b - a + 1, 2\right) \leq \operatorname{area}\left(t, a, b\right)) \land ((\operatorname{area}\left(t, a, b\right) = \operatorname{choose}\left(b - a + 1, 2\right)) \iff (\operatorname{CompleteSubtree}\left(t, a, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.ancestor_area_interval` (`✓ std3`). ∎

*Citation.* Jean-Louis Loday (2002). *Realization of the Stasheff polytope*. URL: <https://arxiv.org/abs/math/0212126v1>.

*Commentary.*

For every Source tree and every 1<=a<=b<=length(t), put k=b-a+1. The ancestor-area sum is at least choose(k,2), with equality if and only if the interval consists of all leaves of an actual addressed subtree. This includes all prefixes, suffixes, singleton intervals, the full tree, and the one-leaf tree, regardless of repeated labels.

Split the interval at the root gap. An interval contained in one child inherits that child's bound and subtree occurrence. For a crossing interval, let p,q be the child leaf counts and x,y the positive selected leaf counts on the two sides. The two child interval sums contribute at least choose(x,2) and choose(y,2), and the root contributes pq>=xy. The identity choose(x+y,2)=choose(x,2)+choose(y,2)+xy gives the bound. Equality implies pq=xy; since 0<x<=p and 0<y<=q, this forces x=p and y=q, so the interval is the root's whole leaf interval. Conversely the whole interval has equality by the same recurrence.

Address navigation also gives the exact ambient ordered leaf slice of each occurrence. Left steps prefix false; right steps prefix true and skip the left child's whole leaf list. Hence the equality criterion retains occurrence identity even for identical subtrees at different addresses.

Loday's original coordinate construction and proper-block Proposition 2.6 use n=m-1, r=a-1, d=b-a, x(i)=A(i), and S(d)=choose(b-a+1,2). Lemma 2.5 gives the full-tree total. Singleton and one-leaf cases have zero gaps and correspond to actual leaves.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.CompleteSubtree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.ancestor_area_interval`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.area`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.coordinates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.offset`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](../ActualJointResponseCostCore.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
