# Finite Hereditary Patterns in Actual Tree Images

## Abstract

Actual third-substitution images realize every finite hereditary information-leaf pattern at equal composition.

Sources are complete nonempty ordered binary trees with alpha and beta leaves. The native substitution rho sends alpha to beta and beta to (beta,alpha), preserving every pairing. Addresses are finite root-first Boolean lists: false denotes left, true denotes right. The original endpoint observation reports leafAlpha, leafBeta, branch or absent, including at the root and after a path has passed a leaf. Composition c records the two leaf counts.

**Definition 1.1 (Three column entries).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Block`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries a, u and v name the complete blocks A, U and V.

**Definition 1.2 (Literal block preimages).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.preimage`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.preimage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The preimages are alpha, ((alpha,alpha),beta) and ((alpha,beta),alpha), respectively.

**Definition 1.3 (Actual image blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.block`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each block is rho applied three times to its literal preimage. Their compositions are (1,2), (4,7) and (4,7).

**Definition 1.4 (Indexed information leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Delta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delta(P,S) consists of addresses that are leaves of every indexed source in S and carry alpha in at least one row and beta in at least one row. Distinct indices may name the same tree.

**Definition 1.5 (Residual two-block information).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is Delta for U and V. It contains the address LRLR.

**Definition 1.6 (Contributing columns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Mixed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mixed(X,S) means no row in S contains A and at least one row contains each of U and V.

**Definition 1.7 (Right-comb context).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.B_T`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.B_T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(n,X) has n+1 holes and no literal leaves. B(0,X)=X(0); B(n+1,X) pairs X(0) with the context on the remaining entries.

**Definition 1.8 (Hole addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.hole`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.hole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hole addresses follow the left-to-right leaf order. For one hole the address is empty; otherwise each initial hole is reached by right steps followed by left, and the last is reached entirely by right steps.

**Definition 1.9 (Full address decomposition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.locate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.locate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

locate(n,w) is none when w ends at an internal context node. Otherwise it is some(j,v), where w=hole(n,j)++v. The suffix may be empty or continue beyond a block leaf.

**Definition 1.10 (Downward closure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Hereditary`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Hereditary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hereditary(K) means every subset of every member of K is itself a member.

**Definition 1.11 (Maximal faces).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.maximalFaces`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.maximalFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the set of all inclusion-maximal members of K.

**Definition 1.12 (Face columns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.FaceColumn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.FaceColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An original column is a pair (F,k), with F a maximal face and k in F.

**Definition 1.13 (Face table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.faceEntry`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.faceEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry in row i and column (F,k) is V for i=k, U for i in F other than k, and A outside F.

**Definition 1.14 (Original row counts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.rowCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.rowCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rowCount(K,i) counts the original columns whose face contains i.

**Definition 1.15 (Maximum row count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.M`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(K) is the maximum original row count over all indices, with zero for an empty index set.

**Definition 1.16 (Private padding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.PaddingColumn`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.PaddingColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row i receives M(K)-rowCount(K,i) private padding columns.

**Definition 1.17 (Complete column set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Column`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete column set is the disjoint union of original columns and private padding columns.

**Definition 1.18 (Padded table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.entry`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A padding column contains U in its owner's row and A elsewhere; original entries retain their face-table values.

**Theorem 1.19 (Full reports and hereditary realization).**

$$(\forall n, X, w, (\operatorname{out}\left(\operatorname{B}\left(n, X\right), w\right) = \operatorname{read}\left(n, X, w\right))) \land (\forall n, w, ((\operatorname{locate}\left(n, w\right) = none) \iff (\exists j, r, ((\neg(r = empty)) \land (\operatorname{hole}\left(n, j\right) = \operatorname{concat}\left(w, r\right)))))) \land (\forall m, n, X, S, w, ((w \in \operatorname{Delta}\left(\operatorname{Bblocks}\left(n, X\right), S\right)) \iff (\exists j, v, ((w = \operatorname{concat}\left(\operatorname{hole}\left(n, j\right), v\right)) \land (\operatorname{Mixed}\left(\operatorname{Xj}\left(X, j\right), S\right)) \land (v \in D))))) \land (\forall n, j, k, v, u, ((\operatorname{concat}\left(\operatorname{hole}\left(n, j\right), v\right) = \operatorname{concat}\left(\operatorname{hole}\left(n, k\right), u\right)) \implies ((j = k) \land (v = u)))) \land (\forall m, ((2 \leq m) \implies (\forall K, (((\operatorname{Hereditary}\left(K\right)) \land (\operatorname{Singletons}\left(K\right))) \implies (\exists T, N, Q, P, ((1 \leq T) \land (\operatorname{Injective}\left(Q\right)) \land (\operatorname{Injective}\left(P\right)) \land (\forall i, ((\operatorname{rho3}\left(\operatorname{Q}\left(i\right)\right) = \operatorname{P}\left(i\right)) \land (\operatorname{P}\left(i\right) \in \operatorname{I}\left(3\right)) \land (\operatorname{c}\left(\operatorname{Q}\left(i\right)\right) = (T + N, N)) \land (\operatorname{c}\left(\operatorname{P}\left(i\right)\right) = (T + 3 N, 2 T + 5 N)) \land (\operatorname{c1}\left(\operatorname{P}\left(i\right)\right) + \operatorname{c2}\left(\operatorname{P}\left(i\right)\right) = 3 T + 8 N))) \land (\forall i, R, ((\operatorname{rho3}\left(R\right) = \operatorname{P}\left(i\right)) \iff (R = \operatorname{Q}\left(i\right)))) \land (\forall S, ((2 \leq \operatorname{card}\left(S\right)) \implies ((\operatorname{Nonempty}\left(\operatorname{Delta}\left(P, S\right)\right)) \iff (S \in K))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed statement, n,m,T,N are natural numbers, j,k range over Fin(n+1), w,v,u,r are finite addresses, and X in the report clause maps Fin(n+1) to Source. In the information clause X maps Fin(m) times Fin(n+1) to Block, S is a finite subset of Fin(m), and Xj denotes its j-th column. Bblocks(n,X)(i) means B(n,j maps to block(X(i,j))). A concatenation is written concat. Empty denotes the empty address. read(n,X,w) is branch when locate(n,w)=none and is out(X(j),v) when locate(n,w)=some(j,v). K is a finite family of subsets of Fin(m); Singletons(K) means every singleton belongs to K. Q and P map Fin(m) to Source. I(3) is the actual range of the third native substitution. N is the common padded non-A row count, denoted M in the source. c1 and c2 are the two coordinates of composition, card is finite cardinality, and Nonempty means there exists an address.

The report holds at every finite address. Its internal-node case is exactly the strict-prefix condition in the second conjunct. The third conjunct describes all information leaves. The fourth makes contributions from different holes disjoint and also makes the suffix unique. These statements include the empty root address and arbitrary paths extending past block leaves.

Every face lies in a maximal face. Each face column singles out one V row among the U rows of that face. A set of at least two indices has a contributing original column exactly when it is a face of K. Private padding contributes no information leaf on any such set. Padding equalizes the non-A counts without changing this equivalence. The complete trees therefore have the displayed common compositions. The face columns distinguish every pair of rows, and injective native transport gives the unique complete preimages.

Downward-closed finite set families and Helly terminology are classical background. The equal-composition block-table realization and its exact information-leaf equivalence are the tree-specific derivation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.B_T`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Block`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Column`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Delta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.FaceColumn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Hereditary`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.M`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.Mixed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.PaddingColumn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.block`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.entry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.faceEntry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.hole`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.locate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.maximalFaces`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.preimage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.rowCount`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](ActualImageAddressCertificate.md)
