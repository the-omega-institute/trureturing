# Exact rational laws from strictly positive five-mode tables

## Abstract

Strict five-mode rational networks have exactly graph-independent supports, with arbitrary positive masses.

**Definition 1.1 (Strict positivity on all five allowed tuples).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Strict`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Strict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Strict is a property of the existing Table: its value is positive at every tuple of A. The full eight-entry table is nonnegative, sums to one, and vanishes outside A by the Table structure. Thus its support is exactly 000, 100, 010, 110 and 001, including entries that a repeated scope never visits.

**Definition 1.2 (Labelled undirected graphs with loops).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.LoopGraph`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.LoopGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A LoopGraph on n coordinates has a symmetric adjacency relation on Fin n. Diagonal adjacency is permitted. No irreflexivity assumption discards loops.

**Definition 1.3 (Independent Boolean words).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Independent`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Independent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word a is independent when a(i) and a(j) are not simultaneously one at any adjacent pair i,j. A loop forces its coordinate to zero. The all-zero word is always independent; with no edges every word is independent.

**Definition 1.4 (The exact finite representation predicate).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Representable`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Representable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Representable P means that some finite natural hidden count m and factor count k admit an existing Network n m k. Each factor's existing Table is Strict, the existing partition is positive, and its existing normalized law equals P at every visible assignment. Factors have ordered triples of actual variables in Fin n plus Fin m, with repetition permitted. The weight is the finite product, including the empty product one; the marginal sums every hidden assignment.

**Theorem 1.5 (Strict canonical pin table).**

$$\operatorname{Strict}\left(\mathrm{pinTable}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.pin_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical full pinTable is positive at every allowed tuple of A.

**Definition 1.6 (The induced visible exclusion graph).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.induced`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.induced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a canonical Network, the induced LoopGraph joins original visible coordinates whenever they occur as the first or second and third terminals of one factor, in either direction. Scope repetitions retain diagonal edges.

**Theorem 1.7 (Partition positivity and exact visible support).**

$$\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall net \in \operatorname{Network}\left(n, m, k\right),\; {\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Strict}\left(\operatorname{table}\left(\operatorname{factor}\left(net, j\right)\right)\right)} \Rightarrow {{0 < \operatorname{partition}\left(net\right)} \land {\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; {0 < \operatorname{law}\left(net, a\right)} \Leftrightarrow {\operatorname{Independent}\left(\operatorname{induced}\left(net\right), a\right)}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every canonical Network whose complete factor tables are Strict has a positive partition. At every visible assignment its normalized law is positive exactly when the assignment is independent in the induced LoopGraph. Arbitrary hidden counts and empty factor sets are included.

**Theorem 1.8 (All rational masses on every independent support).**

$$\forall n \in \mathrm{Nat},\; \forall P \in ((\operatorname{Fin}\left(n\right)) \to \mathrm{Bool}) \to \mathrm{Rat},\; {{\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; 0 \le \operatorname{P}\left(a\right)} \land {\sum_{a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool}} \operatorname{P}\left(a\right) = 1}} \Rightarrow {{\exists m \in \mathrm{Nat},\; \exists k \in \mathrm{Nat},\; \exists net \in \operatorname{Network}\left(n, m, k\right),\; {\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{Strict}\left(\operatorname{table}\left(\operatorname{factor}\left(net, j\right)\right)\right)} \land {{0 < \operatorname{partition}\left(net\right)} \land {\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; \operatorname{law}\left(net, a\right) = \operatorname{P}\left(a\right)}}} \Leftrightarrow {\exists K \in \operatorname{LoopGraph}\left(n\right),\; \forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; {0 < \operatorname{P}\left(a\right)} \Leftrightarrow {\operatorname{Independent}\left(K, a\right)}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every nonnegative rational law P on the Boolean n-cube with total one, P has an exact finite representation by strict five-mode factors if and only if its positive support is the independent-word family of some labelled undirected graph with loops. In particular this includes every n at least one, every positive rational mass assignment on such a support, isolated coordinates, loops and the singleton all-zero support. The same statement also holds for the zero-dimensional cube.

For necessity, each factor on actual variables (u,w,t) excludes the pairs (u,t) and (w,t). Keep both directions and every diagonal exclusion to obtain a symmetric graph on the visible coordinates. A positive full weight satisfies every exclusion. Conversely an independent visible word extends positively by assigning zero to every hidden variable. Nonnegative finite sums detect a positive summand. The complete zero assignment proves that the partition is positive, even with no factors and with arbitrary finite hidden count.

The construction uses the existing normalized pin table, the indicator of A divided by five, on (o,o,o) for a fresh hidden variable o. This forces o to zero internally. Its scope (u,u,w) enforces the exclusion of simultaneous ones. The existing unary table has values one at 000, 100, 010 and 001, value c at 110, and zero elsewhere, divided by four plus c. On (u,u,o) it supplies activities one and c. Every c used here is positive.

A positive binary table B is realized by the full ternary table with value B(x,y) at (x,y,0), value one at 001, and zero elsewhere, divided by one plus the sum of the four B entries. Its scope is (u,v,o). All five allowed entries are positive and all eight entries are included in normalization. Binary weights and unary activities below are implemented by these actual ternary factors.

For a positive rational full-cube table w, choose a positive rational L so that r(a)=Lw(a)-1 is positive for every a. Define M(e)(a,s) as the product over coordinates of one when a(i)=s(i) and e otherwise. At zero this rational matrix is the identity. Continuity of the determinant and inverse gives a rational e strictly between zero and one for which M(e) is invertible and c=M(e) inverse times r has every entry positive. Thus one plus the sum over s of c(s)M(e)(a,s) equals Lw(a) exactly. Continuity establishes a single rational choice; the network uses no limiting operation.

Introduce one hidden selector for each full visible word s. Pairwise exclusion factors permit exactly the all-zero selector assignment and assignments with exactly one selected word. Its activity is c(s). The binary table between selector s and visible coordinate i is one when the selector is zero, and otherwise is one when a(i)=s(i) and e when they differ. Comparing entries with the fixed index s(i) does not complement a scope variable. The hidden pin and selector assignments give respectively one and c(s)M(e)(a,s), times the same positive normalization scalar. Every other hidden assignment violates a pin or an exclusion and has weight zero. The full hidden sum is therefore computed over its entire assignment space.

Given graph-independent support, extend P to the positive full-cube table w that equals P on independent words and one elsewhere. Add a visible exclusion factor for every adjacency pair, including diagonal pairs; nonedges can use the internally pinned scope. Their product is the independent-word indicator times a positive constant. The marginal is exactly C L P for a positive rational C. Summing P gives partition C L, and final normalization recovers P. Finite equivalences number the actual hidden variables and factors using the existing Network constructor.

The conclusion concerns globally normalized rational potentials. It supplies neither an efficiency bound nor a causal sampling interpretation. Constants, complemented scope literals, supplied equality or disequality, external unary or multivariate factors, and limits are absent from the factor language. The matrix argument and selector construction establish arbitrary weights as well as support.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Independent`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.LoopGraph`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Representable`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.Strict`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.induced`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.necessity`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.pin_strict`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.result`
- Dependency: [D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization](RationalZeroRealization.md)
