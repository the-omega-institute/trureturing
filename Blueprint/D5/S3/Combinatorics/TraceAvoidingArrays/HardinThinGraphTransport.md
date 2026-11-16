# Actual graph reconstruction and continuation induction

## Abstract

Literal six-colour counts of distinct thin square and diagonal strips.

The height is n+1 and the width is k+1. True selects horizontal edges and both diagonals between consecutive rows; false selects horizontal and vertical edges. There are no wraparound edges. The graphs are defined independently. Colours are the three actual elements of Fin 3.

**Definition 1.1 (A pair-label row).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.Row`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Row k is Fin (k+1) to Fin 3.

**Definition 1.2 (Horizontal properness).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.proper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every j in Fin k, the colours at j.castSucc and j.succ differ.

**Definition 1.3 (The actual inter-row bonds).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.compatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

In the diagonal case, p j.castSucc differs from q j.succ and p j.succ differs from q j.castSucc for every j in Fin k. In the square case, p j differs from q j at every column.

**Definition 1.4 (Finite row decision).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableProper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableProper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The decision procedure is the finite universal inequality test defining proper.

**Definition 1.5 (Finite bond decision).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableCompatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The decision procedure unfolds compatible and decides its finite conjunctions and universal inequalities.

**Definition 1.6 (Endpoint equality of a three-cell row).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.boundaryClass`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.boundaryClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For p : Row 2, boundaryClass p is true exactly when p 0 equals p 2. Among proper rows, true is the aba class and false is the abc class.

**Definition 1.7 (The common two-class transfer).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.K`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

K : Bool to Bool to Nat counts target classes in the order true, false. Its entries are 3 at (true,true) and 2 at each other pair. The transition_counts theorem identifies this table with actual proper-row successor counts for either bond choice.

**Theorem 1.8 (Exact successor counts at widths two and three).**

$$(\forall d: \operatorname{Bool}, (\forall p: \operatorname{Row}\left(1\right), ((\operatorname{proper}\left(p\right)) \implies (\sum_{q: \operatorname{Row}\left(1\right)} \operatorname{if}\left((\operatorname{proper}\left(q\right)) \land (\operatorname{compatible}\left(d, p, q\right)), 1, 0\right) = 3)))) \land (\forall d: \operatorname{Bool}, (\forall p: \operatorname{Row}\left(2\right), ((\operatorname{proper}\left(p\right)) \implies (\forall b: \operatorname{Bool}, (\sum_{q: \operatorname{Row}\left(2\right)} \operatorname{if}\left(((\operatorname{proper}\left(q\right)) \land (\operatorname{compatible}\left(d, p, q\right))) \land (\operatorname{boundaryClass}\left(q\right) = b), 1, 0\right) = \operatorname{K}\left(\operatorname{boundaryClass}\left(p\right), b\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For each d : Bool and each proper p : Row 1, exactly three proper rows q satisfy compatible d p q. For each d : Bool, proper p : Row 2 and b : Bool, the number of proper compatible q with boundaryClass q=b is K (boundaryClass p) b. Both clauses quantify over every actual row over Fin 3; d=true selects both diagonals and d=false selects vertical bonds. Finite enumeration proves the two clauses, which determine the continuation recursions.

**Definition 1.9 (Separate square and diagonal graphs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Vertices are Fin (n+1) times Fin (k+1). Adjacency is an oriented horizontal bond, or an oriented vertical or diagonal bond as selected by d, or the reversal of such a bond. Distinct coordinate values prove looplessness.

**Definition 1.10 (Actual colourings as complete row sequences).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.colouringEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.colouringEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The forward map reads the actual colour of every cell. The inverse reconstructs the graph colouring from horizontal properness and every adjacent-row compatibility condition. Both inverse identities hold at all heights and widths.

**Definition 1.11 (The actual row-major index).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.rowMajor`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.rowMajor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The index of cell (i,j) is j+(k+1)i. The codomain has n(k+1)+k+1 vertices, exactly (n+1)(k+1). The index order is precisely the lexicographic row-then-column order.

**Definition 1.12 (The graph on literal scanner indices).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.orderedGraph`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.orderedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

This is stripGraph transported along rowMajor, with no change to its actual cells or bonds.

**Definition 1.13 (The complete six-colour strip).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalStrip`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Each actual rectangular assignment satisfies the existing widthLegal scanner, first-cell zero, horizontal exclusions and the selected vertical or diagonal exclusions. The colour_bond_iff theorem translates each exclusion to unequal beta labels. All positive heights and widths remain in scope.

**Definition 1.14 (Reversible graph and literal-strip normalization).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalEquiv`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Flattening the actual array along rowMajor gives exactly GraphNormalization.Legal on orderedGraph. Earlier flat indices are exactly earlier rows or earlier columns in the same row. This proves every scanner predecessor condition in both directions. The inverse unflattens the actual six-colour word, and both compositions recover every cell.

**Theorem 1.15 (The actual one-row path count).**

$$\forall k: \operatorname{Nat}, 2 \cdot \operatorname{Nat}.\operatorname{card}\left(\operatorname{literalStrip}\left(\operatorname{true}, 0, k + 1\right)\right) = 4^{k} + 2^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.path_result` (`✓ std3`). ∎

*Citation.* John R. Britnell, Mark Wildon (2017). *Bell numbers, partition moves and the eigenvalues of the random-to-top shuffle in Dynkin Types A, B and D*. DOI: [10.1016/j.jcta.2016.12.003](https://doi.org/10.1016/j.jcta.2016.12.003). URL: <https://arxiv.org/abs/1507.04803>.

*Commentary.*

For every k≥0 the one-row path has k+2 vertices and its literal normalized six-colour count L satisfies 2L=4^k+2^k. The proper Fin 3 path count is 3 times 2^(k+1): after the first of three colours, each next vertex has exactly two choices. Decomposing actual row words into their first colour and remaining proper word proves that statement for arbitrary length. The connected graph formula and literalEquiv then give the displayed equality. In source indices this is T(1,w)=(4^(w-2)+2^(w-2))/2 for w≥2. The singleton convention T(1,1)=1 is separate. The one-row paired-colouring identity is attributed to Britnell and Wildon, Bell numbers, partition moves and the eigenvalues of the random-to-top shuffle in Dynkin Types A, B and D, arXiv:1507.04803v1, equation (9) and Proposition 8.1, as recorded in the cited Library note. The two-dimensional strip transport is outside that prior-result attribution; no sequence is defined by this shift.

**Theorem 1.16 (Literal diagonal counts equal the existing square counts).**

$$\forall n: \operatorname{Nat}, \operatorname{Nat}.\operatorname{card}\left(\operatorname{literalStrip}\left(\operatorname{true}, n, 1\right)\right) = \operatorname{HardinA233123SquareStrip}.\operatorname{a}\left(n + 1\right) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{literalStrip}\left(\operatorname{true}, n, 2\right)\right) = \operatorname{HardinA233124SquareStrip}.\operatorname{a}\left(n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.normalized_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

For every positive height, the normalized six-colour diagonal strips at widths two and three have exactly the counts of the existing A233123 and A233124 square-strip owners. Horizontal paths connect each row; an actual diagonal and a horizontal path connect consecutive rows. Column parity gives the diagonal bipartition, while row-plus-column parity gives the square bipartition. A horizontal edge is present at these widths. The connected_count theorem gives P(1)=0 and P(2)=2, so equality of P(3) transfers through the exact graph identity. The literalEquiv maps recover the scanner assignments. Expanding the existing square owners verifies their literal widthLegal predicates. No generating-series proof is duplicated.

**Theorem 1.17 (Equality at every positive height).**

$$\forall n: \operatorname{Nat}, \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}, n, 1\right), \operatorname{Fin}\left(3\right)\right)\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{false}, n, 1\right), \operatorname{Fin}\left(3\right)\right)\right) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}, n, 2\right), \operatorname{Fin}\left(3\right)\right)\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{false}, n, 2\right), \operatorname{Fin}\left(3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

A graph colouring is equivalent to its row sequence: properness supplies horizontal bonds and compatible supplies every selected inter-row bond. Both inverse maps preserve the actual colour at every cell. Splitting a row sequence into its first row and tail identifies its cardinality with the finite continuation recursion. At width two every proper row has three next rows for either graph. At width three the aba and abc classes have common successor counts K=((3,2),(2,2)). These local certificates are checked for all actual Fin 3 row words. Induction on every continuation length proves the shared recursion and hence equality of the actual graph-colouring counts. This is an all-height theorem, not an inference from finite-height agreement. It asserts neither graph isomorphism nor equality for every palette. The normalized_result theorem consumes this equality through the reversible six-colour scanner bridge and the connected-bipartite reduction.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.K`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.boundaryClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.colouringEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableProper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.literalStrip`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.normalized_result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.orderedGraph`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.path_result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.rowMajor`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233123SquareStrip](HardinA233123SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip](HardinA233124SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization](HardinGraphNormalization.md)
