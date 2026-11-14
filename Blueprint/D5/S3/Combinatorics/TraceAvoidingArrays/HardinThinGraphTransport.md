# Actual graph reconstruction and continuation induction

## Abstract

Three-colouring counts of distinct thin square and diagonal graphs.

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

**Definition 1.6 (Separate square and diagonal graphs).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Vertices are Fin (n+1) times Fin (k+1). Adjacency is an oriented horizontal bond, or an oriented vertical or diagonal bond as selected by d, or the reversal of such a bond. Distinct coordinate values prove looplessness.

**Theorem 1.7 (Equality at every positive height).**

$$\forall n: \operatorname{Nat}\left(\right), \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}\left(\right), n, 1\right), \operatorname{Fin}\left(3\right)\right)\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{false}\left(\right), n, 1\right), \operatorname{Fin}\left(3\right)\right)\right) \land \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{true}\left(\right), n, 2\right), \operatorname{Fin}\left(3\right)\right)\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Coloring}\left(\operatorname{stripGraph}\left(\operatorname{false}\left(\right), n, 2\right), \operatorname{Fin}\left(3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

A graph colouring is equivalent to its row sequence: properness supplies horizontal bonds and compatible supplies every selected inter-row bond. Both inverse maps preserve the actual colour at every cell. Splitting a row sequence into its first row and tail identifies its cardinality with the finite continuation recursion. At width two every proper row has three next rows for either graph. At width three the aba and abc classes have common successor counts K=((3,2),(2,2)). These local certificates are checked for all actual Fin 3 row words. Induction on every continuation length proves the shared recursion and hence equality of the actual graph-colouring counts. This is an all-height theorem, not an inference from finite-height agreement. It asserts neither graph isomorphism nor equality for every palette. The row-major six-colour scanner bridge and connected-bipartite reduction remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.instDecidableProper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.stripGraph`
