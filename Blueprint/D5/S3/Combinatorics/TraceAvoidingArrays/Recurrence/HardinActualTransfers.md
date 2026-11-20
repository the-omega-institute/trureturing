# Actual strip states and their continuations

## Abstract

Full transfer matrices for the diagonal and square strip graphs.

**Definition 1.1 (Unrestricted column transfer).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.C`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every h≥0, C h acts on all functions from Fin(h+1) to Fin 3. The entry at current column p and successor q is one exactly when p and q differ across each horizontal bond and both diagonals. There are no within-column bonds.

**Definition 1.2 (Proper word states).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.Word`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every k≥0, the states are length k+1 words in Fin 3 whose adjacent labels differ. There are 3·2^k such words.

**Definition 1.3 (Diagonal and square row transfers).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.wordTransfer`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.wordTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both matrices act on Word k. The diagonal matrix R has entry one exactly when the two opposite diagonals differ at each pair of adjacent positions. The square matrix S has entry one exactly when vertically aligned labels differ. Horizontal edges are enforced by the state type.

**Theorem 1.4 (All column powers).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_power`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every h,m≥0 and current column p, (C h)^m applied to the all-one vector equals the existing columnV m p. The zero-step vector has value one at every column. The successor step sums over the exact cross-bonds.

**Theorem 1.5 (The number of literal column tails).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_continuations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_continuations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed current column and every m≥0, the power vector entry is the number of m-column tails satisfying the immediate cross-bond conditions. The existing column reconstruction supplies the correspondence.

**Theorem 1.6 (Counting the actual strip by columns).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every h,m≥0, summing the vector for m transitions gives the labelled three-colour count of the diagonal strip with height h+1 and width m+1. At width one the graph has no edges and all 3^(h+1) columns contribute.

**Theorem 1.7 (The number of literal row tails).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_continuations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_continuations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either bond rule, every k,m≥0 and fixed proper row p, the power vector entry counts all m-row tails with the required horizontal and inter-row bonds. Every legal successor is one proper word and contributes once.

**Theorem 1.8 (Counting the actual strip by rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both bond rules and every k,m≥0, sum the power vector indexed by all proper words. The result counts labelled three-colourings of the strip with width k+1 and height m+1. The source uses the diagonal matrix for widths at least two and the square matrix at widths two and three.

**Theorem 1.9 (Pullback of a quotient power).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.powerOnes_of_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.powerOnes_of_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite state sets A and B and matrices T and Q over the integers, fix a map c from A to B. If every row of T has total Q(c(a),b) in the fibre over b, then for every a and every m≥0, the a-entry of T^m on ones equals the c(a)-entry of Q^m on ones. Regroup the successor sum into fibres at each induction step. The degree-zero case includes every state.

**Definition 1.10 (Lag convention).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a length-d coefficient list c, the relation with shift b equates T^(b+d) on ones with the sum of c_j times T^(b+d−j) on ones for j from one through d. Diagonal strip columns use b=1 and proper row words use b=0.

Write T(h,n) for the cardinality of the literal normalized diagonal arrays of positive height h and width n. Read the columns in increasing order and recover the colour at (r,j) from position r of column j. The column compatibility test compares the labels at positions r and t whenever their distance is at most one. Reading the rows in increasing order instead recovers the colour at (r,j) from position j of row r. Each row is a proper word, and successive rows compare the two opposite diagonals at every adjacent pair of positions. These inverse maps give the exact graph colourings in either orientation. The unique empty tail gives the all-one vector, and each successor step is multiplication by the same matrix, indexed by current state and then successor state.

Every diagonal strip of width at least two is connected, has an edge and is bipartite by column parity. Horizontal edges link the vertices in each row, and each pair of successive rows is joined by a diagonal. If L counts its labelled three-colourings, the literal normalization is 48 T(h,n) = 2^(hn)(L+6). At width one the strip is edgeless, and 48 T(h,1) = 6^h + 3·4^h + 15·2^h.

For any of the transfer matrices M, let W_M(s) = s·1ᵀ(I−sM)⁻¹1 in the formal power series ring. Its constant coefficient is zero, and its coefficient at degree m+1 is 1ᵀM^m1. The coefficient matrix at degree m of the inverse is M^m, as multiplying by I−sM cancels every positive-degree coefficient. Clearing the inverse with the polynomial adjugate gives denominator det(I−sM), whose constant coefficient is one.

At fixed h, put s = 2^h x. The row series is T(h,1)x + (W_(C_h)(s) − 3^h s + 6s²/(1−s))/48. The subtraction removes the contribution of all 3^h labelled first columns in degree one, and the geometric correction begins at degree two. At fixed k ≥ 2, put s = 2^k x. The column series is (W_(R_k)(s) + 6s/(1−s))/48, with the connected identity already applicable in degree one. These denominators can be taken as (1−s)det(I−sM) after absorbing 1/48 into the numerator.

For width one the column series is (6x/(1−6x) + 3·4x/(1−4x) + 15·2x/(1−2x))/48. Each series begins in degree one and admits a polynomial denominator with constant coefficient one. The argument applies to every fixed positive dimension.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.C`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.Word`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_continuations`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_power`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.powerOnes_of_rows`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.wordTransfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_continuations`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_count`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations](../HardinColumnContinuations.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
