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

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.row_fibres_iff_pow_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.row_fibres_iff_pow_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T and Q be integer matrices on finite state sets A and B and let c map A to B. The row total of T at a over the fibre of b is Q(c(a),b) for every a and b if and only if T^m(v∘c)(a) = (Q^m v)(c(a)) for every integer vector v on B, exponent m≥0, and a in A. For the forward direction regroup the sum into fibres at each step. For the reverse direction take m=1 and let v be the indicator of b.

**Definition 1.10 (Lag convention).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a length-d coefficient list c, the relation with shift b equates T^(b+d) on ones with the sum of c_j times T^(b+d−j) on ones for j from one through d. The manuscript uses b=1 for diagonal strip columns and b=0 for proper row words. The height-one and height-two column relations also hold at b=0.

Write T(h,n) for the cardinality of the literal normalized diagonal arrays of positive height h and width n. Write L(h,n) for the labelled three-colour count of the same graph. For physical height h≥1, set C_h = C (h−1) in Lean, acting on the 3^h unrestricted columns of height h. For physical width k≥1, set R_k = wordTransfer true (k−1) in Lean, acting on Word (k−1), the 3·2^(k−1) proper words of length k. Read the labelled columns in increasing order and recover the label at (r,j) from position r of column j. The column compatibility test compares the labels at positions r and t whenever their distance is at most one. Reading the labelled rows in increasing order recovers the label at (r,j) from position j of row r. Each row is a proper word, and successive rows compare the two opposite diagonals at every adjacent pair of positions. Reading and reconstructing are inverse in each orientation. The unique empty tail gives the all-one vector, and each successor step uses the matrix indexed by current state and then successor state. Thus L(h,n) = 1ᵀC_h^(n−1)1 = 1ᵀR_n^(h−1)1. These are column_count (h−1) (n−1) and word_count true (n−1) (h−1), respectively.

Every diagonal strip of width at least two is connected, has an edge and is bipartite by column parity. Horizontal edges link the vertices in each row, and each pair of successive rows is joined by a diagonal. Hence there are two labelled two-colourings and zero one-colourings. The literal normalization is 48 T(h,n) = 2^(hn)(L(h,n)+6) for n≥2. At width one the strip is edgeless, and 48 T(h,1) = 6^h + 3·4^h + 15·2^h.

For any of the transfer matrices M, let W_M(s) = s·1ᵀ(I−sM)⁻¹1 over the rational formal power series ring. Its constant coefficient is zero, and its coefficient at degree m+1 is 1ᵀM^m1. The series with coefficient matrix M^m in degree m is the inverse, since multiplication on either side by I−sM leaves I in degree zero and cancels every positive-degree coefficient. The polynomial adjugate gives denominator det(I−sM), whose constant coefficient is det(I) = 1. These identities are the all-one specialization of FiniteTransferSeries.walks_resolvent.

For every fixed h≥1, put s = 2^h x. The row series ∑_(n≥1) T(h,n)x^n is T(h,1)x + (W_(C_h)(s) − 3^h s + 6s²/(1−s))/48, since s^n = 2^(hn)x^n. The subtraction removes the contribution of all 3^h labelled first columns in degree one, and the geometric correction begins at degree two. For every fixed k≥2, put s = 2^k x. The column series ∑_(h≥1) T(h,k)x^h is (W_(R_k)(s) + 6s/(1−s))/48, since s^h = 2^(hk)x^h. The connected identity already applies at height one, where the coefficient of x is 2^k(3·2^(k−1)+6)/48. Both denominators can be taken as (1−s)det(I−sM) after absorbing 1/48 into the numerator.

For width one the column series ∑_(h≥1) T(h,1)x^h is (6x/(1−6x) + 3·4x/(1−4x) + 15·2x/(1−2x))/48. Each series begins in degree one and admits a polynomial denominator with constant coefficient one. The argument applies to every fixed positive dimension.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.C`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.IsLagRelation`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.Word`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_continuations`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.column_power`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.row_fibres_iff_pow_mulVec`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.wordTransfer`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_continuations`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.word_count`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations](../HardinColumnContinuations.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../TransferMatrix.md)
