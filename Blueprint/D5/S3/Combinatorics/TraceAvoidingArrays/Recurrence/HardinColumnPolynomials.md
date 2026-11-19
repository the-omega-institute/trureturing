# Column continuation polynomials

## Abstract

Exact full-state vector polynomials for four and six rows.

**Theorem 1.1 (Four-row relation on all 81 columns).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowFour`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eighth power on ones equals the sum at exponents 7, 6, 5, 4, 3, 2, 1 with respective coefficients (4, 13, −19, −22, 27, 2, −4). Their sum is one. The exact current-column quotient supplies this relation after multiplying its degree-six relation by the first-order factor X−1.

**Theorem 1.2 (Six-row relation on all 729 columns).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowSix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowSix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twenty-fifth power of C on ones equals the sum of c_j times C^(25−j) on ones, with j from 1 through 24. The lag coefficients are (7, 103, −365, −2896, 7168, 32291, −75471, −161805, 426135, 333692, −1225001, −155206, 1850161, −363389, −1524689, 557502, 690388, −312941, −166928, 81406, 19997, −9672, −906, 420) and sum to one.

**Theorem 1.3 (The actual six-row pattern count).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.sixRow_walk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.sixRow_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m≥0, L(m+1) in HardinA233179PairTransfer equals the sum of the continuation vector C^m on all six-row columns. The coordinate maps place every label back in its original cell and equate the source Proper predicate to the existing column reconstruction. This includes all 729 width-one patterns.

Reading the coordinates of the original tuples gives all source columns. Each quotient row is the sum over a whole fibre of actual compatible successor columns. The pullback preserves the all-one vector, including degree zero for dead columns. In the six-row case reverse the existing ascending power order to the manuscript lag order. The established A233179 recurrence supplies the all-width literal count statement with 64^j scaling and onset 26.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowFour`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.rowSix`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinColumnPolynomials.sixRow_walk`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer](../HardinA233179PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers](HardinActualTransfers.md)
