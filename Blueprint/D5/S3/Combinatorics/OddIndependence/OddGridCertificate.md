# A local discharge inequality for square-grid windows

## Abstract

Local strip potentials telescope to bound the total occupancy of cross-free independent square-grid windows.

**Theorem 1.1 (Summing the local discharge).**

Lean statement: `D5/S3/Combinatorics/OddIndependence/OddGridCertificate.certificate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OddIndependence/OddGridCertificate.certificate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yair Caro; Mirko Petruševski; Riste Škrekovski; Zsolt Tuza (2025). *The odd independence number of graphs, II: Finite and infinite grids and chessboard graphs*. URL: <https://arxiv.org/abs/2510.01897v1>.

*Commentary.*

Let b be a Boolean array on pairs of natural numbers whose occupied positions satisfy 2 at most x less than n+2 and 2 at most y less than n+2. Suppose every occupied position has unoccupied successors in both coordinate directions, and no four positions (x,y+1), (x+1,y), (x+1,y+2), (x+2,y+1) are all occupied. Let W be the sum of the occupancies in all three by three windows starting at coordinates i,j from zero through n+1. Then 8W is at most 27(n+2) squared. For a window with entries a,b,c in the first row, d,e,f in the second and g,h,k in the third, put L=(a,b,d,e,g,h), R=(b,c,e,f,h,k), T=(a,b,c,d,e,f), and B=(d,e,f,g,h,k). Encode occupied and unoccupied entries by 1 and 0. The horizontal potential H takes values -1, 1, -5 and 5 on 100010, 000110, 100110 and 011001 respectively, and zero elsewhere. The vertical potential V takes values 3, 2, 4 and 3 on 100010, 001010, 000101 and 010101 respectively, and zero elsewhere. Every independent window without a full central cross satisfies 8w + H(L) - H(R) + V(T) - V(B) at most 27, where w is its occupancy. Summing these inequalities cancels interior strip potentials. The support restriction makes the remaining boundary potentials zero, leaving the stated bound.

## References

- Truth anchor: `D5/S3/Combinatorics/OddIndependence/OddGridCertificate.certificate_bound`
