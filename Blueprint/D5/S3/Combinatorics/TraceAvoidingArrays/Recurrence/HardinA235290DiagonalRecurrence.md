# Hardin's diagonal recurrence for stress-three arrays

## Abstract

The eleven-lag recurrence for literal stress-three square arrays.

**Theorem 1.1 (The signed eleven-lag recurrence).**

$$\forall n: Nat, (12 \le n \implies a\left(n\right) = 4 \cdot a\left(n - 1\right) + 23 \cdot a\left(n - 2\right) - 92 \cdot a\left(n - 3\right) - 200 \cdot a\left(n - 4\right) + 800 \cdot a\left(n - 5\right) + 820 \cdot a\left(n - 6\right) - 3280 \cdot a\left(n - 7\right) - 1584 \cdot a\left(n - 8\right) + 6336 \cdot a\left(n - 9\right) + 1152 \cdot a\left(n - 10\right) - 4608 \cdot a\left(n - 11\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence.hardin_a235290` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235290 — Constant-stress square arrays*. URL: <https://oeis.org/A235290>.

*Commentary.*

The count C(3,3,h,w) is the number of indexed arrays of height h+1 and width w+1 with entries 0 through 3. Every contiguous two-by-two block has an absolute difference of three between its diagonal and antidiagonal sums. The integer a(n) is C(3,3,n,n). Indices and their differences are natural numbers, and the recurrence is an equality over the integers.

Apply the signed eleven-lag recurrence as a residual on rectangles, shifting the two side parameters together. At each positive fixed side, the rectangular count obeys the common order-ten recurrence in the other coordinate. The finite sum defining the residual commutes with the order-ten rule, so the residual obeys that rule separately in both coordinates.

A sparse row transfer and a six-state column continuation count give the literal counts for both side parameters from one through ten. The axial recurrences determine the table through side parameter twenty-one. The residual vanishes on the full ten-by-ten window of starting side parameters. The order-ten recurrence propagates those zeros along both axes. Taking the two side parameters equal gives the displayed identity.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235290DiagonalRecurrence.hardin_a235290`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence](HardinA235301Recurrence.md)
