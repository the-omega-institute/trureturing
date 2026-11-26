# Hardin's common recurrences for constant-stress rectangles

## Abstract

Hardin's three common recurrences for literal constant-stress rectangles.

The count C(M,S,n,k) counts literal indexed grids with n+1 rows and k+1 columns. Their entries range from 0 to M, and every contiguous 2×2 block has absolute difference S between its diagonal and antidiagonal sums. See `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C`.

The equivalence `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.fixedDeficitEquiv` gives two copies of the grids with block sum d = 2M−S when 0 ≤ d < M and S = 2M−d. In each copy the horizontal edge sums in successive rows alternate between a profile and its complement in d. An initial entry determines a row from its edge sums. If the first edge sum is s, the two complementary row fibers have at most s+1 and d−s+1 choices. The resulting one- and two-step laws apply to each profile's contribution. The same shift polynomial annihilates every contribution, so it also annihilates their sum. This gives the first-axis recurrence, and transposition gives the second.

**Theorem 1.1 (A235280 recurrence for all rows and columns).**

$$\begin{aligned}&\forall n: \mathbb{N}, \forall k: \mathbb{N}, 0 < n \implies 0 < k \implies\\((C\left(4, 5, n + 9, k\right) : \mathbb{Z}) &=(C\left(4, 5, n + 8, k\right) : \mathbb{Z})+15\cdot(C\left(4, 5, n + 7, k\right) : \mathbb{Z})-15\cdot(C\left(4, 5, n + 6, k\right) : \mathbb{Z})\\&\quad-80\cdot(C\left(4, 5, n + 5, k\right) : \mathbb{Z})+80\cdot(C\left(4, 5, n + 4, k\right) : \mathbb{Z})+180\cdot(C\left(4, 5, n + 3, k\right) : \mathbb{Z})\\&\quad-180\cdot(C\left(4, 5, n + 2, k\right) : \mathbb{Z})-144\cdot(C\left(4, 5, n + 1, k\right) : \mathbb{Z})+144\cdot(C\left(4, 5, n, k\right) : \mathbb{Z}))\\&\land\\((C\left(4, 5, n, k + 9\right) : \mathbb{Z}) &=(C\left(4, 5, n, k + 8\right) : \mathbb{Z})+15\cdot(C\left(4, 5, n, k + 7\right) : \mathbb{Z})-15\cdot(C\left(4, 5, n, k + 6\right) : \mathbb{Z})\\&\quad-80\cdot(C\left(4, 5, n, k + 5\right) : \mathbb{Z})+80\cdot(C\left(4, 5, n, k + 4\right) : \mathbb{Z})+180\cdot(C\left(4, 5, n, k + 3\right) : \mathbb{Z})\\&\quad-180\cdot(C\left(4, 5, n, k + 2\right) : \mathbb{Z})-144\cdot(C\left(4, 5, n, k + 1\right) : \mathbb{Z})+144\cdot(C\left(4, 5, n, k\right) : \mathbb{Z}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235280_all_rows_and_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235280 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235280>.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235279 — Column 9 of A235280*. URL: <https://oeis.org/A235279>.

*Commentary.*

The table proposes one recurrence for every row and every column. A235279 supplies the signed row for column 9. At deficit three the shift polynomial is (X−1)(X²−2)(X²−3)(X²−4)(X²−6). The first varying index on either axis is 10. The fixed index can be as small as one in both identities.

**Theorem 1.2 (A235310 recurrence for all rows and columns).**

$$\begin{aligned}&\forall n: \mathbb{N}, \forall k: \mathbb{N}, 0 < n \implies 0 < k \implies\\((C\left(5, 6, n + 14, k\right) : \mathbb{Z}) &=4\cdot(C\left(5, 6, n + 13, k\right) : \mathbb{Z})+25\cdot(C\left(5, 6, n + 12, k\right) : \mathbb{Z})-112\cdot(C\left(5, 6, n + 11, k\right) : \mathbb{Z})\\&\quad-231\cdot(C\left(5, 6, n + 10, k\right) : \mathbb{Z})+1260\cdot(C\left(5, 6, n + 9, k\right) : \mathbb{Z})+875\cdot(C\left(5, 6, n + 8, k\right) : \mathbb{Z})\\&\quad-7280\cdot(C\left(5, 6, n + 7, k\right) : \mathbb{Z})-224\cdot(C\left(5, 6, n + 6, k\right) : \mathbb{Z})+22736\cdot(C\left(5, 6, n + 5, k\right) : \mathbb{Z})\\&\quad-7980\cdot(C\left(5, 6, n + 4, k\right) : \mathbb{Z})-36288\cdot(C\left(5, 6, n + 3, k\right) : \mathbb{Z})+21456\cdot(C\left(5, 6, n + 2, k\right) : \mathbb{Z})\\&\quad+23040\cdot(C\left(5, 6, n + 1, k\right) : \mathbb{Z})-17280\cdot(C\left(5, 6, n, k\right) : \mathbb{Z}))\\&\land\\((C\left(5, 6, n, k + 14\right) : \mathbb{Z}) &=4\cdot(C\left(5, 6, n, k + 13\right) : \mathbb{Z})+25\cdot(C\left(5, 6, n, k + 12\right) : \mathbb{Z})-112\cdot(C\left(5, 6, n, k + 11\right) : \mathbb{Z})\\&\quad-231\cdot(C\left(5, 6, n, k + 10\right) : \mathbb{Z})+1260\cdot(C\left(5, 6, n, k + 9\right) : \mathbb{Z})+875\cdot(C\left(5, 6, n, k + 8\right) : \mathbb{Z})\\&\quad-7280\cdot(C\left(5, 6, n, k + 7\right) : \mathbb{Z})-224\cdot(C\left(5, 6, n, k + 6\right) : \mathbb{Z})+22736\cdot(C\left(5, 6, n, k + 5\right) : \mathbb{Z})\\&\quad-7980\cdot(C\left(5, 6, n, k + 4\right) : \mathbb{Z})-36288\cdot(C\left(5, 6, n, k + 3\right) : \mathbb{Z})+21456\cdot(C\left(5, 6, n, k + 2\right) : \mathbb{Z})\\&\quad+23040\cdot(C\left(5, 6, n, k + 1\right) : \mathbb{Z})-17280\cdot(C\left(5, 6, n, k\right) : \mathbb{Z}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235310_all_rows_and_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235310 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235310>.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235304 — Column 2 of A235310*. URL: <https://oeis.org/A235304>.

*Commentary.*

The table proposes one recurrence for every row and every column. A235304 supplies the signed row for column 2. At deficit four the shift polynomial is (X−1)(X−3)(X²−2)(X²−3)(X²−4)(X²−5)(X²−6)(X²−8). The first varying index on either axis is 15. The fixed index can be as small as one in both identities.

**Theorem 1.3 (The common A235319 order-18 recurrence).**

$$\begin{aligned}&\forall n: \mathbb{N}, \forall k: \mathbb{N}, 0 < n \implies 0 < k \implies\\((C\left(6, 7, n + 18, k\right) : \mathbb{Z}) &=4\cdot(C\left(6, 7, n + 17, k\right) : \mathbb{Z})+47\cdot(C\left(6, 7, n + 16, k\right) : \mathbb{Z})-200\cdot(C\left(6, 7, n + 15, k\right) : \mathbb{Z})\\&\quad-901\cdot(C\left(6, 7, n + 14, k\right) : \mathbb{Z})+4204\cdot(C\left(6, 7, n + 13, k\right) : \mathbb{Z})+8957\cdot(C\left(6, 7, n + 12, k\right) : \mathbb{Z})\\&\quad-48440\cdot(C\left(6, 7, n + 11, k\right) : \mathbb{Z})-47194\cdot(C\left(6, 7, n + 10, k\right) : \mathbb{Z})+334096\cdot(C\left(6, 7, n + 9, k\right) : \mathbb{Z})\\&\quad+101948\cdot(C\left(6, 7, n + 8, k\right) : \mathbb{Z})-1410080\cdot(C\left(6, 7, n + 7, k\right) : \mathbb{Z})+170136\cdot(C\left(6, 7, n + 6, k\right) : \mathbb{Z})\\&\quad+3549696\cdot(C\left(6, 7, n + 5, k\right) : \mathbb{Z})-1446912\cdot(C\left(6, 7, n + 4, k\right) : \mathbb{Z})-4861440\cdot(C\left(6, 7, n + 3, k\right) : \mathbb{Z})\\&\quad+2954880\cdot(C\left(6, 7, n + 2, k\right) : \mathbb{Z})+2764800\cdot(C\left(6, 7, n + 1, k\right) : \mathbb{Z})-2073600\cdot(C\left(6, 7, n, k\right) : \mathbb{Z}))\\&\land\\((C\left(6, 7, n, k + 18\right) : \mathbb{Z}) &=4\cdot(C\left(6, 7, n, k + 17\right) : \mathbb{Z})+47\cdot(C\left(6, 7, n, k + 16\right) : \mathbb{Z})-200\cdot(C\left(6, 7, n, k + 15\right) : \mathbb{Z})\\&\quad-901\cdot(C\left(6, 7, n, k + 14\right) : \mathbb{Z})+4204\cdot(C\left(6, 7, n, k + 13\right) : \mathbb{Z})+8957\cdot(C\left(6, 7, n, k + 12\right) : \mathbb{Z})\\&\quad-48440\cdot(C\left(6, 7, n, k + 11\right) : \mathbb{Z})-47194\cdot(C\left(6, 7, n, k + 10\right) : \mathbb{Z})+334096\cdot(C\left(6, 7, n, k + 9\right) : \mathbb{Z})\\&\quad+101948\cdot(C\left(6, 7, n, k + 8\right) : \mathbb{Z})-1410080\cdot(C\left(6, 7, n, k + 7\right) : \mathbb{Z})+170136\cdot(C\left(6, 7, n, k + 6\right) : \mathbb{Z})\\&\quad+3549696\cdot(C\left(6, 7, n, k + 5\right) : \mathbb{Z})-1446912\cdot(C\left(6, 7, n, k + 4\right) : \mathbb{Z})-4861440\cdot(C\left(6, 7, n, k + 3\right) : \mathbb{Z})\\&\quad+2954880\cdot(C\left(6, 7, n, k + 2\right) : \mathbb{Z})+2764800\cdot(C\left(6, 7, n, k + 1\right) : \mathbb{Z})-2073600\cdot(C\left(6, 7, n, k\right) : \mathbb{Z}))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235319_all_rows_and_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235319 — Constant-stress rectangular arrays*. URL: <https://oeis.org/A235319>.

*Acknowledgement.* R. H. Hardin (2014). *OEIS A235317 — Column 6 of A235319*. URL: <https://oeis.org/A235317>.

*Commentary.*

C(6,7,n,k) counts the literal indexed rectangles with alphabet 0 through 6 and absolute diagonal difference 7 in every contiguous block. Its integer cast appears in each signed term. The first full window uses indices 1 through 19 in either direction.

At deficit five, complementary row fibers have sizes whose sum is at most seven. The two-step shifts multiply their profile contribution by the product of the fiber sizes. Equal sizes one and three give first-order factors. Expanding the annihilating polynomial gives the published lag coefficients, and transposition supplies the second axis.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.C`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.fixedDeficitEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235280_all_rows_and_columns`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235310_all_rows_and_columns`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence.a235319_all_rows_and_columns`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet](HardinA235280A235310Alphabet.md)
