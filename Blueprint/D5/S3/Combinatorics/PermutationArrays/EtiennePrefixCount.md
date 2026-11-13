# Etienne's width-two prefix matrices

## Abstract

Sorted binary matrices with bounded top-left rectangle sums.

**Definition 1.1 (Actual labeled matrices).**

Lean statement: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.Arrays`

*Formalization.* `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.Arrays` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Luce Etienne (2011). *OEIS A183409, sorted binary arrays with bounded top-left rectangle sums*. URL: <https://oeis.org/A183409>.

*Commentary.*

The objects are actual functions from Fin n to Fin 2 to Bool. The rank of a row is twice its left bit plus its right bit. Thus the weak row order is exactly 00,01,10,11. Columns are words read from top to bottom: either all corresponding bits agree, or their first difference is a zero in the left column and a one in the right column. Repeated rows and equal columns are retained; there is no quotient by permutations or symmetries.

For every i from one through n and j from one through two, twice the number of ones in the top-left i by j rectangle is at most i*j. The zero extension in cell only provides natural indices for the finite sums; these bounds keep every tested cell inside the matrix. The function a is Nat.card of exactly this subtype, independently of a closed formula.

**Definition 1.2 (The all-height formula).**

Lean statement: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.claim`

*Formalization.* `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Luce Etienne (2011). *OEIS A183409, sorted binary arrays with bounded top-left rectangle sums*. URL: <https://oeis.org/A183409>.

*Commentary.*

For every natural height n at least one, the assertion is 32*a(n)=2*n^3+11*n^2+31*n+27+(n^2+n+5)*(-1)^n, with signed integer arithmetic. It is the entire second FORMULA in OEIS A183409. The empirical recurrence and generating function listed separately in that entry are not premises of this assertion.

**Theorem 1.3 (Cardinality by the four row blocks).**

Lean statement: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Luce Etienne (2011). *OEIS A183409, sorted binary arrays with bounded top-left rectangle sums*. URL: <https://oeis.org/A183409>.

*Commentary.*

A sorted matrix has four consecutive blocks 00,01,10,11. The cuts p,q,r count ranks strictly below one, two and three. For a monotone word every strict sublevel set is an initial segment, so these three sizes reconstruct every entry at its original position. Conversely the block construction is monotone and its cuts are unique. The equivalence of actual matrices with valid cuts includes both inverse laws.

Write A=p, B=q-p, C=r-q and D=n-r. Their sum is n. The column comparison is equivalent to B>0 or C=0. At every prefix height i, the first column has i-q ones, using natural subtraction. The two-column rectangle has (i-p)+(i-r) ones. These identities show that all rectangle bounds are equivalent to C+D<=A+B and D<=A; the reverse implication uses the same prefix identities for each i, not only the full-height rectangle.

Set t=C+D, d=D and u=n-t. Then t ranges from zero through floor(n/2), and d ranges from zero through t. If d<t, the admissible values of A form the half-open interval from d to u. If d=t, the interval includes u. The last coordinate is A-d, with respective sizes u-d and u-d+1. Reconstruction gives B=u-A, C=t-d and D=d. The inverse laws also hold at zero-length blocks and interval endpoints.

The inner sum has one extra endpoint, at d=t. Mathlib's finite arithmetic-series identity evaluates its doubled cardinality; summing the fibers gives 2*a(n)=2*(m+1)+(n-m)*(m+1)*(m+2), where m=floor(n/2). The two possibilities n=2*m and n=2*m+1 then give the signed formula. In particular, the sole equal-column matrix at each t is retained. The boundary n=1 and the even endpoint t=n/2 require no separate exclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.Arrays`
- Truth anchor: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.claim`
- Truth anchor: `D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result`
