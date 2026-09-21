# Barry's Riordan-Pascal Kernel Determinant

## Abstract

Barry's Riordan kernel matrix is a Gram product with determinant one.

Let C embed an integer as a constant formal power series and let X be the power-series variable. The inverse invOfUnit(1-C(a)X,1) is the formal power-series interpretation of 1/(1-ax). Polynomial C embeds an integer or a polynomial as a constant polynomial. Fin(n+1) indexes the integers from zero through n.

**Definition 1.1 (The generalized Pascal Riordan array).**

$$\forall m: \mathbb{N}, \forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{riordan}\left(m, a, b, n, k\right) = \operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(1 - \operatorname{C}\left(a\right) \cdot X, 1\right) \cdot (X \cdot \left(1 + \operatorname{C}\left(b\right) \cdot X\right) \cdot \operatorname{invOfUnit}\left(1 - \operatorname{C}\left(a\right) \cdot X, 1\right)^{m})^{k}\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.riordan` (`✓ std3`).

*Citation.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

Barry's page-1 pair is g=1/(1-ax) and f=x(1+bx)/(1-ax)^m. Section 2 indexes columns from zero and generates column k by g times f^k. Thus riordan(m,a,b,n,k) is the coefficient of X^n in g times f^k.

**Definition 1.2 (The row polynomial).**

$$\forall m: \mathbb{N}, \forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{P}\left(m, a, b, n\right) = \sum_{k = 0}^{n} (\operatorname{C}\left(\operatorname{riordan}\left(m, a, b, n, k\right)\right) \cdot X^{k})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.P` (`✓ std3`).

*Citation.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

Printed page 19 defines P_n(x;m,a,b) as the sum from k=0 through n of T_(n,k) times x^k. The finite sum here has the same inclusive bounds and uses the Riordan entries as its coefficients.

**Definition 1.3 (The finite Riordan matrix).**

$$\forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n + 1\right), \forall k: \operatorname{Fin}\left(n + 1\right), \operatorname{M}\left(n, i, k\right) = \operatorname{riordan}\left(2, 1, 1, \operatorname{val}\left(i\right), \operatorname{val}\left(k\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.M` (`✓ std3`).

*Citation.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

Printed page 20 defines M_n as the first n+1 rows and columns of M. The preceding sentence fixes m=2 and a=b=1, so both finite indices range over Fin(n+1) and each entry is riordan(2,1,1,i,k).

**Definition 1.4 (The polynomial kernel matrix).**

$$\forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n + 1\right), \forall k: \operatorname{Fin}\left(n + 1\right), \operatorname{Dtilde}\left(n, i, k\right) = \operatorname{coeff}\left(\operatorname{val}\left(k\right), \operatorname{coeff}\left(\operatorname{val}\left(i\right), \sum_{j = 0}^{n} (\operatorname{map}\left(C, \operatorname{P}\left(2, 1, 1, j\right)\right) \cdot \operatorname{C}\left(\operatorname{P}\left(2, 1, 1, j\right)\right))\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.Dtilde` (`✓ std3`).

*Citation.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

The bivariate polynomial is represented as a polynomial in x whose coefficients are polynomials in y. The (i,k) entry first extracts the outer x^i coefficient and then the inner y^k coefficient from the sum of P_j(x)P_j(y) for j=0 through n. The page-20 display prints k below the sum while retaining P_j in the summand; the unambiguous comparison display on page 19 uses j as the index.

**Definition 1.5 (Conjecture 32).**

$$claim \iff \forall n: \mathbb{N}, (\operatorname{Dtilde}\left(n\right) = \operatorname{transpose}\left(\operatorname{M}\left(n\right)\right) \cdot \operatorname{M}\left(n\right)) \land (\operatorname{det}\left(\operatorname{Dtilde}\left(n\right)\right) = 1)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.claim` (`✓ std3`).

*Citation.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

The source states: "Conjecture 32. The matrix D̃_n(2, 1, 1) with generating function Σ_{k=0}^{n} P_j(x; 2, 1, 1)P_j(y; 2, 1, 1) is given by M_n^{(2)}(a, b)^t M_n^{(2)}(a, b). We then have |D̃_n(2, 1, 1)| = 1 for n ≥ 0. In the above the notation M_n denotes the matrix formed from the first (n + 1) rows and columns of M." The right side is read at a=b=1 from the sentence immediately preceding the conjecture and from its left side.

**Theorem 1.6 (Conjecture 32 holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2013). *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf>.

*Commentary.*

For each pair of finite indices, coefficient extraction from the kernel sum gives the finite sum of products T_(j,i)T_(j,k), which is the corresponding entry of the transpose of M_n times M_n. The Riordan series contributing to column k contains X^k with constant coefficient one after that factor. Hence M_n is lower triangular with diagonal one. Its determinant is one, and multiplicativity together with invariance under transpose gives determinant one for the kernel matrix.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.Dtilde`
- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.M`
- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.P`
- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.riordan`
