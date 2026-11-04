# A Stirling minor as a finite Vandermonde-square sum

## Abstract

Kurkov's three-parameter Stirling-minor Vandermonde sum.

All parameters are natural numbers. The matrix indices in the OEIS source start at one; a Fin index i represents i+1. The unsigned cycle numbers are Nat.stirlingFirst. The domain Chain is the antitone-map type of KurkovNestedStirlingIdentity, so each tuple in the nested ranges is counted exactly once. Factorials, descending factorials and exponents are natural; all divisions and Vandermonde differences are rational. Natural subtraction has Lean's truncated meaning; the bounds on a chain make the displayed indices equal to their integer values.

**Definition 1.1 (The first-kind Stirling minor).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{B}\left(n, k, m\right) = \operatorname{Matrix.det}\left(\lambda i:\operatorname{Fin}\left(k\right) \mapsto \lambda j:\operatorname{Fin}\left(k\right) \mapsto (\operatorname{Nat.stirlingFirst}\left(n + m + \operatorname{val}\left(i\right) + 1, n + \operatorname{val}\left(j\right) + 1\right):\mathbb{Q})\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.B` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A396563: three-parameter Stirling-minor Vandermonde sum*. URL: <https://oeis.org/A396563/internal>.

*Commentary.*

The source, OEIS A396563 FORMULA (unpaginated), defines the determinant in the sentence below. Conjecture: B(n, k, m) = (Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} * (n-j_t+t)^(n+k) / (j_t+m-t)!) / (Product_{i=0..m-1} (n+i)!) where B(n, k, m) is the determinant of the k X k matrix with (i, j)-th entry |Stirling1(n+m+i, n+j)|, where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k).

**Definition 1.2 (The signed summand).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall j \in \operatorname{Chain}\left(n, m\right),\; \operatorname{sourceTerm}\left(k, j\right) = ((-1:\mathbb{Q}))^{\sum_{t:\operatorname{Fin}\left(m\right)} (\operatorname{val}\left(\operatorname{val}\left(j\right)\left(t\right)\right))} \cdot \prod_{q:\operatorname{Fin}\left(m\right)} (\prod_{p \in \operatorname{Finset.Ioi}\left(q\right)} (((\operatorname{val}\left(\operatorname{val}\left(j\right)\left(q\right)\right):\mathbb{Q}) - (\operatorname{val}\left(\operatorname{val}\left(j\right)\left(p\right)\right):\mathbb{Q}) + (\operatorname{val}\left(p\right):\mathbb{Q}) - (\operatorname{val}\left(q\right):\mathbb{Q}))^{2})) \cdot \prod_{t:\operatorname{Fin}\left(m\right)} (\frac{(\operatorname{Nat.descFactorial}\left(n + \operatorname{val}\left(t\right), \operatorname{val}\left(\operatorname{val}\left(j\right)\left(t\right)\right)\right):\mathbb{Q}) \cdot ((n - \operatorname{val}\left(\operatorname{val}\left(j\right)\left(t\right)\right) + \operatorname{val}\left(t\right) + 1:\mathbb{Q}))^{n + k}}{(\operatorname{Nat.factorial}\left(\operatorname{val}\left(\operatorname{val}\left(j\right)\left(t\right)\right) + m - \left(\operatorname{val}\left(t\right) + 1\right)\right):\mathbb{Q})})$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.sourceTerm` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A396563: three-parameter Stirling-minor Vandermonde sum*. URL: <https://oeis.org/A396563/internal>.

*Commentary.*

The sign exponent is the sum of the chain values. Each pair of positions contributes the square of its rational difference with the position correction. The descending factorial and the power n+k lie in the numerator. Conjecture: B(n, k, m) = (Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} * (n-j_t+t)^(n+k) / (j_t+m-t)!) / (Product_{i=0..m-1} (n+i)!) where B(n, k, m) is the determinant of the k X k matrix with (i, j)-th entry |Stirling1(n+m+i, n+j)|, where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k).

**Definition 1.3 (The normalized nested sum).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{sourceRHS}\left(n, k, m\right) = \frac{\sum_{j:\operatorname{Chain}\left(n, m\right)} (\operatorname{sourceTerm}\left(k, j\right))}{\prod_{i:\operatorname{Fin}\left(m\right)} ((\operatorname{Nat.factorial}\left(n + \operatorname{val}\left(i\right)\right):\mathbb{Q}))}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.sourceRHS` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A396563: three-parameter Stirling-minor Vandermonde sum*. URL: <https://oeis.org/A396563/internal>.

*Commentary.*

The complete chain sum is divided by the product of (n+i)! for 0<=i<m. Empty products and determinants have value one. Conjecture: B(n, k, m) = (Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} * (n-j_t+t)^(n+k) / (j_t+m-t)!) / (Product_{i=0..m-1} (n+i)!) where B(n, k, m) is the determinant of the k X k matrix with (i, j)-th entry |Stirling1(n+m+i, n+j)|, where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k).

**Definition 1.4 (Kurkov's three-parameter assertion).**

$$claim = (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\operatorname{B}\left(n, k, m\right) = \operatorname{sourceRHS}\left(n, k, m\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.claim` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A396563: three-parameter Stirling-minor Vandermonde sum*. URL: <https://oeis.org/A396563/internal>.

*Commentary.*

OEIS A396563 FORMULA, approved revision 15, is unpaginated. Conjecture: B(n, k, m) = (Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} * (n-j_t+t)^(n+k) / (j_t+m-t)!) / (Product_{i=0..m-1} (n+i)!) where B(n, k, m) is the determinant of the k X k matrix with (i, j)-th entry |Stirling1(n+m+i, n+j)|, where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k). The assertion quantifies over all n,k>=0 and m>=1. The source examples and programs include n=0 and k=0.

**Theorem 1.5 (The full identity).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\operatorname{B}\left(n, k, m\right) = \operatorname{sourceRHS}\left(n, k, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/kurk396563` (proved) by `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kurk396563","declaration_gid":"D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2026). *OEIS A396563: three-parameter Stirling-minor Vandermonde sum*. URL: <https://oeis.org/A396563/internal>.

*Commentary.*

The coefficient identity for rising factorials converts the first-kind minor into an elementary-coefficient corner. Determinant-one inverse Toeplitz matrices identify that corner with the complete-coefficient corner of a different size. The map sending j at position t to n-j+t identifies the nested tuples with increasing subsets. Factorial normalization and Cauchy–Binet give a signed moment determinant. Stirling inclusion–exclusion evaluates its entries; column reversal cancels its sign. This proves the displayed identity also when n=0 or k=0.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.B`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.claim`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.result`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.sourceRHS`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/KurkovStirlingMinorVandermondeSum.sourceTerm`
- Dependency: [D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG](../../../S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.md)
- Dependency: [D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity](../../../S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.md)
- Dependency: [D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk](../../../S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.md)
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../../../S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.md)
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](../../Analytic/GoldenTomography/FinitePronyHankelReconstruction.md)
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Duality](../../Arith/AbsoluteValues/Heights/Duality.md)
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../../Quantum/Schatten/CompoundMatrices.md)
