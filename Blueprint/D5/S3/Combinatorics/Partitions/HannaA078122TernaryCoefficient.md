# Hanna's ternary coefficient formula

## Abstract

The cubic-shift matrix exists, and every such natural-valued matrix satisfies Hanna's full ternary coefficient formula.

**Definition 1.1 (The cubic-shift source matrix).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Nat}, \operatorname{Nat}, \operatorname{Nat}\right),\; (\operatorname{IsSourceMatrix}\left(M\right)) \Leftrightarrow ((\operatorname{Matrix}.\operatorname{IsLowerTriangular}\left(M\right)) \land ((\forall n \in \operatorname{Nat},\; M\left(n, 0\right) = 1) \land ((\forall n \in \operatorname{Nat},\; M\left(n, n\right) = 1) \land (\forall m \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(m+1\right),\; \forall j \in \operatorname{Fin}\left(m+1\right),\; \left((\operatorname{Matrix}.\operatorname{submatrix}\left(M, (\operatorname{fun}(a: \operatorname{Fin}\left(m+1\right)) \mapsto \operatorname{val}\left(a\right)), (\operatorname{fun}(a: \operatorname{Fin}\left(m+1\right)) \mapsto \operatorname{val}\left(a\right))\right))^{3}\right)\left(i, j\right) = M\left(\operatorname{val}\left(i\right)+1, \operatorname{val}\left(j\right)+1\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.IsSourceMatrix` (`✓ std3`).

*Citation.* Paul D. Hanna (2002). *OEIS A078122 — infinite lower triangular cubic-shift matrix*. URL: <https://oeis.org/A078122>.

*Commentary.*

OEIS A078122 revision 10, NAME (unpaginated), states: “Infinite lower triangular matrix, M, that satisfies [M^3](i,j) = M(i+1,j+1) for all i,j>=0 where [M^n](i,j) denotes the element at row i, column j, of the n-th power of matrix M, with M(0,k)=1 and M(k,k)=1 for all k>=0.” Its first-row condition conflicts with lower triangularity. Both source programs instead set the first column to one, as does the displayed matrix. IsSourceMatrix uses this first-column condition and the stated diagonal condition. Finite principal blocks carry Mathlib's ordinary matrix multiplication and third power. Requiring the equation on every block gives the coefficientwise infinite matrix equation because lower triangularity restricts every nonzero summand to the interval between its two indices.

**Definition 1.2 (The ternary partition reciprocal).**

$$\forall d \in \operatorname{Nat},\; \operatorname{partitionSeries}\left(d\right) = (\prod_{j \in \operatorname{Finset}.\operatorname{range}\left(d+1\right)} ((1: \operatorname{PowerSeries}\left(\operatorname{Rat}\right))-(\operatorname{PowerSeries}.\operatorname{X})^{(3)^{j}}))^{-1}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.partitionSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2002). *OEIS A078122 — infinite lower triangular cubic-shift matrix*. URL: <https://oeis.org/A078122>.

*Commentary.*

The second FORMULA of OEIS A078122 revision 10 (unpaginated) states: “M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of 1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n for all n>0 (conjecture).” Here d=n−k, X is the formal power-series variable, and the finite product ranges over j=0,…,d. Every exponent 3^j is positive, so the denominator has constant coefficient one and its inverse is a formal reciprocal over Rat.

**Definition 1.3 (The full second FORMULA conjecture).**

$$(\operatorname{claim}) \Leftrightarrow ((\exists M \in \operatorname{Matrix}\left(\operatorname{Nat}, \operatorname{Nat}, \operatorname{Nat}\right),\; \operatorname{IsSourceMatrix}\left(M\right)) \land (\forall M \in \operatorname{Matrix}\left(\operatorname{Nat}, \operatorname{Nat}, \operatorname{Nat}\right),\; (\operatorname{IsSourceMatrix}\left(M\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; \forall k \in \operatorname{Nat},\; (0 < n) \Rightarrow ((k < n) \Rightarrow ((M\left(n, k\right): \operatorname{Rat}) = \operatorname{PowerSeries}.\operatorname{coeff}\left(((3)^{n}-(3)^{(n-k)}), \operatorname{partitionSeries}\left((n-k)\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2002). *OEIS A078122 — infinite lower triangular cubic-shift matrix*. URL: <https://oeis.org/A078122>.

*Commentary.*

OEIS A078122 revision 10, second FORMULA (unpaginated), states: “M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of 1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n for all n>0 (conjecture).” The statement includes existence of a natural-valued source matrix and quantifies over every such matrix. The indices n and k are natural numbers, so 0≤k is automatic. The guards 0<n and k<n make both displayed natural subtractions agree with the nonnegative integer exponents in the source. Entries are cast to Rat before comparison with formal coefficients.

**Theorem 1.4 (The coefficient formula for every source matrix).**

$$(\exists M \in \operatorname{Matrix}\left(\operatorname{Nat}, \operatorname{Nat}, \operatorname{Nat}\right),\; \operatorname{IsSourceMatrix}\left(M\right)) \land (\forall M \in \operatorname{Matrix}\left(\operatorname{Nat}, \operatorname{Nat}, \operatorname{Nat}\right),\; (\operatorname{IsSourceMatrix}\left(M\right)) \Rightarrow (\forall n \in \operatorname{Nat},\; \forall k \in \operatorname{Nat},\; (0 < n) \Rightarrow ((k < n) \Rightarrow ((M\left(n, k\right): \operatorname{Rat}) = \operatorname{PowerSeries}.\operatorname{coeff}\left(((3)^{n}-(3)^{(n-k)}), \operatorname{partitionSeries}\left((n-k)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2002). *OEIS A078122 — infinite lower triangular cubic-shift matrix*. URL: <https://oeis.org/A078122>.

*Commentary.*

The finite-difference recurrence for the restricted ternary partition coefficients gives a scaled convolution identity by double induction. The resulting natural-valued lower triangular matrices form an additive semigroup in their scale parameter. At parameter one, the cube shifts both indices, while the first column and diagonal are one. Strong induction on rows identifies every source matrix with this construction. The exponent identity 3^(n−k)(3^k−1)=3^n−3^(n−k) gives exactly the stated coefficient. This proves the full unbounded ternary array, including existence; other bases and row-sum interpretations are separate questions.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.IsSourceMatrix`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.partitionSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient.result`
