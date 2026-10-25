# The homogeneous trisection polynomial

## Abstract

Trisection binomial coefficients give strict symmetric balancing.

Degree variables and summation indices are natural numbers. Subtraction in indices and exponents is natural truncated subtraction. Scalar subtraction in the moment formulas takes place in the integers or reals, as specified below. The functions alpha and beta are integer-valued, and their six cases are ordered by n modulo six. No root-of-unity choice is required: Pascal's recurrence proves the six-periodic filter formula.

**Definition 1.1 (Binomial residue sums).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{residue}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer sum counts binomial coefficients in a prescribed residue class modulo three.

**Definition 1.2 (The six-periodic correction).**

$$\forall (q: \mathbb{N}), \operatorname{periodic}\left(q\right) = \operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 0) \operatorname{then} (2) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 1) \operatorname{then} (1) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 2) \operatorname{then} (-(1)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 3) \operatorname{then} (-(2)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 4) \operatorname{then} (-(1)) \operatorname{else} (1)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.periodic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six values are 2, 1, -1, -2, -1, 1. This is the real correction normally obtained by a cubic root-of-unity filter.

**Theorem 1.3 (The exact trisection filter).**

$$\forall (n: \mathbb{N}), 3 \cdot \operatorname{residue}\left(n, 0\right) = (2)^{n} + \operatorname{periodic}\left(n\right) \land \left(3 \cdot \operatorname{residue}\left(n, 1\right) = (2)^{n} + \operatorname{periodic}\left(n + 4\right) \land 3 \cdot \operatorname{residue}\left(n, 2\right) = (2)^{n} + \operatorname{periodic}\left(n + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.residue_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pascal's recurrence couples the three residue sums. Induction and the six possible residues of n determine all three correction terms simultaneously.

**Definition 1.4 (The first marked moment).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{weighted}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot k \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.weighted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplying by k marks one selected element of a binomial subset.

**Definition 1.5 (The second marked moment).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{second}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot k \cdot \left(k - 1\right) \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor k(k-1) marks an ordered pair of distinct selected elements. This subtraction takes place in the integers.

**Definition 1.6 (The first-moment difference).**

$$\forall (n: \mathbb{N}), \operatorname{A}\left(n\right) = \operatorname{weighted}\left(n, 0\right) - 2 \cdot \operatorname{weighted}\left(n - 1, 0\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(n) is the first marked trisection sum at n minus twice its value at n-1.

**Definition 1.7 (The weighted difference).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), \operatorname{T}\left(n, N\right) = \left(N - 1\right) \cdot \operatorname{A}\left(n\right) - \left(\operatorname{second}\left(n, 0\right) - 2 \cdot \operatorname{second}\left(n - 1, 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Using k(N-k)=(N-1)k-k(k-1), this is the weighted trisection difference. The factors N-1 and k-1 are integer differences.

**Definition 1.8 (The first correction table).**

$$\forall (n: \mathbb{N}), \operatorname{alpha}\left(n\right) = \operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 0) \operatorname{then} (-(3 \cdot n) + 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 1) \operatorname{then} (-(3 \cdot n) + 2) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 2) \operatorname{then} (-(2)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 3) \operatorname{then} (3 \cdot n - 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 4) \operatorname{then} (3 \cdot n - 2) \operatorname{else} (2)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction alpha(n) is selected by n modulo six.

**Definition 1.9 (The second correction table).**

$$\forall (n: \mathbb{N}), \operatorname{beta}\left(n\right) = \operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 0) \operatorname{then} (-(3 \cdot n) + 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 1) \operatorname{then} (-(4)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 2) \operatorname{then} (3 \cdot n - 8) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 3) \operatorname{then} (3 \cdot n - 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 4) \operatorname{then} (4) \operatorname{else} (-(3 \cdot n) + 8)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction beta(n) is selected by the same residue.

**Theorem 1.10 (The first closed formula).**

$$\forall (n: \mathbb{N}), (1 \le n) \Rightarrow (3 \cdot \operatorname{A}\left(n\right) = (2)^{n - 1} + \operatorname{alpha}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing one marked element reduces the first moment to a residue sum. Substitution of the filter formula gives the stated identity, including n=1 and n=2.

**Theorem 1.11 (The weighted closed formula).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), (1 \le n) \Rightarrow (3 \cdot \operatorname{T}\left(n, N\right) = \left(N - n\right) \cdot (2)^{n - 1} + \left(N - 1\right) \cdot \operatorname{alpha}\left(n\right) - \left(n - 1\right) \cdot \operatorname{beta}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing two marked elements handles the second moment. The displayed differences N-n, N-1 and n-1 in the scalar factors are integer differences.

**Theorem 1.12 (Nonnegativity of the slope).**

$$\forall (n: \mathbb{N}), (1 \le n) \Rightarrow (0 \le \operatorname{A}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Small degrees are immediate. For n at least five, the Bernoulli estimate one_add_mul_le_pow at n-5 gives 2 to the power n-1 at least 3n-2, which dominates every negative correction.

**Theorem 1.13 (Nonnegativity of every homogeneous coefficient).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), (1 \le n) \Rightarrow ((\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow ((n < N) \Rightarrow (0 \le \operatorname{T}\left(n, N\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six residue cases reduce to the nonnegative slope and two exponential bounds against quadratics. For the offsets q=n-7 and q=n-8, respectively, the proof squares the Bernoulli estimate one_add_mul_le_pow at q/2, splits q into twice its natural quotient by two plus its remainder, and normalizes the two parity cases.

**Definition 1.14 (Homogeneous binomial coefficients).**

$$\forall (N: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{coeff}\left(N, k\right) = \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = 0) \operatorname{then} (k \cdot \left(N - k\right) \cdot \operatorname{Nat.choose}\left(N, k\right)) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only exponents divisible by three contribute. The scalar N-k is the real difference, and the binomial coefficient is cast to the reals. The endpoint factors make the k=0 and k=N terms zero.

**Definition 1.15 (The homogeneous trisection polynomial).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{P}\left(N, x, y\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{coeff}\left(N, k\right) \cdot (x)^{k} \cdot (y)^{N - k})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every monomial has total degree N. For N divisible by three, reflection of the exponent k exchanges x and y.

**Theorem 1.16 (Symmetric coefficients).**

$$\forall (N: \mathbb{N}), \forall (k: \mathbb{N}), (\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow ((k \le N) \Rightarrow (\operatorname{coeff}\left(N, N - k\right) = \operatorname{coeff}\left(N, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.coeff_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binomial reflection identity and divisibility by three give the required symmetry for Beta lifting.

**Definition 1.17 (Coefficients after shearing).**

$$\forall (N: \mathbb{N}), \forall (t: \mathbb{N}), \operatorname{B}\left(N, t\right) = \operatorname{Nat.choose}\left(N, t\right) \cdot \left(\left(N - 1\right) \cdot \operatorname{weighted}\left(N - t, 0\right) - \operatorname{second}\left(N - t, 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expansion P(N,x,x+d) is the sum of B(N,t)x to the power N-t times d to the power t. Exchanging the two binomial choices proves this formula.

**Definition 1.18 (The balancing derivative).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{D}\left(N, x, d\right) = \sum_{t \in \operatorname{Finset.range}\left(N\right)} (\left(N - t\right) \cdot \operatorname{Nat.choose}\left(N, t\right) \cdot \operatorname{T}\left(N - t, N\right) \cdot (x)^{N - t - 1} \cdot (d)^{t})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Collecting adjacent coefficients of the differentiated shear expansion produces this finite sum.

**Theorem 1.19 (Derivative along a constant-sum slice).**

$$\forall (N: \mathbb{N}), \forall (S: \mathbb{R}), \forall (x: \mathbb{R}), \operatorname{HasDerivAt}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{P}\left(N, s, S - s\right)), \operatorname{D}\left(N, x, S - 2 \cdot x\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.hasDerivAt_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate the finite shear expansion. The derivative coefficient is n times the corresponding binomial coefficient times T(n,N).

**Definition 1.20 (The divided derivative kernel).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{K}\left(N, x, d\right) = \sum_{n \in \operatorname{Finset.Icc}\left(1, N - 1\right)} (n \cdot \operatorname{Nat.choose}\left(N, n\right) \cdot \operatorname{T}\left(n, N\right) \cdot (x)^{n - 1} \cdot (d)^{N - n - 1})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Homogeneous.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the coefficient formula for the divided homogeneous balancing derivative. Its coefficients are nonnegative whenever N is divisible by three.

**Theorem 1.21 (Factorization by the imbalance).**

$$\forall (N: \mathbb{N}), (\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow (\forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{D}\left(N, x, d\right) = d \cdot \operatorname{K}\left(N, x, d\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.derivative_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at d=0 vanishes by symmetry. Reindexing the remaining terms gives d times K exactly.

**Theorem 1.22 (Strict balancing on the positive half interval).**

$$\forall (m: \mathbb{N}), (2 \le m) \Rightarrow (\operatorname{StrictMonoOn}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{P}\left(3 \cdot m, t, 1 - t\right)), \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Homogeneous.strictMonoOn_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x and d positive, the n=3 coefficient is strictly positive because T(3,N)=3(N-3), while every other summand is nonnegative. For 0<x<1/2, d=1-2x is positive. The mean-value theorem gives strict increase, including comparisons with the midpoint.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A_formula`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.A_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.B`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.D`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.K`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.P`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T_formula`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.T_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.alpha`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.beta`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.coeff`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.coeff_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.derivative_expansion`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.hasDerivAt_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.periodic`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.residue`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.residue_filter`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.second`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.strictMonoOn_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Homogeneous.weighted`
