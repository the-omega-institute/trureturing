# Trisection balancing and symmetric homogeneous beta lifting

## Abstract

Beta lifting preserves symmetric balancing for arbitrary real coefficients.

The degree N and coefficient function c are arbitrary. No coefficient sign assumption is imposed. The homogeneous polynomial is evaluated on a line of fixed coordinate sum, and its lift replaces the powers by rising factorials.

**Definition 1.1 (Homogeneous monomial expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{polynomial}\left(c, N, x, y\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{c}\left(k\right) \cdot x^{k} \cdot y^{N - k})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is the finite sum of c(k)x^k y^(N-k), including both endpoints.

**Definition 1.2 (Rising factorial lift).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{lift}\left(c, N, u, v\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{c}\left(k\right) \cdot \operatorname{Polynomial.eval}\left(u, \operatorname{ascPochhammer}\left(\mathbb{R}, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(v, \operatorname{ascPochhammer}\left(\mathbb{R}, N - k\right)\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same coefficient array multiplies the two complementary rising factorials.

**Theorem 1.3 (Continuity of the homogeneous slice).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \operatorname{Continuous}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every homogeneous slice is continuous because it is a finite sum of products of integer powers.

**Theorem 1.4 (Continuity of the lifted slice).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (S: \mathbb{R}), \operatorname{Continuous}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{lift}\left(c, N, s, S - s\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lifted slice is a polynomial in its real parameter, so it is continuous on the full real line.

**Theorem 1.5 (Symmetry of the homogeneous expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow (\forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{polynomial}\left(c, N, x, y\right) = \operatorname{polynomial}\left(c, N, y, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection of the finite index k to N-k proves coordinate symmetry when the coefficients are symmetric.

**Theorem 1.6 (Symmetry of the rising factorial expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow (\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{lift}\left(c, N, u, v\right) = \operatorname{lift}\left(c, N, v, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same reflected finite sum proves symmetry of the lifted polynomial.

**Theorem 1.7 (Normalized beta moment identity).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (m: \mathbb{R}), \forall (d: \mathbb{R}), (0 < m + d) \Rightarrow ((0 < m - d) \Rightarrow (\operatorname{lift}\left(c, N, m + d, m - d\right) = \operatorname{Polynomial.eval}\left(2 \cdot m, \operatorname{ascPochhammer}\left(\mathbb{R}, N\right)\right) \cdot \operatorname{betaMean}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right)), m, d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_eq_betaMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating each monomial against the beta density gives its Gamma quotient. KummerRatio.BetaIntegral.gamma_pochhammer converts the shifted Gamma factors to rising factorials. The remaining normalizer depends only on the total shape parameter.

**Theorem 1.8 (Weak comparison for arbitrary monotone integrands).**

$$\forall (W: \mathbb{R} \to \mathbb{R}), (\operatorname{ContinuousOn}\left(W, \operatorname{Set.Icc}\left(0, 1\right)\right)) \Rightarrow ((\forall (t: \mathbb{R}), (t \in \operatorname{Set.Icc}\left(0, 1\right)) \Rightarrow (\operatorname{W}\left(1 - t\right) = \operatorname{W}\left(t\right))) \Rightarrow ((\operatorname{MonotoneOn}\left(W, \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right)) \Rightarrow (\forall (m: \mathbb{R}), (0 < m) \Rightarrow (\operatorname{AntitoneOn}\left((\lambda (d: \mathbb{R}) \mapsto \operatorname{betaMean}\left(W, m, d\right)), \operatorname{Set.Ico}\left(0, m\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.betaMean_antiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding a positive multiple of t(1-t) makes the integrand strictly increasing toward the midpoint while preserving its symmetry. IncompleteBeta.Comparison.betaMean_strictAntiOn compares the perturbed means. Linearity of the integral and the limit as the perturbation decreases to zero yield the weak comparison.

**Theorem 1.9 (Beta lifting preserves balancing).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow ((\operatorname{MonotoneOn}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right)), \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right)) \Rightarrow (\forall (S: \mathbb{R}), (0 \le S) \Rightarrow (\operatorname{MonotoneOn}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{lift}\left(c, N, s, S - s\right)), \operatorname{Set.Icc}\left(0, \frac{S}{2}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_monotoneOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive shapes, the beta moment identity and comparison of symmetric beta means show that the lift is nondecreasing as the coordinates approach equality. Continuity extends the inequality to shape zero. A zero total has only the point zero. This preservation theorem has no positivity hypothesis on c.

Degree variables and summation indices are natural numbers. Subtraction in indices and exponents is natural truncated subtraction. Scalar subtraction in the moment formulas takes place in the integers or reals, as specified below. The functions alpha and beta are integer-valued, and their six cases are ordered by n modulo six. No root-of-unity choice is required: Pascal's recurrence proves the six-periodic filter formula.

**Definition 1.10 (Binomial residue sums).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{residue}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer sum counts binomial coefficients in a prescribed residue class modulo three.

**Definition 1.11 (The six-periodic correction).**

$$\forall (q: \mathbb{N}), \operatorname{periodic}\left(q\right) = \operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 0) \operatorname{then} (2) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 1) \operatorname{then} (1) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 2) \operatorname{then} (-(1)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 3) \operatorname{then} (-(2)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(q, 6\right) = 4) \operatorname{then} (-(1)) \operatorname{else} (1)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.periodic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six values are 2, 1, -1, -2, -1, 1. This is the real correction normally obtained by a cubic root-of-unity filter.

**Theorem 1.12 (The exact trisection filter).**

$$\forall (n: \mathbb{N}), 3 \cdot \operatorname{residue}\left(n, 0\right) = (2)^{n} + \operatorname{periodic}\left(n\right) \land \left(3 \cdot \operatorname{residue}\left(n, 1\right) = (2)^{n} + \operatorname{periodic}\left(n + 4\right) \land 3 \cdot \operatorname{residue}\left(n, 2\right) = (2)^{n} + \operatorname{periodic}\left(n + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.residue_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pascal's recurrence couples the three residue sums. Induction and the six possible residues of n determine all three correction terms simultaneously.

**Definition 1.13 (The first marked moment).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{weighted}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot k \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.weighted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplying by k marks one selected element of a binomial subset.

**Definition 1.14 (The second marked moment).**

$$\forall (n: \mathbb{N}), \forall (r: \mathbb{N}), \operatorname{second}\left(n, r\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Nat.choose}\left(n, k\right) \cdot k \cdot \left(k - 1\right) \cdot \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = r) \operatorname{then} (1) \operatorname{else} (0))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor k(k-1) marks an ordered pair of distinct selected elements. This subtraction takes place in the integers.

**Definition 1.15 (The first-moment difference).**

$$\forall (n: \mathbb{N}), \operatorname{A}\left(n\right) = \operatorname{weighted}\left(n, 0\right) - 2 \cdot \operatorname{weighted}\left(n - 1, 0\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(n) is the first marked trisection sum at n minus twice its value at n-1.

**Definition 1.16 (The weighted difference).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), \operatorname{T}\left(n, N\right) = \left(N - 1\right) \cdot \operatorname{A}\left(n\right) - \left(\operatorname{second}\left(n, 0\right) - 2 \cdot \operatorname{second}\left(n - 1, 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Using k(N-k)=(N-1)k-k(k-1), this is the weighted trisection difference. The factors N-1 and k-1 are integer differences.

**Definition 1.17 (The first correction table).**

$$\forall (n: \mathbb{N}), \operatorname{alpha}\left(n\right) = \operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 0) \operatorname{then} (-(3 \cdot n) + 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 1) \operatorname{then} (-(3 \cdot n) + 2) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 2) \operatorname{then} (-(2)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 3) \operatorname{then} (3 \cdot n - 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 4) \operatorname{then} (3 \cdot n - 2) \operatorname{else} (2)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction alpha(n) is selected by n modulo six.

**Definition 1.18 (The second correction table).**

$$\forall (n: \mathbb{N}), \operatorname{beta}\left(n\right) = \operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 0) \operatorname{then} (-(3 \cdot n) + 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 1) \operatorname{then} (-(4)) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 2) \operatorname{then} (3 \cdot n - 8) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 3) \operatorname{then} (3 \cdot n - 4) \operatorname{else} (\operatorname{if} (\operatorname{Nat.mod}\left(n, 6\right) = 4) \operatorname{then} (4) \operatorname{else} (-(3 \cdot n) + 8)))))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction beta(n) is selected by the same residue.

**Theorem 1.19 (The first closed formula).**

$$\forall (n: \mathbb{N}), (1 \le n) \Rightarrow (3 \cdot \operatorname{A}\left(n\right) = (2)^{n - 1} + \operatorname{alpha}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.A_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing one marked element reduces the first moment to a residue sum. Substitution of the filter formula gives the stated identity, including n=1 and n=2.

**Theorem 1.20 (The weighted closed formula).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), (1 \le n) \Rightarrow (3 \cdot \operatorname{T}\left(n, N\right) = \left(N - n\right) \cdot (2)^{n - 1} + \left(N - 1\right) \cdot \operatorname{alpha}\left(n\right) - \left(n - 1\right) \cdot \operatorname{beta}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.T_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing two marked elements handles the second moment. The displayed differences N-n, N-1 and n-1 in the scalar factors are integer differences.

**Theorem 1.21 (Nonnegativity of the slope).**

$$\forall (n: \mathbb{N}), (1 \le n) \Rightarrow (0 \le \operatorname{A}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.A_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Small degrees are immediate. For n at least five, the Bernoulli estimate one_add_mul_le_pow at n-5 gives 2 to the power n-1 at least 3n-2, which dominates every negative correction.

**Theorem 1.22 (Nonnegativity of every homogeneous coefficient).**

$$\forall (n: \mathbb{N}), \forall (N: \mathbb{N}), (1 \le n) \Rightarrow ((\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow ((n < N) \Rightarrow (0 \le \operatorname{T}\left(n, N\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.T_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six residue cases reduce to the nonnegative slope and two exponential bounds against quadratics. For q=n-7, the first bound squares the Bernoulli estimate one_add_mul_le_pow at q/2, splits q into twice its natural quotient by two plus its remainder, and normalizes the two parity cases. The second bound applies the first at n-1 and normalizes the shifted quadratic.

**Definition 1.23 (Homogeneous binomial coefficients).**

$$\forall (N: \mathbb{N}), \forall (k: \mathbb{N}), \operatorname{coeff}\left(N, k\right) = \operatorname{if} (\operatorname{Nat.mod}\left(k, 3\right) = 0) \operatorname{then} (k \cdot \left(N - k\right) \cdot \operatorname{Nat.choose}\left(N, k\right)) \operatorname{else} (0)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only exponents divisible by three contribute. The scalar N-k is the real difference, and the binomial coefficient is cast to the reals. The endpoint factors make the k=0 and k=N terms zero.

**Definition 1.24 (The homogeneous trisection polynomial).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{P}\left(N, x, y\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{coeff}\left(N, k\right) \cdot (x)^{k} \cdot (y)^{N - k})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every monomial has total degree N. For N divisible by three, reflection of the exponent k exchanges x and y.

**Theorem 1.25 (Symmetric coefficients).**

$$\forall (N: \mathbb{N}), \forall (k: \mathbb{N}), (\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow ((k \le N) \Rightarrow (\operatorname{coeff}\left(N, N - k\right) = \operatorname{coeff}\left(N, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.coeff_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binomial reflection identity and divisibility by three give the required symmetry for Beta lifting.

**Definition 1.26 (Coefficients after shearing).**

$$\forall (N: \mathbb{N}), \forall (t: \mathbb{N}), \operatorname{B}\left(N, t\right) = \operatorname{Nat.choose}\left(N, t\right) \cdot \left(\left(N - 1\right) \cdot \operatorname{weighted}\left(N - t, 0\right) - \operatorname{second}\left(N - t, 0\right)\right)$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expansion P(N,x,x+d) is the sum of B(N,t)x to the power N-t times d to the power t. Exchanging the two binomial choices proves this formula.

**Definition 1.27 (The balancing derivative).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{D}\left(N, x, d\right) = \sum_{t \in \operatorname{Finset.range}\left(N\right)} (\left(N - t\right) \cdot \operatorname{Nat.choose}\left(N, t\right) \cdot \operatorname{T}\left(N - t, N\right) \cdot (x)^{N - t - 1} \cdot (d)^{t})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Collecting adjacent coefficients of the differentiated shear expansion produces this finite sum.

**Theorem 1.28 (Derivative along a constant-sum slice).**

$$\forall (N: \mathbb{N}), \forall (S: \mathbb{R}), \forall (x: \mathbb{R}), \operatorname{HasDerivAt}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{P}\left(N, s, S - s\right)), \operatorname{D}\left(N, x, S - 2 \cdot x\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.hasDerivAt_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate the finite shear expansion. The derivative coefficient is n times the corresponding binomial coefficient times T(n,N).

**Definition 1.29 (The divided derivative kernel).**

$$\forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{K}\left(N, x, d\right) = \sum_{n \in \operatorname{Finset.Icc}\left(1, N - 1\right)} (n \cdot \operatorname{Nat.choose}\left(N, n\right) \cdot \operatorname{T}\left(n, N\right) \cdot (x)^{n - 1} \cdot (d)^{N - n - 1})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the coefficient formula for the divided homogeneous balancing derivative. Its coefficients are nonnegative whenever N is divisible by three.

**Theorem 1.30 (Factorization by the imbalance).**

$$\forall (N: \mathbb{N}), (\operatorname{Nat.mod}\left(N, 3\right) = 0) \Rightarrow (\forall (x: \mathbb{R}), \forall (d: \mathbb{R}), \operatorname{D}\left(N, x, d\right) = d \cdot \operatorname{K}\left(N, x, d\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.derivative_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient at d=0 vanishes by symmetry. Reindexing the remaining terms gives d times K exactly.

**Theorem 1.31 (Strict balancing on the positive half interval).**

$$\forall (m: \mathbb{N}), (2 \le m) \Rightarrow (\operatorname{StrictMonoOn}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{P}\left(3 \cdot m, t, 1 - t\right)), \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.strictMonoOn_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x and d positive, the n=3 coefficient is strictly positive because T(3,N)=3(N-3), while every other summand is nonnegative. For 0<x<1/2, d=1-2x is positive. The mean-value theorem gives strict increase, including comparisons with the midpoint.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.A`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.A_formula`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.A_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.B`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.D`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.K`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.P`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.T`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.T_formula`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.T_nonneg`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.alpha`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.beta`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.betaMean_antiOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.coeff`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.coeff_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.derivative_expansion`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.hasDerivAt_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_eq_betaMean`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_monotoneOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.periodic`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.residue`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.residue_filter`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.second`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.strictMonoOn_slice`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.weighted`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
