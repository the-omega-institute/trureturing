# Hanna A155201 Bivariate Integrality

## Abstract

Integer coefficients of Hanna's independent-variable formal exponential.

Paul D. Hanna's OEIS A155201 comment states: More generally, it appears that for m integer, exp( Sum_{n>=1} (m^n + y)^n * x^n/n ) is a power series in x and y with integer coefficients.

**Definition 1.1 (Integer polynomial ghosts).**

$$\forall m: \mathbb{Z}, \forall k: \mathbb{N}, \operatorname{ghost}\left(m, k\right) = \left(\operatorname{Polynomial.C}\left(m^{k}\right) + Y\right)^{k}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.ghost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

For every signed integer m and natural k, ghost m k is (C(m^k)+Y)^k in Z[Y]. The polynomial variable is independent of the outer formal series variable.

**Definition 1.2 (The literal formal logarithm).**

$$\forall m: \mathbb{Z}, \forall k: \mathbb{N}, \operatorname{PowerSeries.coeff}\left(k, \operatorname{logarithmicInput}\left(m\right)\right) = \frac{1}{k} \cdot \left(\operatorname{Polynomial.C}\left(m^{k}\right) + Y\right)^{k}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.logarithmicInput` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

Its degree-k coefficient is (m^k+Y)^k/k in Q[Y]. Rational division makes the degree-zero coefficient zero. This is the formal sum over positive k, with no analytic convergence hypothesis.

**Definition 1.3 (The bivariate exponential).**

$$\forall m: \mathbb{Z}, \operatorname{exponentialSum}\left(m\right) = \operatorname{exp}\left(\operatorname{logarithmicInput}\left(m\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.exponentialSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

Substitute the zero-constant logarithmic input into PowerSeries.exp over Q[Y]. The resulting element belongs to Q[Y][[X]] and retains both independent variables.

**Definition 1.4 (All signed parameters and coefficient indices).**

$$\operatorname{claim}\left(\right) \iff \forall m: \mathbb{Z}, \forall n: \mathbb{N}, \forall j: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{Polynomial.coeff}\left(\operatorname{PowerSeries.coeff}\left(n, \operatorname{exponentialSum}\left(m\right)\right), j\right) = \operatorname{Int.cast}\left(z\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

For every integer m and natural n,j, the coefficient of X^n Y^j has an integer representative. No coefficient-integrality premise, positivity condition, scalar specialization of Y or degree cutoff occurs.

**Theorem 1.5 (Polynomial Frobenius congruences).**

$$\forall m: \mathbb{Z}, \forall p: \mathbb{N}, \forall s: \mathbb{N}, \forall t: \mathbb{N}, \operatorname{Nat.Prime}\left(p\right) \implies p^{s + 1} \mid \operatorname{ghost}\left(m, p \cdot p^{s} \cdot t\right) - \operatorname{Polynomial.expand}\left(p, \operatorname{ghost}\left(m, p^{s} \cdot t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.ghost_prime_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

For every prime p and natural s,t, p^(s+1) divides ghost(m,p*(p^s*t))-expand(p,ghost(m,p^s*t)) in Z[Y]. Reduction modulo p uses Fermat and the characteristic-p binomial formula. The existing power-divisibility lifting theorem raises the modulus, and taking the t-th power preserves divisibility.

**Theorem 1.6 (The triangular support bound).**

$$\forall m: \mathbb{Z}, \forall n: \mathbb{N}, \forall j: \mathbb{N}, n < j \implies \operatorname{Polynomial.coeff}\left(\operatorname{PowerSeries.coeff}\left(n, \operatorname{exponentialSum}\left(m\right)\right), j\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.exponential_coefficient_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

The coefficient of Y^j in the degree-n exponential coefficient vanishes when n<j. Each logarithmic row has polynomial degree at most its outer degree, this bound is preserved under multiplication, and each exponential coefficient is a finite sum of powers.

**Definition 1.7 (Positive-weight coefficient specialization).**

$$\forall M: \mathbb{N}, \forall N: \mathbb{N}, \operatorname{PowerSeries.coeff}\left(N, \operatorname{kronecker}\left(M, f\right)\right) = \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(N + 1\right), a \mapsto ifM \cdot a \le Nthen\operatorname{Polynomial.coeff}\left(\operatorname{PowerSeries.coeff}\left(a, f\right), N - M \cdot a\right)else0\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.kronecker` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

The degree-N coefficient is the finite sum over outer degrees a at most N of the coefficient of Y^(N-M*a), restricted to M*a<=N. For positive M this is the ring specialization X=T^M,Y=T.

**Theorem 1.8 (Isolation of every triangular coefficient).**

$$\forall m: \mathbb{Z}, \forall n: \mathbb{N}, \forall j: \mathbb{N}, j \le n \implies \operatorname{PowerSeries.coeff}\left(\left(n + 1\right) \cdot n + j, \operatorname{kronecker}\left(n + 1, \operatorname{exponentialSum}\left(m\right)\right)\right) = \operatorname{Polynomial.coeff}\left(\operatorname{PowerSeries.coeff}\left(n, \operatorname{exponentialSum}\left(m\right)\right), j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.kronecker_extract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

For j<=n, the coefficient of T^((n+1)*n+j) after X=T^(n+1),Y=T equals the original X^n Y^j coefficient. Smaller outer degrees require a polynomial degree beyond their support; larger outer degrees already have excessive T degree.

**Definition 1.9 (Shifted series-valued Dwork weights).**

$$\forall a: \mathbb{N}, \forall m: \mathbb{Z}, \forall r: \mathbb{N}, \operatorname{weightedGhost}\left(a, m, r\right) = \left(m^{r} + T\right)^{r} \cdot T^{a \cdot r}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.weightedGhost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

The weight is T^(a*r)*(m^r+T)^r in Z[[T]]. The existing logSum inserts an additional T^r, so its total weight is T^((a+1)*r). This shift is essential for agreement with positive-weight specialization.

**Theorem 1.10 (Full bivariate integrality).**

$$\forall m: \mathbb{Z}, \forall n: \mathbb{N}, \forall j: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{Polynomial.coeff}\left(\operatorname{PowerSeries.coeff}\left(n, \operatorname{exponentialSum}\left(m\right)\right), j\right) = \operatorname{Int.cast}\left(z\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a155201-bivariate` (proved) by `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a155201-bivariate","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A155201: full bivariate exponential integrality*. URL: <https://oeis.org/A155201>.

*Commentary.*

Fix n,j with j<=n and put M=n+1. The continuous evaluation ring homomorphism X=T^M,Y=T commutes with the formal exponential. Its logarithm equals logSum of weightedGhost with a=n; the coefficient proof explicitly matches coeff(N-r,f(r))/r with the weighted diagonal sum. For a prime p and positive r, the unit case p not dividing r is automatic. Otherwise write r=p*q and q=p^s*t with s=v_p(q). The polynomial Frobenius congruence gives p^(s+1) dividing the difference of the two weighted ghosts, since their monomial factors agree. Thus the original series-valued exp_logSum_integral_of_divisibility theorem gives an integral diagonal exponential. Coefficient isolation gives the required original coefficient. For j>n it is zero by the support bound. The n=0 boundary is included. These are formal, all-degree statements over Q[Y][[X]] for every signed integer m.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.exponentialSum`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.exponential_coefficient_support`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.ghost`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.ghost_prime_power`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.kronecker`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.kronecker_extract`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.logarithmicInput`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.weightedGhost`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality](HannaSelfSubstitutionIntegrality.md)
- Dependency: [D5/S3/Combinatorics/PowerSeries/LaurentSpecialization](../../../S3/Combinatorics/PowerSeries/LaurentSpecialization.md)
