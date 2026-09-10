# Cubic Odd Bisection

## Abstract

The odd coefficients of A372018 are twice the coefficients of A371364.

All series have rational coefficients and indeterminate X. The operator coeff(n,f) extracts coefficient n; constantCoeff(f) is coefficient zero. The original A372018 formula has a missing argument in A371364(); the statement here uses the approved correction A371364(n). The two OEIS entries attest the equations and the conjecture. The proof below comes from polynomial elimination.

For a polynomial p over the series ring, fixedSeries(c,p) is constructed by f(0)=c, f(k+1)=c+X*p(f(k)), taking coefficient n from f(n+1). Polynomial differences are divisible by differences of their arguments, so each iteration preserves one more coefficient. Thus the resulting series satisfies f=c+X*p(f). Here pA(Y)=3Y-Y^2+3XY^2+2X^2Y^3 and pB(Y)=8Y^2-3Y-16XY^3; Y is the polynomial variable, independent of X.

**Definition 1.1 (The cubic branch).**

$$A = 1 + 2 \cdot X \cdot \operatorname{fixedSeries}\left(1, pA\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/CubicOddBisection.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

This definition uses only the cubic equation after the substitution A=1+2XH.

**Definition 1.2 (The normalized reversion).**

$$B = \operatorname{fixedSeries}\left(1, pB\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/CubicOddBisection.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

This independent iteration rewrites B(1-4XB)^2=1-3XB as B=1+X*(8B^2-3B-16XB^3).

**Theorem 1.3 (The cubic equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (X \cdot A^{3} - A^{2} + 3 \cdot X \cdot A + 1 = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.A_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

The fixed point for H gives the original cubic after multiplication by -4X; the constant coefficient of A is one.

**Theorem 1.4 (The reversion equation).**

$$(\operatorname{constantCoeff}\left(B\right) = 1) \land (B \cdot (1 - 4 \cdot X \cdot B)^{2} = 1 - 3 \cdot X \cdot B)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.B_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

Expanding the independent fixed-point equation gives the normalized reversion equation. Taking its constant coefficient gives one.

**Theorem 1.5 (Uniqueness of the cubic branch).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies ((X \cdot f^{3} - f^{2} + 3 \cdot X \cdot f + 1 = 0) \implies (f = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.A_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

Subtract two cubic equations. Their difference is f-A times a factor whose constant coefficient is -2, so the factor is nonzero and f=A.

**Theorem 1.6 (Uniqueness of the reversion series).**

$$\forall g: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (g \cdot (1 - 4 \cdot X \cdot g)^{2} = 1 - 3 \cdot X \cdot g) \implies (g = B)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.B_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

The difference of the reversion equations is g-B times a factor with constant coefficient one. Cancellation proves uniqueness without an additional normalization hypothesis.

**Theorem 1.7 (The odd coefficient identity).**

$$\forall n: \mathbb{N}, \operatorname{coeff}\left(2 \cdot n + 1, A\right) = 2 \cdot \operatorname{coeff}\left(n, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.odd_coeff_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

Put u=A(X), v=-A(-X), and s=u+v. Both u and v satisfy the cubic, and u-v has constant coefficient two. Subtraction and cancellation give X*(u^2+uv+v^2)-s+3X=0. Subtracting u times this equation from the cubic for u gives uv*(1-Xs)+1=0. Elimination now gives s*(1-Xs)^2=4X-3X^2*s. The series 4X*B(X^2) satisfies the same equation. Its difference from s factors through a series of constant coefficient one, so s=4X*B(X^2). Coefficient 2n+1 on the left is twice that of A; on the right it is four times coefficient n of B. Dividing by two proves the identity for every natural n.

**Theorem 1.8 (The identity for arbitrary equation witnesses).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall g: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies ((X \cdot f^{3} - f^{2} + 3 \cdot X \cdot f + 1 = 0) \implies ((g \cdot (1 - 4 \cdot X \cdot g)^{2} = 1 - 3 \cdot X \cdot g) \implies (\forall n: \mathbb{N}, \operatorname{coeff}\left(2 \cdot n + 1, f\right) = 2 \cdot \operatorname{coeff}\left(n, g\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/CubicOddBisection.odd_coeff_identity_of_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seiichi Manyama; R. J. Mathar (2024). *OEIS A372018: an algebraic generating function and its odd-index conjecture*. URL: <https://oeis.org/A372018>.

*Acknowledgement.* Seiichi Manyama (2024). *OEIS A371364: normalized reversion of x(1-4x)^2/(1-3x)*. URL: <https://oeis.org/A371364>.

*Commentary.*

Uniqueness identifies any two witnesses of the original equations with the independently constructed A and B, so their coefficients satisfy the same identity.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.A_equation`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.A_unique`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.B`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.B_equation`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.B_unique`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.odd_coeff_identity`
- Truth anchor: `D5/S1/Recurrence/Algebraic/CubicOddBisection.odd_coeff_identity_of_equations`
