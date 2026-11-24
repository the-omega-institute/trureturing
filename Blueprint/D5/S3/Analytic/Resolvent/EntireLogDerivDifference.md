# Two-Point Logarithmic Derivative Formula

## Abstract

Below quadratic growth, the zero divisor determines logarithmic derivative differences.

**Theorem 1.1 (Translation and normalization of a power growth bound).**

$$0\le D\land\forall z \in Complex,\; \operatorname{norm}\left(\operatorname{G}\left(z\right)\right)\le \operatorname{exp}\left(D(1+\operatorname{norm}\left(z\right))^{\operatorname{max}\left(alpha, 0\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.normalized_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be any complex-valued function on the complex plane, and let a be any complex number. For arbitrary real alpha and C, assume norm(F(z)) <= exp(C*(1+norm(z))^alpha) for every complex z. Set G(z) = inverse(F(a))*F(a+z) and set beta=max(alpha,0). The explicit constant D=max(C,0)*(1+norm(a))^beta+max(-log(norm(F(a))),0) is nonnegative and gives the displayed bound for every z. Neither analyticity, a nonzero value at a, positivity of C, nor an upper bound on alpha is required.

The triangle inequality bounds 1+norm(a+z) by (1+norm(a))*(1+norm(z)). Raising the exponent to max(alpha,0), replacing C and -log(norm(F(a))) by their nonnegative parts give this D. When F(a)=0, the inverse-zero convention makes G identically zero. The assertion concerns this normalized growth bound alone.

**Theorem 1.2 (Quantitative summability about every center).**

$$\operatorname{Summable}\left(rho:\operatorname{Zeros}\left(F\right)\mapsto \operatorname{div}\left(\operatorname{m}\left(rho\right), 1+\operatorname{norm}\left(rho-a\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_zero_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume F is differentiable over the complex numbers everywhere. Let alpha and C be arbitrary reals with alpha<2, and suppose norm(F(z)) <= exp(C*(1+norm(z))^alpha) for every z. For every complex center a, the displayed family is summable, indexed by the subtype of all zeros of F. Here m(rho) is analyticOrderNatAt F rho, cast to the reals. No restriction on C or nonvanishing hypothesis at a is imposed. Write S_a for the sum and beta=max(alpha,0). For every center b, S_a <= (1+norm(a-b)+norm(a-b)^2)*S_b. For every b with F(b) nonzero, set D_b=max(C,0)*(1+norm(b))^beta+max(-log(norm(F(b))),0) and H_b=2*D_b*(5/2)^beta/((2-beta)*log(3/2)). Then S_b <= H_b and S_a <= (1+norm(a-b)+norm(a-b)^2)*H_b.

For nonzero F, connectedness of the complex plane and the identity theorem make every analytic order finite. A nonzero base point normalizes F. Jensen's radial count bounds the total zero multiplicity in a radius-r disk by a constant times r^beta, where beta=max(alpha,0)<2. Apply the weighted inverse-power count estimate to g(rho)=sqrt(1+norm(rho)^2), with threshold one and power two. Its integral majorant gives H_b. A quadratic comparison transfers summability and the quantitative bound from that base point to every center, including a zero.

If F is identically zero, analyticOrderNatAt is zero because the infinite analytic order is sent to zero by its natural-number projection; the asserted family is then zero. This convention does not give a finite analytic multiplicity to the zero function. The estimate is a classical part of the Hadamard theory of entire functions, here obtained from a radial Jensen bound and a direct inverse-power count estimate. At order two its integral majorant ceases to converge; a quadratic count alone does not imply this inverse-square summability.

**Theorem 1.3 (The regular part vanishes linearly at the center).**

Lean statement: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.centered_cf`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.centered_cf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be analytic on a neighborhood of the closed complex unit disk, with f(0) = 1. Let B be real, at least two, and bound norm(f(w)) by B whenever norm(w) is at most 24/25. Divide out the zeros within radius 22/25, with their analytic multiplicities, and write Cf for the resulting regular factor. For every complex z with norm(z) at most 83/100, the norm of logDeriv(Cf)(z) minus logDeriv(Cf)(0) is at most ((44795000 times log(B) plus norm(logDeriv(Cf)(0))) divided by (83/100)) times norm(z).

Finite analytic factorization makes the regular factor nonzero inside the divided disk. Borel--Caratheodory bounds its logarithmic derivative on the smaller disk. Subtracting the central value and applying Schwarz preserves the actual central norm in the coefficient and produces the factor norm(z) in the open disk. On its boundary the closed-disk bound and triangle inequality give the same estimate. Bounding the central norm by 44795000 times log(B) recovers the coefficient twice that constant used downstream. After a physical dilation this supplies the second inverse-radius factor needed in the two-point logarithmic derivative formula. The radii and numerical coefficient express one explicit estimate; no optimality of these constants is asserted.

**Theorem 1.4 (An explicit finite-radius truncation error).**

Lean statement: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_logDeriv_difference_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_logDeriv_difference_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be analytic near the closed disk centered at a with radius R, with F(a) and F(s) nonzero. For any real beta>=0 and any real D assume norm(inverse(F(a))*F(a+z)) <= exp(D*(1+norm(z))^beta) for every complex z with norm(z)<=(24/25)*R. Here R is real and norm(s-a)<=(83/100)*R, which implies R>=0. Let t be a Finset of the zero subtype, containing exactly those rho with norm(rho-a)<=(22/25)*R. The norm of logDeriv(F)(s)-logDeriv(F)(a) minus the sum over t of m(rho)*(inverse(s-rho)-inverse(a-rho)) is at most (2*44795000/(83/100))*log(max(2,exp(D*(1+(24/25)*R)^beta)))*norm(s-a)/R^2. Since R>=0 puts z=0 in this disk, the growth bound implies D>=0. No separate sign assumption on D or beta<2 assumption is required.

Finite zero factorization identifies the difference with the cutoff sum plus the scaled regular-factor remainder. The centered Schwarz estimate bounds that remainder. At R=0 the condition forces s=a and both sides are zero. The infinite-sum theorem uses this public estimate with beta=max(alpha,0) and the explicit normalization constant supplied by normalized_growth.

**Theorem 1.5 (The multiplicity-weighted two-point sum).**

$$\sum_{\rho:F(\rho)=0}m_{\rho}(\frac{1}{s-\rho}-\frac{1}{a-\rho})=\frac{F'(s)}{F(s)}-\frac{F'(a)}{F(a)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_logDeriv_difference_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be an entire complex function. Let alpha and C be real numbers, with alpha strictly less than two, and assume for every complex z that norm(F(z)) is at most exp(C(1 + norm(z))^alpha). The coefficient C can be any real number. At complex points a and s require F(a) and F(s) to be nonzero. The sum ranges over the subtype of all distinct complex zeros of F. Its multiplicity m at rho is analyticOrderNatAt F rho. The displayed equality asserts HasSum for this whole family, and the combined summands are absolutely summable.

This is the classical two-point consequence of Hadamard theory for entire functions of order below two, expressed by an explicit power growth bound. The proof uses finite disk factorizations. Normalizing F(a + Rw) by F(a) preserves its analytic zero multiplicities. A nonzero value at a and connectedness of the complex plane ensure that every analytic order is finite. The zeros in each bounded disk form a finite set.

A radial zero count and its inverse-power estimate establish inverse-square summability without using this identity. Outside a bounded set, the norm of each two-point summand is at most four times norm(s-a) times m divided by 1 + norm(rho-a)^2. Removing the finite zero divisor on the disk of radius (22/25)R leaves an analytic nonzero factor. The centered Schwarz estimate bounds its physical remainder by (2 times 44795000 divided by (83/100)) times log(B_R) times norm(s-a) divided by R^2, where B_R = max(2,exp(D(1+(24/25)R)^beta)) and beta = max(alpha,0) is less than two. Monotonicity bounds B_R by 2 exp(D(1+R)^beta), so the remainder tends to zero. Finite cutoff exhaustion therefore identifies the sum.

The strict quadratic boundary is essential. The zero-free entire function F(z) = exp(c(z-1/2)^2) has logarithmic derivative difference 2c(s-a). For c nonzero and distinct a and s this is nonzero, whereas the zero sum is empty. In particular c = 1, a = 1/2 and s = 3/2 give difference two. Thus allowing alpha = 2 generally invalidates the formula. The two nonvanishing conditions ensure the logarithmic derivatives are evaluated away from their poles.

## References

- Truth anchor: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.centered_cf`
- Truth anchor: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_logDeriv_difference_hasSum`
- Truth anchor: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_logDeriv_difference_truncation`
- Truth anchor: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.entire_zero_summable`
- Truth anchor: `D5/S3/Analytic/Resolvent/EntireLogDerivDifference.normalized_growth`
- Dependency: [D5/S3/Analytic/Dilation/ScalarUnitDressing](../Dilation/ScalarUnitDressing.md)
- Dependency: [D5/S3/Weil/ZetaExplicit/Landau](../../Weil/ZetaExplicit/Landau.md)
- Dependency: [D5/S3/Weil/ZetaTail/PowerCountTail](../../Weil/ZetaTail/PowerCountTail.md)
