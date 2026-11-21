# An exponential growth bound and an exact slope criterion

## Abstract

Zeta zeros and the signed prime tail primitive

Write θ for the Chebyshev count with weight log p at each prime p. The tail is integrated all the way to infinity. Both the tail and the outer interval integral keep the signs of their integrands.

**Definition 1.1 (The signed primitive of the actual prime tail).**

$$\operatorname{thetaTail}\left(x\right) = \int_{x}^{\infty}\frac{\theta(u) - u}{u^{2}}\,du\qquad\operatorname{P}\left(T\right) = \int_{2}^{\operatorname{exp}\left(T\right)}\frac{\operatorname{thetaTail}\left(x\right)}{\sqrt{x}}\,dx$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.signedPrimePrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner integral is the set integral on (x,∞). The outer integral is the oriented interval integral with lower endpoint 2 and upper endpoint exp(T).

**Definition 1.2 (Eventual growth with arbitrary positive slack).**

$$\operatorname{HasExponentBound}\left(b, f\right) \Leftrightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\exists Y \in \mathbb{R},\; \forall T \in \mathbb{R},\; Y \le T \Rightarrow \left|f(T)\right| \le C\,\operatorname{exp}\left((b + e - \frac{1}{2}) \cdot T\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.HasExponentBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parameter b is real and f maps reals to reals. The constant and the eventual threshold can depend on the positive slack e.

**Theorem 1.3 (The growth hypothesis bounds every zero's real part).**

$$\forall b \in \mathbb{R},\; \left(\left(\frac{1}{2} \le b \land b < 1\right) \land \operatorname{HasExponentBound}\left(b, P\right)\right) \Rightarrow \left(\forall r \in \mathbb{C},\; \zeta(r) = 0 \Rightarrow \Re(r) \le b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.zeta_zero_re_le_of_signedPrimePrimitive_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed 1/2 ≤ β < 1 (written b in the formulas), an eventual bound on the signed primitive at exponential rate β+ε−1/2 for every ε>0 excludes zeta zeros with real part greater than β. The prime-power correction to the primitive is at most linear in T. This gives the same growth condition for the complete primitive. Integration by parts continues the Mangoldt transform to Re(s)>β. There the pole-removed zeta function satisfies a first-order analytic equation and is nonzero at s=2, so it stays nonzero on the half-plane.

**Theorem 1.4 (The Riemann hypothesis and slope minus two from 5040).**

$$RiemannHypothesis \Leftrightarrow \lim_{T\to\infty}\frac{\int_{5040}^{\operatorname{exp}\left(T\right)}\frac{\operatorname{thetaTail}\left(x\right)}{\sqrt{x}}\,dx}{T} = -2$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.rh_iff_signedPrimePrimitive_slope_from_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoints in the criterion are the real number 5040 and exp(T). The divisor is T. The complete Chebyshev tail minus thetaTail(x), multiplied by √x, tends to +2 because of the actual prime powers. Under RH the oscillatory complete zero series has mean zero and its residual tends to zero. Subtracting the prime-power contribution gives prime-only slope −2. Moving the lower endpoint from 2 to 5040 changes the unnormalized integral by a fixed amount for large T, which vanishes after division by T.

Conversely, the limit gives a linear bound for the signed primitive from 2. Apply the growth theorem at β=1/2 and use the functional equation to obtain RH.

**Theorem 1.5 (Either eventual affine bound is equivalent to RH).**

$$\operatorname{W}\left(T\right) = \int_{5040}^{\operatorname{exp}\left(T\right)}\frac{\operatorname{thetaTail}\left(x\right)}{\sqrt{x}}\,dx\qquad(RiemannHypothesis \Leftrightarrow \left(\exists A \in \mathbb{R},\; \exists B \in \mathbb{R},\; \exists Y \in \mathbb{R},\; \forall T \in \mathbb{R},\; Y \le T \Rightarrow \operatorname{W}\left(T\right) \le A \cdot T + B\right)) \land (RiemannHypothesis \Leftrightarrow \left(\exists A \in \mathbb{R},\; \exists B \in \mathbb{R},\; \exists Y \in \mathbb{R},\; \forall T \in \mathbb{R},\; Y \le T \Rightarrow A \cdot T + B \le \operatorname{W}\left(T\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.rh_iff_signedPrimePrimitive_affine_bounds_from_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write W(T) for the signed, unnormalized interval integral from 5040 to exp(T) of thetaTail(x)/√x. Here thetaTail(x) is the set integral of (θ(u)−u)/u² on (x,∞), and θ(u) sums log p over primes p≤u. The upper and lower comparisons each have their own real coefficients A, B and their own eventual threshold. Under RH the slope −2 gives the eventual upper bound −T and the eventual lower bound −3T.

For large T, the primitive from 2 equals W(T) plus the fixed signed interval integral from 2 to 5040. The sum of this prime primitive and the signed complete Mangoldt primitive in log coordinates has absolute value at most DT. A prime upper bound therefore yields an affine majorant of the negative complete primitive. A prime lower bound yields an affine majorant of the complete primitive.

The integrable Chebyshev error kernel gives initial exponential control. On a late half-line, the gap between the affine majorant and the signed complete primitive is nonnegative. Damping it by exp(−3t/2) gives a finite positive measure. After the shift s=z+2, the real-regular meromorphic Mangoldt continuation supplies a continuation of the gap transform to Re(z)>−3/2. Positive Laplace convergence makes the actual gap transform holomorphic there. Subtract the gap transform from the affine transform, divide by the sign chosen for the complete primitive, and restore the finite integration intervals. Integration by parts then recovers a holomorphic complete Mangoldt transform on Re(s)>1/2.

The first-order equation for the pole-removed zeta function propagates from Re(s)>1 across this half-plane. The function is nonzero at s=2, so the equation excludes zeta zeros in the right half of the critical strip. The functional equation gives RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.HasExponentBound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.rh_iff_signedPrimePrimitive_affine_bounds_from_5040`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.rh_iff_signedPrimePrimitive_slope_from_5040`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.signedPrimePrimitive`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion.zeta_zero_re_le_of_signedPrimePrimitive_exponent`
- Dependency: [D5/S3/Analytic/Laplace/EulerPoleObstruction](../../../Analytic/Laplace/EulerPoleObstruction.md)
- Dependency: [D5/S3/Analytic/Laplace/PositiveLaplaceContinuation](../../../Analytic/Laplace/PositiveLaplaceContinuation.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent](CompleteMangoldtLaurent.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular](CompleteMangoldtRealRegular.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](../../Probability/AnalyticLogarithmicContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
