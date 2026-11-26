# Scalar Strassen equivalence with finite first moments

## Abstract

For arbitrary real Borel probability laws with finite first moments, convex order is equivalent to one actual martingale coupling with exact marginals and native joint conditional expectation.

**Theorem 1.1 (Global convex tests and one native martingale joint).**

$$\begin{aligned}\forall mu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall nu: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{IntegrableIdentity}\left(mu\right) \Rightarrow\operatorname{IntegrableIdentity}\left(nu\right) \Rightarrow\\(\operatorname{Mean}\left(mu\right)=\operatorname{Mean}\left(nu\right) \land\\\forall phi: \mathbb{R}\to\mathbb{R}, \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{univ}\left(\right), phi\right) \Rightarrow\operatorname{IntegrableAbs}\left(phi, mu\right) \Rightarrow\operatorname{IntegrableAbs}\left(phi, nu\right) \Rightarrow\operatorname{Integral}\left(phi, mu\right) \leq \operatorname{Integral}\left(phi, nu\right))\\\iff \exists pi: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\times\mathbb{R}\right), \operatorname{Pushforward}\left(pi, \operatorname{fst}\left(\right)\right)=mu \land\\\operatorname{Pushforward}\left(pi, \operatorname{snd}\left(\right)\right)=nu \land\operatorname{NativeConditionalMean}\left(pi\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NoncompactStrassen.strassen_iff` (`✓ std3`). ∎

*Citation.* Lasse Leskelä and Matti Vihola (2017). *Conditional convex orders and measurable martingale couplings*. DOI: [10.3150/16-BEJ827](https://doi.org/10.3150/16-BEJ827). URL: <https://arxiv.org/abs/1404.0999>.

*Commentary.*

All laws are Borel probability measures. IntegrableIdentity(rho) means that x maps to x is integrable against the underlying measure of rho. Mean is that identity integral. Integral(phi,rho) is the real Bochner integral; IntegrableAbs(phi,rho) means integrability of x maps to |phi(x)|. The test phi is globally real-valued and convex on all of the real line. It is quantified only when its absolute value is integrable under both mu and nu.

Pushforward(pi,fst)=mu and Pushforward(pi,snd)=nu are equalities of the underlying pushforward measures, not approximate marginal constraints. NativeConditionalMean(pi) means pi.toMeasure[Prod.snd | (borel R).comap Prod.fst] equals Prod.fst almost everywhere under pi.toMeasure. The existential quantifier chooses one real-plane probability joint before this conditional expectation is asserted. There is no support, finite-support, density, nonatomicity or supplied-coupling premise. The conclusion asserts neither uniqueness nor an algorithm, vector or process extension.

For existence, integrable hinge tests give stop-loss order. Synchronized equal-quantile-bin means preserve both original means and finite convex order. The finite majorization supplier constructs actual martingale joint laws with these exact finite marginals. Their marginals converge weakly and have genuine uniform absolute-first-moment tails. Tightness of the two marginal ranges implies tightness of the joint range. Prokhorov compactness chooses one subsequence and one joint limit, whose two exact marginals follow from continuity of pushforwards.

The exact limiting marginals transfer coordinate integrability to that same joint. The first-moment weak-limit theorem passes every bounded continuous displacement integral to it, using clipping of the integrand and the actual uniform coordinate tails. The shared finite weighted-measure argument extends zero tests to bounded Borel functions, and the original conditional-expectation bridge gives the native joint-a.e. martingale identity. No re-extraction depends on the test function.

Conversely, the native conditional mean and the conditional-expectation integral identity give equal means. Global real convexity implies continuity. Transfer the given absolute test integrability through each exact marginal, apply conditional Jensen to the second coordinate, replace its conditional mean by the first coordinate, and integrate. This yields precisely the stated common-integrability convex-test order. The result is the scalar finite-first-moment Strassen theorem; no literature originality is claimed.

## References

- Truth anchor: `D5/S3/Analytic/Probability/NoncompactStrassen.strassen_iff`
- Dependency: [D5/S3/Analytic/Probability/CompactStrassen](CompactStrassen.md)
- Dependency: [D5/S3/Analytic/Probability/FirstMomentWeakLimit](FirstMomentWeakLimit.md)
