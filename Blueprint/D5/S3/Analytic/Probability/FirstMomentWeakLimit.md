# Displacement integrals and first-moment tails

## Abstract

Uniform absolute first-moment tails permit displacement tests to pass to a weak limit of real-plane probability laws.

Every law is a Borel probability measure on the real plane. The notation measure(rho) denotes its underlying measure, piSeq(n) denotes the nth law, and Tail(i,R,rho) is the integral of the absolute ith coordinate over the set where that absolute coordinate exceeds R. DisplacementIntegral(h,rho) is the integral of (y-x)h(x) against rho. The limit and every member of the sequence have both coordinates integrable. No common compact support, density, finite support, prescribed marginals or coupling premise is required.

**Theorem 1.1 (Convergence for every bounded continuous first-coordinate test).**

$$\begin{aligned}\forall piSeq: \mathbb{N} \to \operatorname{ProbabilityMeasure}\left(\mathbb{R}\times\mathbb{R}\right), \forall pi: \operatorname{ProbabilityMeasure}\left(\mathbb{R}\times\mathbb{R}\right), \operatorname{Tendsto}\left(piSeq, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(pi\right)\right) \Rightarrow\\(\forall n: \mathbb{N}, \operatorname{Integrable}\left(\operatorname{fst}\left(\right), \operatorname{measure}\left(\operatorname{apply}\left(piSeq, n\right)\right)\right) \land \operatorname{Integrable}\left(\operatorname{snd}\left(\right), \operatorname{measure}\left(\operatorname{apply}\left(piSeq, n\right)\right)\right)) \Rightarrow\\\operatorname{Integrable}\left(\operatorname{fst}\left(\right), \operatorname{measure}\left(pi\right)\right) \Rightarrow\operatorname{Integrable}\left(\operatorname{snd}\left(\right), \operatorname{measure}\left(pi\right)\right) \Rightarrow\\(\forall epsilon: \mathbb{R}, 0<epsilon \Rightarrow\exists R: \mathbb{R}, 0<R \land \forall n: \mathbb{N}, \operatorname{Tail}\left(1, R, \operatorname{apply}\left(piSeq, n\right)\right)+\operatorname{Tail}\left(2, R, \operatorname{apply}\left(piSeq, n\right)\right)<epsilon) \Rightarrow\\\forall h: \mathbb{R} \to \mathbb{R}, \operatorname{Continuous}\left(h\right) \Rightarrow(\exists M: \mathbb{R}, 0 \leq M \land \forall x: \mathbb{R}, |\operatorname{apply}\left(h, x\right)| \leq M) \Rightarrow\\\operatorname{Tendsto}\left(n \mapsto \operatorname{DisplacementIntegral}\left(h, \operatorname{apply}\left(piSeq, n\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{DisplacementIntegral}\left(h, pi\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FirstMomentWeakLimit.tendsto_integral_displacement` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Put c_R(t)=max(-R,min(R,t)). The bounded continuous test is (c_R(y)-c_R(x))h(x); the factor h uses the original first coordinate. Every probability law remains the same. For nonnegative R at most r, the absolute error of a coordinate clipped at r is bounded by its absolute value times the indicator that its absolute value exceeds R. Integration bounds the displacement-test error by the sum of the two coordinate tails times the bound on h.

For the limit law, dominated convergence applies as the natural-number clipping radius grows: the integrable majorant is (|y|+|x|)M. Choose one sufficiently large radius for the uniform sequence error and the limit error. Weak convergence supplies convergence of the bounded continuous clipped integrals at that radius, and the triangle inequality yields convergence of the original integrals. This is the classical truncation method for uniform integrability; it is a mathematical application of that method, with no originality claim.

In martingale transport this result preserves zero continuous displacement integrals for a previously extracted single weak limit. It supplies neither the construction of ordered finite approximations nor their uniform tails, tightness, subsequence extraction, marginal identification, or the passage from continuous tests to native conditional expectation. Those require separate results.

## References

- Truth anchor: `D5/S3/Analytic/Probability/FirstMomentWeakLimit.tendsto_integral_displacement`
