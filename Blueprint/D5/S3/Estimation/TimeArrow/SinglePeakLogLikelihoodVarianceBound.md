# Uniform Single-Peak Log-Likelihood Variance Bound

## Abstract

The variance of a uniformly started single-peak log-likelihood path is bounded by twice its accumulated one-step information.

**Theorem 1.1 (Single-peak path variance is uniformly controlled by information).**

$$\begin {aligned}&\forall X: Type, \operatorname {Fintype}(X), chi: {X} \to \mathbb {R}, z: X, r, q \in \mathbb {R}, M \in \mathbb {N},\\ &(\forall x \in X, \operatorname {chi}(x) = 1 \lor \operatorname {chi}(x) = -1) \land \operatorname {chi}(z) = 1 \land 0 < r \land r < 1,\\ &\lvert X \rvert = 2 \cdot M \land \lvert \{x \in X \mid \operatorname {chi}(x) = 1\} \rvert = M \land 2 \leq M \land q = \frac{r}{M - 1} \Rightarrow \\ &let P = \operatorname {kernel}(chi, z, r, q, \lvert X \rvert); let k = M - 1; \\ &let I = \frac{\operatorname {phi}(r) + k \cdot \operatorname {phi}(q)}{\lvert X \rvert}; let J = \frac{\operatorname {xi}(r) - k \cdot \operatorname {xi}(q)}{\lvert X \rvert}; \\ &let v = \frac{\operatorname {psi}(r) + k \cdot \operatorname {psi}(q)}{\lvert X \rvert} - I^{{2}}; \\ &let P^{-} = (x, y) \mapsto \operatorname {P}(y, x); \\ &let L^{-} = (s, {\mathbf {x}}) \mapsto \operatorname {logLikelihoodSum}(chi, z, r, q, s, t \mapsto {\mathbf {x}}_{s - t}); \\ &(\forall u \in \mathbb {R}, \left|u\right| < 1 \Rightarrow \operatorname {psi}(u) \leq 2 \cdot \operatorname {phi}(u)) \land J \leq 0 \land v \leq 2 \cdot I \land 0 \leq I \land \\ &\forall s \in \mathbb {N}, \operatorname {pathVariance}(P, s, \operatorname {logLikelihoodSum}(chi, z, r, q, s)) \leq 2 \cdot s \cdot I \land \\ &\forall s \in \mathbb {N}, \operatorname {pathVariance}(P^{-}, s, \left(L^{-}\right)\left(s\right)) \leq 2 \cdot s \cdot I\end {aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite sign space with equally many positive and negative signs, and let z be a distinguished positive state. For a peak strength between zero and one, the compensating background strength is r divided by M minus one.

The one-edge second moment psi is at most twice the mean function phi throughout the open unit interval. The odd correction J is nonpositive, the one-edge variance v is at most 2I, and I is nonnegative.

Consequently, for every nonnegative path length, both the forward path and the reversed path have log-likelihood variance at most 2sI. Reversing the path preserves the distribution of the log-likelihood sum, and the zero-length sum has zero variance.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodVarianceBound.uniform_single_peak_log_likelihood_variance_bound`
- Dependency: [D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance](SinglePeakLogLikelihoodCovariance.md)
