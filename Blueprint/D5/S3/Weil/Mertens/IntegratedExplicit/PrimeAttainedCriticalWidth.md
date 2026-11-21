# Critical width at an attained zeta abscissa

## Abstract

Critical width for prime-tail negative mass

**Theorem 1.1 (The zero set of the lower mass limit).**

$$\forall rho \in \mathbb{C},\; \operatorname{NontrivialZero}\left(rho\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(rho\right) \Rightarrow \left(\left(\forall z \in \mathbb{C},\; \operatorname{NontrivialZero}\left(z\right) \Rightarrow \operatorname{Re}\left(z\right) \le \operatorname{Re}\left(rho\right)\right) \Rightarrow \exists! W^{*}: \mathbb{R}, 0 < W^{*} \land \left(\forall W \in \mathbb{R},\; 0 \le W \Rightarrow \left(\operatorname{liminf}_{B \in \mathbb{R}, B \to +\infty} \frac{\operatorname{N}\left(B \cdot \operatorname{exp}\left(-W\right), B\right)}{B^{\operatorname{Re}\left(rho\right) - \frac{1}{2}}} = 0 \Leftrightarrow W \le W^{*}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth.prime_tail_zero_liminf_iff_le_critical_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

Let θ(u) sum log q over the primes q≤u. Write Qθ(x) for the integral of (θ(u)−u)/u² over u>x, the tail in Zhao's equation (14). Let N(A,B) be the integral of max(−Qθ(x),0)/√x from A to B. For a nontrivial zeta zero ρ attaining the largest real part β>1/2, set p=β−1/2 and M_W(B)=N(B exp(−W),B)/B^p for real W≥0. The lower limit a(W) is taken through real B→+∞.

The normalized complete tail is approximated by the real part of the maximal-line series with a minus sign. The series is bounded by the sum of the coefficient norms, and the normalized prime-power correction tends to zero. Thus some C>0 bounds |x^(1−β) Qθ(x)| for all sufficiently large x, and the integrand of N is at most C x^(p−1) there.

For fixed 0≤U≤W and sufficiently large B, the two windows differ by the segment from B exp(−W) to B exp(−U). Integrating the power bound on that segment gives 0≤M_W(B)−M_U(B)≤(C/p)(exp(−pU)−exp(−pW))≤C(W−U), with C independent of U and W. Taking U=0 also bounds each late normalized mass by C/p. The corresponding lower limits satisfy 0≤a(W)−a(U)≤C(W−U).

Recurring positive prime-tail windows give a positive width where a vanishes. The fixed-ratio lower bound at exponent p gives a finite width where a is positive. Monotonicity bounds the zero set from above, and the width estimate makes a vanish at its supremum W*. Thus the zero set is exactly [0,W*]. At W* the normalized mass is arbitrarily small on arbitrarily late windows. The value of W* and the occurrence of an exact zero-mass window there remain open.

Kaczorowski and Ramaré discuss the translation hull in the uniform norm in §4, pp. 289–290 (DOI 10.4064/aa106-3-6). Lee et al., Appendix A.2 (arXiv:1907.07017), connect hull compactness, relatively dense almost periods, and the Bohr compactification. Eremenko and Novikov study sign-change density for functions with a spectral gap (DOI 10.1073/pnas.0302874101). The estimate here integrates the weighted prime-tail negative part over the segment added by widening.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth.prime_tail_zero_liminf_iff_le_critical_width`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows](PrimeAttainedShortWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass](PrimeFixedRatioWindowMass.md)
