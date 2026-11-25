# Central Gaussian profiles from pair moments

## Abstract

The ordered pair fourth moment controls the squared Fourier score and provides a Gaussian central window.

For a finite real frequency family g and real weights w, let W be the total weight, Q(t) the squared norm of the complex score, and M(k) the sum over all ordered pairs of w(i)w(j)(g(i)-g(j))^k. PairNonnegative(w) means all pair products are nonnegative. The formulas allow varying finite families indexed by degree n, using the subscript n for the corresponding quantities.

**Theorem 1.1 (Global fourth-moment control).**

$$\operatorname{PairNonnegative}\left(w\right) \Rightarrow \left(0 \le \operatorname{Q}\left(t\right) - \left(W^{2} - \frac{\operatorname{M}\left(2\right) \cdot t^{2}}{2}\right) \land \operatorname{Q}\left(t\right) - \left(W^{2} - \frac{\operatorname{M}\left(2\right) \cdot t^{2}}{2}\right) \le \frac{\operatorname{M}\left(4\right) \cdot t^{4}}{24}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the squared norm of the score as the finite weighted cosine sum over ordered frequency differences. The scalar cosine remainder is between zero and x^4/24 by the cosine double-angle formula, the global scaled sine-square error and the quadratic cosine lower bound. Sum the scalar inequalities with the nonnegative pair products.

**Theorem 1.2 (Central Gaussian power limit).**

$$\left(\operatorname{Eventually}\left(\operatorname{PairNonnegative}\left(w\right)\right) \land \left(\operatorname{Eventually}\left(W = 1\right) \land \left(\operatorname{Eventually}\left(0 < \operatorname{M}\left(2\right)\right) \land \operatorname{Tendsto}\left(R, atTop, \operatorname{nhds}\left(0\right)\right)\right)\right)\right) \Rightarrow \operatorname{Tendsto}\left(\operatorname{P}\left(u\right), atTop, \operatorname{nhds}\left(\operatorname{exp}\left(0 - u^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_gaussian_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume eventually the pair products are nonnegative, W_n=1, and M_n(2)>0. Write s_n=sqrt(n M_n(2)/2), R_n=M_n(4)/(n M_n(2)^2), and P_n(u)=Q_n(u/s_n)^n. For positive n the finite estimate after rescaling bounds n(Q_n(u/s_n)-1)+u^2 between zero and u^4 R_n/6. If R_n tends to zero, the latter error tends to zero at each fixed u. The standard exponential power limit yields P_n(u) tending to exp(-u^2).

**Theorem 1.3 (Gaussian envelope on a fourth-moment window).**

$$\left(\operatorname{PairNonnegative}\left(w\right) \land \left(W = 1 \land \left(0 < n \land \left(0 < \operatorname{M}\left(2\right) \land u^{2} \cdot \operatorname{M}\left(4\right) \le 3 \cdot n \cdot \operatorname{M}\left(2\right)^{2}\right)\right)\right)\right) \Rightarrow \operatorname{P}\left(u\right) \le \operatorname{exp}\left(\frac{0 - u^{2}}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_gaussian_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a single normalized finite family and positive n, write s=sqrt(n M(2)/2) and P(u)=Q(u/s)^n. If u^2 M(4)<=3n M(2)^2, the quartic error is at most u^2/2 after multiplication by n. Hence Q(u/s)<=1-u^2/(2n)<=exp(-u^2/(2n)). Raising to the nth power is valid because Q is a squared norm. This provides an integrable Gaussian bound across every admissible central window. Noncentral contributions to whole-line Fejer moments require additional estimates.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_gaussian_envelope`
- Truth anchor: `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_gaussian_limit`
- Truth anchor: `D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit.score_quartic`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit](CyclicGrowingFrontFit.md)
- Dependency: [D5/S3/Fourier/Concentration/FejerCollisionVariance](../Concentration/FejerCollisionVariance.md)
