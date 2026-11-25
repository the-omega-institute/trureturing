# Lattice convolution and variance

## Abstract

A global cosine minorant and lattice-period averaging bound the collision mass of degree sums.

**Theorem 1.1 (A pointwise lower bound for the score norm).**

$$\forall j\in J, 0\leq \operatorname{w}\left(j\right)\quad B\leq V \cdot W \Rightarrow W \cdot \operatorname{max}\left(0, 1 - \frac{V \cdot t^{2}}{2}\right) \le \lvert\operatorname{S}\left(t\right)\rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.score_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite type, g and w real functions on J, a and V real, and t any real time. Write W=Σ w(j), B=Σ w(j)(g(j)−a)², and S(t)=Σ w(j) exp(i g(j)t), all sums over J. The weights are nonnegative and the moment budget is B≤VW.

Subtracting a from each frequency rotates the score by a unit phase. Its centered real part is Σ w(j) cos((g(j)−a)t). Use the global cosine bound cos(x)≥1−x²/2, multiply by the nonnegative weights, and insert the moment budget. The norm dominates both the real part and zero.

**Theorem 1.2 (Exact averaging over a lattice period).**

$$0< h, 0\leq eta< h \Rightarrow \operatorname{Q}\left(p\right) = E$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.lattice_period_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be finite with decidable equality, a(j) integers, w(j) real weights of either sign, b real, h>0 and g(j)=b+h a(j). For natural degree p, let E be tailCollisionMass g w p η. Set A=π/h and define Q(p) as the mean of |S(t)|^(2p) over [−A,A], with S the complex score for g and w.

The exact expansion in `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.moment_eq_pair` writes the score power as the finite cosine pair sum of the monomial frequencies. Each such frequency is pb plus h times an integer. The common pb cancels in every difference. The mean of the remaining cosine is sinc(πd) for an integer d, equal to one at d=0 and zero elsewhere. For 0≤η<h the closed collision band retains these same pairs.

**Theorem 1.3 (Finite collision lower bound for lattice convolutions).**

$$\forall j\in J, 0\leq \operatorname{w}\left(j\right)\quad B\leq V \cdot W, 0< h, 0\leq eta \Rightarrow W^{2 \cdot p} \cdot \operatorname{R}\left(p, V, A\right) \le E$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.lattice_collision_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the affine lattice frequencies and notation of the preceding statement, now with w(j)≥0, arbitrary real center a, and B=Σ w(j)(g(j)−a)²≤VW where W=Σ w(j). Let R(p,V,A) be the mean over [−A,A] of max(0,1−Vt²/2)^(2p). The resolution η is nonnegative.

Raise the pointwise score bound to the even natural power 2p, then integrate over a full lattice period. Since the pair weights are nonnegative, increasing the closed-band radius from zero to η can only increase collision mass. The finite integral retains the contribution of the convolution structure. At zero variance budget it gives the full mass W^(2p).

The integral can be rescaled by √(pV) when V is positive. Its limiting Gaussian coefficient is a separate asymptotic problem. Extending the full-period argument to general real frequency differences requires a kernel accounting for the closed band; the lattice hypothesis supplies exact orthogonality here.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.moment_eq_pair`
- Truth anchor: `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.lattice_collision_variance_lower`
- Truth anchor: `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.lattice_period_collision`
- Truth anchor: `D5/S3/Fourier/Concentration/LatticeConvolutionVariance.score_variance_lower`
- Dependency: [D5/S3/Fourier/Concentration/CyclicCollisionCertificate](CyclicCollisionCertificate.md)
- Dependency: [D5/S3/Fourier/Concentration/DegreeTwoMomentWitness](DegreeTwoMomentWitness.md)
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
