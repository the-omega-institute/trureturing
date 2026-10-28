# Weighted fractional-kernel injectivity

## Abstract

Weighted injectivity of the actual fractional reciprocal integral transform.

The literal coefficient is fract(1/(u*y)); all powers of a positive real base use the principal complex power. The parameter gamma is arbitrary and no hypothesis asserts that zeta vanishes.

**Definition 1.1 (Actual integrand).**

$$w(u)u^{-\frac{1}{2}+igamma}\operatorname{fract}(\frac{1}{uy})$$

*Formalization.* `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.actualIntegrand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function of u is w(u)*u^(-1/2+i*gamma)*fract(1/(u*y)). The variables gamma and y are real; the injectivity theorem quantifies y>0.

**Definition 1.2 (Actual integral transform).**

$$H_{gamma}w(y)=\int_{0}^{\infty}w(u)u^{-\frac{1}{2}+igamma}\operatorname{fract}(\frac{1}{uy})\,du$$

*Formalization.* `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.actualTransform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the Bochner integral with respect to volume restricted to the positive half-line. The proof pays its absolute integrability for every positive y from the stated weighted domain; it does not use a total integral's undefined-value convention to bypass convergence.

**Definition 1.3 (Absolute weighted domain).**

$$\int_{0}^{\infty}\Vert w(u)\Vert u^{r-1}\,du<\infty$$

*Formalization.* `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.WeightedIntegrable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WeightedIntegrable means IntegrableOn of the nonnegative real function norm(w(u))*u^(r-1) on (0,infinity). The continuity assumption in the theorem supplies measurability. No second weight is required.

**Theorem 1.4 (Injectivity on the weighted continuous domain).**

$$\forall w:\mathbb{R}\to\mathbb{C}, r,gamma\in \mathbb{R}, -\frac{1}{2}<r<\frac{1}{2}\land\operatorname{ContinuousOn}(w,(0,\infty))\land\int_{0}^{\infty}\Vert w(u)\Vert u^{r-1}\,du<\infty\land(\forall y>0,H_{gamma}w(y)=0)\Rightarrow\forall u>0,w(u)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.weighted_fractional_transform_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put kappa=1/2-r, f(v)=w(exp(v))*exp((r+i*gamma)*v), and k(z)=exp(-kappa*z)*fract(exp(z)). Then 0<kappa<1, f and k belong to L1, and norm(k(z))<=1 everywhere. The actual exp substitution, including the Jacobian exp(v), proves exp(-kappa*z)*H_gamma(w)(exp(-z))=(f*k)(z). The proof first establishes all actual integrals using f.mul_bdd. The already existing unit-interval Mellin identity plus the reciprocal tail gives mellin(fract(1/x),s)=-zeta(s)/s for 0<Re(s)<1. The tail's pointwise reduction calls the shared NymanFractionalMellin.fractionalMellin_tail_integrand_eq_cpow helper, extracted from the existing finite-tail proof; the extraction is source reuse and is not a new mathematical result. Applying the public mellin_eq_fourier theorem fixes Mathlib's 2*pi convention and gives Fourier(k)(xi)=-zeta(kappa+2*pi*i*xi)/(kappa+2*pi*i*xi). The public Fourier convolution theorem pays Fubini. The upstream discrete zeta zero set is countable, so the multiplier is nonzero on a dense subset of the frequency line. Continuity forces Fourier(f)=0 everywhere. The zero Fourier transform is integrable, so pointwise Fourier inversion at the continuous f gives f=0, and exp/log recovers w=0 on the positive half-line.

Application to the original power class: let w be continuous on (0,infinity), let a<1/2<b, let gamma be any real number, and suppose one constant C bounds norm(w(u)) by C*u^(-a) for 0<u<=1 and by C*u^(-b) for u>1. Choose max(a,-1/2)<r<1/2. The near-zero weighted majorant is C*u^(r-a-1), and the tail majorant is C*u^(r-b-1), both integrable. The weighted theorem therefore applies to this original class. Its exact Lean application is supplied as a temporary example for scoped checking, without a retained separate theorem, Describe entry or Reg wrapper. The private power-comparison helper stays with that transient check and has no retained main-G consumer. The input class and motivation are the paper-level fixed-profile obstruction recorded in Library/Weil/baezduarte2000natural.md. This injectivity bridge alone does not prove that obstruction's Order Lemma or interval-probe premises, excludes no moving-profile or selected-subsequence construction, and establishes no RH or signed Weil-energy conclusion.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.WeightedIntegrable`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.actualIntegrand`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.actualTransform`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity.weighted_fractional_transform_injective`
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin](NymanFractionalMellin.md)
