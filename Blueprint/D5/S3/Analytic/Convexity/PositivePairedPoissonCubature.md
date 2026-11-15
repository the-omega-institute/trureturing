# Positive paired Poisson finite cubature

## Abstract

A constructed positive cosine density gives exact paired Poisson cubature for every finite initial segment of signed real data, using at most L+1 phases.

All coefficients, weights, angles and parameters are real. Natural indices begin at zero. SumFin(J,u) means the sum over j:Fin J; TsumNat(u) means the infinite sum over natural indices. NatCast is the natural-to-real coercion, IntervalIntegrable uses real Lebesgue measure, and Icc includes both endpoints. Function application in the formulas is ordinary point evaluation.

**Definition 1.1 (pairedMultiplier).**

$$\forall D : \mathbb{R}, (\forall sigma : \mathbb{R}, (\forall n : \mathbb{N}, (\operatorname{pairedMultiplier}\left(D, sigma, n\right) = (\frac{((\frac{1}{sigma})^{n}) + (((D) \cdot (sigma))^{n})}{2}))))$$

*Formalization.* `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.pairedMultiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two geometric radii are 1/sigma and D*sigma. This definition makes the coefficient at zero equal to one. Positivity and summability require the hypotheses of the inverse theorem below.

**Definition 1.2 (inverseCoeff).**

$$\forall D : \mathbb{R}, (\forall sigma : \mathbb{R}, (\forall f : (\mathbb{N} \to \mathbb{R}), (\forall n : \mathbb{N}, (\operatorname{inverseCoeff}\left(D, sigma, f, n\right) = (\frac{f\left(n\right)}{\operatorname{pairedMultiplier}\left(D, sigma, n\right)})))))$$

*Formalization.* `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.inverseCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse divides the supplied real coefficient by the paired multiplier. Nonvanishing of the multiplier is proved from nonnegative D and sigma>1; it is not an additional premise.

**Definition 1.3 (weightedMass).**

$$\forall sigma : \mathbb{R}, (\forall f : (\mathbb{N} \to \mathbb{R}), (\operatorname{weightedMass}\left(sigma, f\right) = (\operatorname{TsumNat}\left(n \mapsto ((\left|f\left((n) + (1)\right)\right|) \cdot ((sigma)^{(n) + (1)}))\right))))$$

*Formalization.* `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weightedMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only positive-index coefficients enter this absolute weighted mass. Summability and the displayed smallness bound control the oscillation of the inverse density.

**Definition 1.4 (cosineDensity).**

$$\forall c : (\mathbb{N} \to \mathbb{R}), (\forall theta : \mathbb{R}, (\operatorname{cosineDensity}\left(c, theta\right) = ((c\left(0\right)) + ((2) \cdot (\operatorname{TsumNat}\left(n \mapsto ((c\left((n) + (1)\right)) \cdot (\operatorname{cos}\left((\operatorname{NatCast}\left((n) + (1)\right)) \cdot (theta)\right)))\right))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.cosineDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each positive cosine coefficient represents the two frequencies plus and minus n. The constant coefficient occurs once, and each positive-index coefficient occurs with factor two.

**Definition 1.5 (haarMean).**

$$\forall g : (\mathbb{R} \to \mathbb{R}), (\operatorname{haarMean}\left(g\right) = ((\frac{1}{(2) \cdot (\pi)}) \cdot (\operatorname{IntervalIntegral}\left(g, 0, (2) \cdot (\pi)\right))))$$

*Formalization.* `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.haarMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized angular integral is (1/(2*pi)) times the interval integral from zero to 2*pi. It is defined for every real function with Mathlib's total integral convention.

**Theorem 1.6 (weighted_positive_paired_poisson_inverse).**

$$\forall D : \mathbb{R}, (\forall sigma : \mathbb{R}, (\forall M : \mathbb{R}, (\forall f : (\mathbb{N} \to \mathbb{R}), ((1 < sigma) \Rightarrow ((0 \le D) \Rightarrow (((D) \cdot ((sigma)^{2}) < 1) \Rightarrow ((0 < M) \Rightarrow ((f\left(0\right) = (M)) \Rightarrow ((\operatorname{Summable}\left(n \mapsto ((\left|f\left((n) + (1)\right)\right|) \cdot ((sigma)^{(n) + (1)}))\right)) \Rightarrow (((2) \cdot (\operatorname{weightedMass}\left(sigma, f\right)) \le \frac{M}{16}) \Rightarrow ((\operatorname{Summable}\left(n \mapsto (\left|\operatorname{pairedMultiplier}\left(D, sigma, n\right)\right|)\right)) \land ((\operatorname{pairedMultiplier}\left(D, sigma, 0\right) = (1)) \land ((\forall n : \mathbb{N}, ((0 < \operatorname{pairedMultiplier}\left(D, sigma, n\right)) \land (\operatorname{pairedMultiplier}\left(D, sigma, n\right) \le (\frac{1}{sigma})^{n}))) \land ((\operatorname{Summable}\left(n \mapsto (\left|\operatorname{inverseCoeff}\left(D, sigma, f, n\right)\right|)\right)) \land ((\operatorname{inverseCoeff}\left(D, sigma, f, 0\right) = (M)) \land (((2) \cdot (\operatorname{TsumNat}\left(n \mapsto (\left|\operatorname{inverseCoeff}\left(D, sigma, f, (n) + (1)\right)\right|)\right)) \le (4) \cdot (\operatorname{weightedMass}\left(sigma, f\right))) \land (((4) \cdot (\operatorname{weightedMass}\left(sigma, f\right)) \le \frac{M}{8}) \land ((\operatorname{Continuous}\left(\operatorname{cosineDensity}\left(\operatorname{inverseCoeff}\left(D, sigma, f\right)\right)\right)) \land ((\forall theta : \mathbb{R}, (\operatorname{cosineDensity}\left(\operatorname{inverseCoeff}\left(D, sigma, f\right), -theta\right) = (\operatorname{cosineDensity}\left(\operatorname{inverseCoeff}\left(D, sigma, f\right), theta\right)))) \land ((\operatorname{Periodic}\left(\operatorname{cosineDensity}\left(\operatorname{inverseCoeff}\left(D, sigma, f\right)\right), (2) \cdot (\pi)\right)) \land ((\forall theta : \mathbb{R}, (\frac{M}{2} < \operatorname{cosineDensity}\left(\operatorname{inverseCoeff}\left(D, sigma, f\right), theta\right))) \land ((\forall n : \mathbb{N}, ((\operatorname{pairedMultiplier}\left(D, sigma, n\right)) \cdot (\operatorname{inverseCoeff}\left(D, sigma, f, n\right)) = (f\left(n\right)))) \land (\forall theta : \mathbb{R}, (\operatorname{cosineDensity}\left(n \mapsto ((\operatorname{pairedMultiplier}\left(D, sigma, n\right)) \cdot (\operatorname{inverseCoeff}\left(D, sigma, f, n\right))), theta\right) = (\operatorname{cosineDensity}\left(f, theta\right))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weighted_positive_paired_poisson_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For sigma>1, D>=0 and D*sigma^2<1 the multiplier is positive and bounded above by (1/sigma)^n. Its reciprocal is bounded by 2*sigma^n. Weighted absolute summability therefore gives absolute summability of the inverse coefficients. The smallness hypothesis yields 2*sum(abs(c(n+1)))<=4*weightedMass<=M/8. The synthesis is continuous, even and 2*pi-periodic, and is strictly greater than M/2 at every real angle. All thirteen conjunction clauses are retained, including both the pointwise coefficient identity and the synthesis identity.

**Theorem 1.7 (cosineDensity_haar_moments).**

$$\forall c : (\mathbb{N} \to \mathbb{R}), ((\operatorname{Summable}\left(n \mapsto (\left|c\left(n\right)\right|)\right)) \Rightarrow ((\operatorname{IntervalIntegrable}\left(\operatorname{cosineDensity}\left(c\right), \operatorname{volume}\left(\right), 0, (2) \cdot (\pi)\right)) \land ((\operatorname{haarMean}\left(\operatorname{cosineDensity}\left(c\right)\right) = (c\left(0\right))) \land (\forall k : \mathbb{N}, ((0 < k) \Rightarrow ((\operatorname{IntervalIntegrable}\left(theta \mapsto ((\operatorname{cosineDensity}\left(c, theta\right)) \cdot (\operatorname{cos}\left((\operatorname{NatCast}\left(k\right)) \cdot (theta)\right))), \operatorname{volume}\left(\right), 0, (2) \cdot (\pi)\right)) \land (\operatorname{haarMean}\left(theta \mapsto ((\operatorname{cosineDensity}\left(c, theta\right)) \cdot (\operatorname{cos}\left((\operatorname{NatCast}\left(k\right)) \cdot (theta)\right)))\right) = (c\left(k\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.cosineDensity_haar_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute summability of arbitrary real coefficients, with no positivity premise, gives interval integrability, the exact mean c(0), and every positive cosine moment c(k). The proof uses integer cosine orthogonality and a uniform summable majorant to exchange the actual interval integral and series.

**Theorem 1.8 (weighted_positive_paired_poisson_finite_cubature).**

$$\forall D : \mathbb{R}, (\forall sigma : \mathbb{R}, (\forall M : \mathbb{R}, (\forall f : (\mathbb{N} \to \mathbb{R}), ((1 < sigma) \Rightarrow ((0 \le D) \Rightarrow (((D) \cdot ((sigma)^{2}) < 1) \Rightarrow ((0 < M) \Rightarrow ((f\left(0\right) = (M)) \Rightarrow ((\operatorname{Summable}\left(n \mapsto ((\left|f\left((n) + (1)\right)\right|) \cdot ((sigma)^{(n) + (1)}))\right)) \Rightarrow (((2) \cdot (\operatorname{weightedMass}\left(sigma, f\right)) \le \frac{M}{16}) \Rightarrow (\forall L : \mathbb{N}, (\exists J : \mathbb{N}, ((1 \le J) \land ((J \le (L) + (1)) \land (\exists t : (\operatorname{Fin}\left(J\right) \to \mathbb{R}), (\exists theta : (\operatorname{Fin}\left(J\right) \to \mathbb{R}), ((\forall j : \operatorname{Fin}\left(J\right), (0 \le t\left(j\right))) \land ((\operatorname{SumFin}\left(J, t\right) = (\frac{M}{2})) \land ((\forall j : \operatorname{Fin}\left(J\right), (\operatorname{Mem}\left(theta\left(j\right), \operatorname{Icc}\left(0, (2) \cdot (\pi)\right)\right))) \land (\forall k : \mathbb{N}, ((1 \le k) \Rightarrow ((k \le L) \Rightarrow (\operatorname{SumFin}\left(J, j \mapsto (((t\left(j\right)) \cdot (\operatorname{pairedMultiplier}\left(D, sigma, k\right))) \cdot (\operatorname{cos}\left((\operatorname{NatCast}\left(k\right)) \cdot (theta\left(j\right))\right)))\right) = (\frac{f\left(k\right)}{2}))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weighted_positive_paired_poisson_finite_cubature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

For every natural L, choose J first, then one pair of maps t and theta satisfying all moments 1<=k<=L simultaneously. There are no sign conditions on f(k) for k>0. The lower cardinality bound is one and the upper bound is L+1, including L=0, which forces J=1. Output weights are nonnegative and sum exactly to M/2; phases lie in the closed interval [0,2*pi]. The right side of each paired cosine moment is the signed value f(k)/2.

For the finite-cubature foundation, the imported MeasurableFiniteMoments.integral_mem_convexHull places an integrable finite-dimensional probability barycenter in the actual convex hull. Its existing finite_moments_probability and finite_moments roots provide finite existence but assert no numerical cardinality bound. The classical provenance is Bayer and Teichmann, The proof of Tchakaloff's theorem, Corollary 2 and Remark 2; the existing Library note is the citation authority. The present root combines that foundation with the explicit geometric multiplier inverse and its actual Haar moments; no novelty claim is made.

Inside the proof put c(n)=inverseCoeff D sigma f n and rho=cosineDensity c. The inverse and scalar Haar theorem give rho>M/2 and haarMean(rho)=M. Normalize the actual measure with density ((1/(2*pi))/M)*rho relative to Lebesgue measure restricted to (0,2*pi]. Nonnegativity, continuity and the exact mean prove that its mass is one and prove the change-of-density identity.

Clamp each real input x to phase(x)=max(0,min(2*pi,x)); on (0,2*pi] this equals x. The map g(x)(i)=cos((i.val+1)*phase(x)) has values in Fin L to R and is bounded by one, so it is integrable, also for L=0. Apply the imported actual-hull theorem and Mathlib's eq_pos_convex_span_of_mem_convexHull. Affine independence bounds the number of points by finrank(vectorSpan(range z))+1<=L+1, and probability weight sum one forces at least one point. Lift the selected points to actual preimages and reindex by Fin J. Set theta(j)=phase(a(j)) and t(j)=(M/2)*p(j). The same selected maps then match each prescribed moment by the proved coefficient identity.

This is a finite-segment existence theorem over arbitrary signed real coefficient sequences satisfying the stated weighted bounds. It supplies no common nodes for all L, no full-spectrum equality for the finite measure, and no uniform choice across parameters. The strict positivity constructed internally is stronger than the nonnegativity requested in the output.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.cosineDensity`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.cosineDensity_haar_moments`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.haarMean`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.inverseCoeff`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.pairedMultiplier`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weightedMass`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weighted_positive_paired_poisson_finite_cubature`
- Truth anchor: `D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.weighted_positive_paired_poisson_inverse`
- Dependency: [D5/S3/Analytic/Convexity/MeasurableFiniteMoments](MeasurableFiniteMoments.md)
