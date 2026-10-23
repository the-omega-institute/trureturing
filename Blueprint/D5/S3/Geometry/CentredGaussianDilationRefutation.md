# Centred Gaussian dilation refutation

## Abstract

A centred 16-dimensional convex pyramid has non-log-concave Gaussian dilations.

Faifman and Polterovich, The Faber–Krahn position of convex bodies and Gaussian measure inequalities, arXiv:2607.21539v2, §5.2, p. 38, verbatim: “The B-theorem requires central symmetry. To prove Theorem 1.1, we circumvent this by proving a weaker concavity property of the Gaussian measure in a special case. However, we do not know a convex counterexample to the B-conjecture with its linear barycenter at the origin. Question 5.3. Let K ⊂ R^n be a convex body whose Lebesgue barycenter is at the origin. Is t ↦ γ_n(e^t K) log-concave? More generally, is t ↦ γ_n(e^{tS} K) log-concave for every symmetric matrix S?”

**Definition 1.1 (Standard Gaussian measure).**

$$\operatorname{gaussianMeasure}\left(n\right) = \operatorname{pi}\left((i \mapsto \operatorname{gaussianReal}\left(0, 1\right))\right)$$

*Formalization.* `D5/S3/Geometry/CentredGaussianDilationRefutation.gaussianMeasure` (`✓ std3`).

*Citation.* D. Faifman; I. Polterovich (2026). *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*. DOI: [10.48550/arXiv.2607.21539](https://doi.org/10.48550/arXiv.2607.21539). URL: <https://arxiv.org/abs/2607.21539v2>.

*Commentary.*

For dimension n, gaussianMeasure n is the finite product of n copies of gaussianReal 0 1 on Fin n → R. The coordinates are independent standard real Gaussian variables. This is a probability measure, so every set has finite mass.

**Definition 1.2 (A convex body).**

$$\operatorname{IsConvexBody}\left(K\right) \Leftrightarrow ((\operatorname{Convex}\left(\mathbb{R}, K\right)) \land ((\operatorname{IsCompact}\left(K\right)) \land (\operatorname{Nonempty}\left(\operatorname{interior}\left(K\right)\right))))$$

*Formalization.* `D5/S3/Geometry/CentredGaussianDilationRefutation.IsConvexBody` (`✓ std3`).

*Citation.* D. Faifman; I. Polterovich (2026). *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*. DOI: [10.48550/arXiv.2607.21539](https://doi.org/10.48550/arXiv.2607.21539). URL: <https://arxiv.org/abs/2607.21539v2>.

*Commentary.*

A convex body is a real convex compact set with nonempty interior. The coordinates Fin n → R carry their usual finite-dimensional topology.

**Definition 1.3 (Zero Lebesgue barycenter).**

$$\operatorname{BarycenterZero}\left(K\right) \Leftrightarrow (\forall i: \operatorname{Fin}\left(n\right), \int_{z \in K} \operatorname{z}\left(i\right) dz = 0)$$

*Formalization.* `D5/S3/Geometry/CentredGaussianDilationRefutation.BarycenterZero` (`✓ std3`).

*Citation.* D. Faifman; I. Polterovich (2026). *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*. DOI: [10.48550/arXiv.2607.21539](https://doi.org/10.48550/arXiv.2607.21539). URL: <https://arxiv.org/abs/2607.21539v2>.

*Commentary.*

Each coordinate's Lebesgue integral over K is zero. For a convex body the coordinate functions are integrable and the volume is positive and finite. Dividing the coordinate integrals by that volume therefore gives the usual normalized barycenter at the origin. The centering measure here is Lebesgue measure, whereas the dilated masses use Gaussian measure.

**Definition 1.4 (Scalar Gaussian dilation concavity).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall K: \operatorname{Set}\left((\operatorname{Fin}\left(n\right) \to \mathbb{R})\right), (\operatorname{IsConvexBody}\left(K\right)) \Rightarrow ((\operatorname{BarycenterZero}\left(K\right)) \Rightarrow (\operatorname{ConcaveOn}\left(\mathbb{R}, univ, (t \mapsto \operatorname{log}\left(\operatorname{toReal}\left(\operatorname{gaussianMeasure}\left(n, \operatorname{exp}\left(t\right) \cdot K\right)\right)\right))\right))))$$

*Formalization.* `D5/S3/Geometry/CentredGaussianDilationRefutation.claim` (`✓ std3`).

*Citation.* D. Faifman; I. Polterovich (2026). *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*. DOI: [10.48550/arXiv.2607.21539](https://doi.org/10.48550/arXiv.2607.21539). URL: <https://arxiv.org/abs/2607.21539v2>.

*Commentary.*

The formal encoding of the first clause of Question 5.3 requires the logarithm of the Gaussian mass of exp(t) times K to be concave on the entire real line, for every dimension and every convex body with zero Lebesgue barycenter. The logarithm is applied to the real value of the extended nonnegative Gaussian mass. The matrix clause includes this scalar case by taking the symmetric identity matrix.

**Theorem 1.5 (A centred pyramid refutes concavity).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/CentredGaussianDilationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/faifman-polterovich-2026-centred-gaussian-dilation` (refuted) by `D5/S3/Geometry/CentredGaussianDilationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"faifman-polterovich-2026-centred-gaussian-dilation","declaration_gid":"D5/S3/Geometry/CentredGaussianDilationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Faifman; I. Polterovich (2026). *The Faber–Krahn position of convex bodies and Gaussian measure inequalities*. DOI: [10.48550/arXiv.2607.21539](https://doi.org/10.48550/arXiv.2607.21539). URL: <https://arxiv.org/abs/2607.21539v2>.

*Commentary.*

Let K consist of z in R¹⁶ with −1≤z₀≤16 and |zᵢ|≤10(16−z₀) for i≠0. The set is an intersection of linear half-spaces, lies in a bounded box, and contains an open neighbourhood of zero. It is consequently a compact convex body with nonempty interior. Its transverse slices are symmetric 15-dimensional boxes. Their coordinate integrals vanish by negation symmetry. Product integration gives the remaining first moment as the integral from −1 to 16 of x[20(16−x)]¹⁵. The antiderivative 20¹⁵[−(16−x)¹⁶+(16−x)¹⁷/17] has equal endpoint values, so this moment also vanishes. The boxes [−1/4,7/2]×[−5,5]¹⁵ and [−1,7/2]×[−5,5]¹⁵ lie in K/4 and K, respectively, whereas K/2 lies in the half-space z₀≥−1/2. Writing c=(2π)⁻¹ᐟ², the bounds 997/2500<c<2/5 and exp(−u²/2)≥1−u²/2+u⁴/8−u⁶/48−5u⁸/1536 for 0≤u≤1 give lower interval masses. Gaussian symmetry gives mass 1/2 on each side of zero. The exponential moment bounds the positive tails by exp(−a²/2), which is less than 1/350 at a=7/2 and less than 1/16000 at a=5. Independence and these rational estimates give γ₁₆(K/4)>594/1000, γ₁₆(K)>836/1000 and γ₁₆(K/2)<7/10. The quarter-scale pyramid lies inside the half-scale pyramid, ensuring positive middle mass. Concavity at −log 4 and zero would require γ₁₆(K/2)²≥γ₁₆(K/4)γ₁₆(K), but (7/10)²<(594/1000)(836/1000). This answers both clauses of Question 5.3 negatively, with the identity matrix in the second clause. The example has zero Lebesgue barycenter; zero Gaussian centroid is a different condition and is unsettled here. The smallest dimension permitting a counterexample is also unsettled. The author-text locator and quotation are supplied with the statement; independent verification of that text and an exhaustive literature or priority claim are ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S3/Geometry/CentredGaussianDilationRefutation.BarycenterZero`
- Truth anchor: `D5/S3/Geometry/CentredGaussianDilationRefutation.IsConvexBody`
- Truth anchor: `D5/S3/Geometry/CentredGaussianDilationRefutation.claim`
- Truth anchor: `D5/S3/Geometry/CentredGaussianDilationRefutation.gaussianMeasure`
- Truth anchor: `D5/S3/Geometry/CentredGaussianDilationRefutation.result`
