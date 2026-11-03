# Altizio's geometric-sum disk classification

## Abstract

The geometric-sum bound on the closed disk centered at two holds exactly in degrees five, six and seven.

**Definition 1.1 (Remark 4).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 0 < n \Rightarrow ((\forall z \in \mathbb{C},\; z \in \operatorname{Metric}.\operatorname{closedBall}\left((2: \mathbb{C}), 1\right) \Rightarrow (n: \mathbb{R}) \cdot \left\lVert z \right\rVert \le \left\lVert \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} z^{k} \right\rVert) \Leftrightarrow (n = 5 \lor \left(n = 6 \lor n = 7\right))))$$

*Formalization.* `D5/S3/Zeros/AltizioGeometricSumDisk.claim` (`✓ std3`).

*Citation.* David Altizio (2025). *Zeros of Stern polynomials in the complex plane*. DOI: [10.48550/arXiv.2511.03847](https://doi.org/10.48550/arXiv.2511.03847). URL: <https://arxiv.org/abs/2511.03847v1>.

*Commentary.*

Altizio, p. 20, Remark 4: “One might suspect that |(z)_n| ≥ n|z| more generally whenever z ∈ B. However, numerical evidence suggests that the value min_{z∈B} |(z)_n/z| approaches 2π as n → ∞. It seems that this inequality is true only for n = 5, 6, and 7, but we do not have a proof.” On p. 4, Section 2: “For all positive integers n, we introduce the (non-standard) notation (λ)_n := 1 + λ + ⋯ + λ^{n−1} = (λ^n − 1)/(λ − 1) ∈ ℤ[λ].” The finite sum has indices k = 0, …, n−1; it includes its continuous value n at z = 1. Section 3 writes “B := B_1[2] = {|w − 2| ≤ 1}”. Here n is a positive natural number, z is complex, and the complex absolute value is the norm. The statement classifies the degrees; it makes no assertion about the proposed 2π limit.

**Theorem 1.2 (The exact set of degrees).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow ((\forall z \in \mathbb{C},\; z \in \operatorname{Metric}.\operatorname{closedBall}\left((2: \mathbb{C}), 1\right) \Rightarrow (n: \mathbb{R}) \cdot \left\lVert z \right\rVert \le \left\lVert \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} z^{k} \right\rVert) \Leftrightarrow (n = 5 \lor \left(n = 6 \lor n = 7\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/AltizioGeometricSumDisk.result` (`✓ std3`). ∎

*Resolves.* `Problems/altizio-2025-geometric-sum-disk` (proved) by `D5/S3/Zeros/AltizioGeometricSumDisk.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"altizio-2025-geometric-sum-disk","declaration_gid":"D5/S3/Zeros/AltizioGeometricSumDisk.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David Altizio (2025). *Zeros of Stern polynomials in the complex plane*. DOI: [10.48550/arXiv.2511.03847](https://doi.org/10.48550/arXiv.2511.03847). URL: <https://arxiv.org/abs/2511.03847v1>.

*Commentary.*

On the boundary circle, put u = ‖z‖². The power sum zⁿ + conjugate(z)ⁿ obeys a second-order recurrence with sum (u+3)/2 and product u. Subtracting n²u(u−1)/2 gives the squared-norm defect. At degrees 5, 6 and 7 its expansion in u−1 has nonnegative coefficients. The geometric sum is nonzero on the disk, so the maximum modulus principle applied to z divided by that sum extends the boundary estimate to the disk.

For every other positive degree, the quadratic coefficient is −n²(n−5)(n−7)/48 ≤ −1/2. Dividing off the first three powers of the polynomial variable leaves a remainder whose coefficient absolute sum bounds its value on [0,1]. Choosing a positive parameter from that sum makes the defect negative and produces a point on the boundary that violates the inequality. This proves both directions for every positive n. The separate bound in Remark 3 and the 2π limit remain unanswered.

## References

- Truth anchor: `D5/S3/Zeros/AltizioGeometricSumDisk.claim`
- Truth anchor: `D5/S3/Zeros/AltizioGeometricSumDisk.result`
- Dependency: [D5/S3/Analytic/Interpolation/UniformCoefficientBudget](../Analytic/Interpolation/UniformCoefficientBudget.md)
- Dependency: [D5/S3/Weil/InterpolationJets/QuantitativeEvenSeed](../Weil/InterpolationJets/QuantitativeEvenSeed.md)
