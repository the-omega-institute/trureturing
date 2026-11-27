# Complex modular strip and logarithmic correction

## Abstract

A separately holomorphic null-diamond correction with uniform exponential strip decay.

The modular coordinate in the four-dimensional scalar covariance problem of Satishchandran and Sorce allows the radial logarithmic correction to extend to a complex strip. The lifted logarithm of each modular radius yields a holomorphic expression even when their product crosses the cut of the principal logarithm.

**Definition 1.1 (Closed strip half-width).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripB`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real constant b equals 3/8.

**Definition 1.2 (Complex modular radius).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularU`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex z, U(z) = exp(2πz)/(1 + exp(2πz)).

**Definition 1.3 (Modular Jacobian).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularUprime`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularUprime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex z, U′(z) = 2π exp(2πz)/(1 + exp(2πz))².

**Definition 1.4 (Lifted logarithm of the modular radius).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.liftedLog`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.liftedLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex z, L(z) = 2πz − log(1 + exp(2πz)), where log is the principal complex logarithm.

**Definition 1.5 (Open strip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.openStrip`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.openStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The open strip is the set of complex points z with |Im z| < 1/2.

**Definition 1.6 (Closed strip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.closedStrip`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.closedStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The closed strip is the set of complex points z with |Im z| ≤ b.

**Definition 1.7 (Complex modular correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M and x and complex z and w with x < 1, put t = M² U(z) U(w)(1−x)/2 and ℓ = log(M²(1−x)/2) + L(z) + L(w), using the real logarithm in the first term. The kernel G_M(z,w,x) equals 4 U′(z) U′(w) times the correction with supplied logarithm ℓ at argument t. Its value for x ≥ 1 is zero.

**Theorem 1.8 (Uniform lower bound for the modular denominator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.strip_denom_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.strip_denom_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every z in the closed strip, the norm of 1 + exp(2πz) is at least cos(πb)(1 + exp(2π Re z)). Rotating the denominator by exp(−iπ Im z) exhibits the real part (1 + exp(2π Re z)) cos(π Im z), and cosine is bounded below by cos(πb).

**Theorem 1.9 (The lifted logarithm exponentiates to the modular radius).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.exp_liftedLog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.exp_liftedLog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every z in the open strip, exp(L(z)) = U(z). The modular denominator belongs to the slit domain of the complex logarithm there.

**Theorem 1.10 (Agreement with the real radial correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M, r, s and x with M > 0 and x < 1, G_M(r,s,x) equals 4 U′(r) U′(s) times the real radial correction at M, Re U(r), Re U(s) and x. On the real axis each modular radius is positive and its lifted logarithm agrees with the ordinary real logarithm.

**Theorem 1.11 (Holomorphy in the first modular coordinate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real M and x and complex w, the function z ↦ G_M(z,w,x) is complex differentiable on the open strip. The modular radius, Jacobian and lifted logarithm are holomorphic there, and the two weighted power-series coefficients are entire.

**Theorem 1.12 (Holomorphy in the second modular coordinate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real M and x and complex z, the function w ↦ G_M(z,w,x) is complex differentiable on the open strip.

**Theorem 1.13 (Uniform exponential decay on the closed strip).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real M > 0 there exists a real C > 0 such that for all complex z and w in the closed strip and every real x with −1 ≤ x < 1, the norm of G_M(z,w,x) is at most C exp(−2π(|Re z| + |Re w|)) (1 + |Re z| + |Re w| + |log(1−x)|). The denominator bound controls the radii uniformly and supplies an exponential bound for each Jacobian. The real and imaginary parts of the principal logarithm bound each lifted logarithm by a constant times 1 + |Re z|. The series argument stays in a fixed bounded disk and the entire coefficient functions are bounded on its closure. The two Jacobian factors therefore give the required exponential decay while the angular logarithm remains explicit.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.closedStrip`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.exp_liftedLog`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.liftedLog`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularU`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.modularUprime`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.openStrip`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripB`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_left`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_diff_right`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.stripG_real`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D.strip_denom_lower`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D](NullDiamondBesselSeries4D.md)
