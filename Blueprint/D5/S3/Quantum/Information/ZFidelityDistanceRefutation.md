# The z-fidelity distance violates the triangle inequality at z = 2

## Abstract

Nuradha, Mishra, Leditzky and Wilde (arXiv:2404.16101, J. Phys. A 58, 165304) ask in Open Question 3 whether sqrt(2(1 - F_z(rho, sigma))) is a distance measure for z in (1/2, 1) or z > 1, where F_z(rho, sigma) = Tr[(sigma^{1/(4z)} rho^{1/(2z)} sigma^{1/(4z)})^z]. At z = 2 it violates the triangle inequality for two rank-one qubit projections and a diagonal qubit state.

**Definition 1.1 (The z-fidelity).**

$$\forall n : \mathbb{N}, \forall z : \mathbb{R}, \forall \rho, \sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{zFidelity}\left(z, \rho, \sigma\right) = \operatorname{re}\left(\operatorname{tr}\left((\sigma^{\frac{1}{4 \cdot z}} \cdot \rho^{\frac{1}{2 \cdot z}} \cdot \sigma^{\frac{1}{4 \cdot z}})^{z}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.zFidelity` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Eq. (eq:z-fid-def): F_z(rho, sigma) is the trace of the z-th power of sigma^{1/(4z)} rho^{1/(2z)} sigma^{1/(4z)}, with real powers of positive semidefinite matrices taken in the continuous functional calculus; the real part of the trace is recorded.

**Definition 1.2 (The distance of Open Question 3).**

$$\forall n : \mathbb{N}, \forall z : \mathbb{R}, \forall \rho, \sigma : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{zDistance}\left(z, \rho, \sigma\right) = \sqrt{2 \cdot (1 - \operatorname{zFidelity}\left(z, \rho, \sigma\right))}$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.zDistance` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

The candidate distance is the square root of 2(1 - F_z(rho, sigma)).

**Definition 1.3 (The asked distance property).**

$$(claim) \Leftrightarrow (\forall z : \mathbb{R}, (((\frac{1}{2} < z) \land (z < 1)) \lor (1 < z)) \Rightarrow (\forall n : \mathbb{N}, \forall \rho, \sigma, \tau : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), ((((\operatorname{PosSemidef}\left(\rho\right)) \land (\operatorname{tr}\left(\rho\right) = 1)) \land ((\operatorname{PosSemidef}\left(\sigma\right)) \land (\operatorname{tr}\left(\sigma\right) = 1))) \land ((\operatorname{PosSemidef}\left(\tau\right)) \land (\operatorname{tr}\left(\tau\right) = 1))) \Rightarrow (\operatorname{zDistance}\left(z, \rho, \tau\right) \le \operatorname{zDistance}\left(z, \rho, \sigma\right) + \operatorname{zDistance}\left(z, \sigma, \tau\right))))$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.claim` (`✓ std3`).

*Citation.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Open Question 3 asks whether the distance is a distance measure for z in (1/2, 1) or z > 1. The statement is its triangle inequality, part of being a distance measure, for every such z, every dimension n and all n x n density matrices rho, sigma, tau.

**Definition 1.4 (The first projection).**

$$stateP = \frac{1}{10} \cdot [9, 3; 3, 1]$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

P is the projection onto (3, 1)/sqrt 10.

**Definition 1.5 (The diagonal state).**

$$stateQ = \frac{1}{17} \cdot \operatorname{diag}\left(16, 1\right)$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Q is the diagonal density matrix diag(16, 1)/17.

**Definition 1.6 (The second projection).**

$$stateT = \frac{1}{10} \cdot [9, -3; -3, 1]$$

*Formalization.* `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

T is the projection onto (3, -1)/sqrt 10.

**Theorem 1.7 (The triangle inequality fails at z = 2).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nuradha-2025-z-fidelity-distance` (refuted) by `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nuradha-2025-z-fidelity-distance","declaration_gid":"D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Theshani Nuradha; Hemant K. Mishra; Felix Leditzky; Mark M. Wilde (2025). *Multivariate Fidelities*. DOI: [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645). URL: <https://arxiv.org/abs/2404.16101v3>.

*Commentary.*

Every positive power of a positive idempotent is itself, so P and T are unchanged by the powers in F_2. The square roots of Q are diag(4, 1)/sqrt 17 and diag(2, 1)/17^{1/4}, by uniqueness of positive square roots. Hence F_2(P, T) = 256/625 and F_2(P, Q) = F_2(Q, T) = 361/(100 sqrt 17). The triangle inequality d(P, T) <= d(P, Q) + d(Q, T) would force 361/(100 sqrt 17) <= 2131/2500, but 9025^2 - 17 * 2131^2 = 4250888 > 0.

## References

- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateP`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateQ`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.stateT`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.zDistance`
- Truth anchor: `D5/S3/Quantum/Information/ZFidelityDistanceRefutation.zFidelity`
