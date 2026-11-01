# The reverse Mittag-Leffler modulus characterization fails

## Abstract

A closed beta interval of strict deficits exists for every alpha between one and two.

**Definition 1.1 (The convergent two-parameter series).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Leftrightarrow \left(\forall alpha \in Real,\; 0 < alpha \Rightarrow \left(\forall beta \in Real,\; \forall z \in Complex,\; HasSum\left(((k: Nat) \mapsto \frac{z^{k}}{val\left(\operatorname{Real}.\operatorname{Gamma}\left(alpha \cdot val\left(k, Real\right) + beta\right), Complex\right)}), E\left(alpha, beta, z\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.IsSourceSeries` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 1, equation (1.1): “In this paper we study several inequalities of the two-parameter Mittag-Leffler function Eα,β, which is defined on the complex plane for α > 0 and β ∈ ℝ by the series representation” Eα,β(z) = ∑ from k = 0 to infinity of z^k/Γ(αk+β), z ∈ ℂ. The formula uses HasSum, so convergence is part of the relation. Alpha and beta are real, z is complex, and k is natural. The value val(k,Real) is the natural-to-real coercion, and val(Real.Gamma(alpha*val(k,Real)+beta),Complex) embeds the denominator in the complex plane. Division is totalized at Gamma poles.

**Definition 1.2 (The real reciprocal on the positive axis).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; \forall alpha \in Real,\; \forall beta \in Real,\; \forall x \in Real,\; reciprocal\left(E, alpha, beta, x\right) = \frac{1}{\operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(x, Complex\right)\right)\right)}$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.reciprocal` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 18, Conjecture 25 uses “1/Eα,β(x)”. Here E is a real-real-complex-complex family and alpha, beta and x are real. The real part reads the real-valued series on real arguments, after embedding x in Complex.

**Definition 1.3 (Conjecture 25 in full).**

$$claim = \left(\left(\exists E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right)\right) \land \left(\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \forall beta \in Real,\; 1 < alpha \Rightarrow \left(alpha < 2 \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\left(\forall z \in Complex,\; \operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(\operatorname{Complex}.\operatorname{re}\left(z\right), Complex\right)\right)\right) \le \left\lVert E\left(alpha, beta, z\right) \right\rVert\right) \Leftrightarrow \left(alpha - 1 \le beta \land beta \le alpha\right)\right) \land \left(\left(alpha - 1 \le beta \land beta \le alpha\right) \Leftrightarrow \left(\left(\forall x \in Real,\; 0 < x \Rightarrow 0 < reciprocal\left(E, alpha, beta, x\right)\right) \land \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left(reciprocal\left(E, alpha, beta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim` (`✓ std3`).

*Citation.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Page 18: “Conjecture 25. For every α ∈ (1, 2), one has The inequality (1.4) holds globally ⇐⇒ β ∈ [α − 1, α] ⇐⇒ 1/Eα,β(x) is CM on (0, ∞).” Inequality (1.4) is |Eα,β(z)| ≥ Eα,β(Re z), and globally means every complex z. The parameter beta is nonnegative, as in the paper's inequality problem. The leading existential supplies the entire convergent family. The second conjunct expresses both equivalences for every such family. CompletelyMonotoneOn supplies smoothness and all nonnegative signed derivatives; the separate positivity clause preserves the positive codomain. The displayed val operations are the real-to-complex coercions.

**Theorem 1.4 (Continuity in the second parameter).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; 0 < alpha \Rightarrow \left(\forall z \in Complex,\; Continuous\left((beta:Real \mapsto E\left(alpha, beta, z\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_continuous_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

For each positive alpha and complex z, every family satisfying the literal convergent source series is continuous as a function of beta on the whole real line. On every compact beta interval, eventual monotonicity of real Gamma on [2,infinity) gives a summable majorant from its left endpoint. The partial sums are continuous because reciprocal complex Gamma is entire, including at its zeros. Their local uniform limit equals E by HasSum uniqueness.

**Theorem 1.5 (The actual moving-left limit).**

$$\forall alpha \in Real,\; 1 < alpha \Rightarrow \left(\forall z \in Complex,\; \left(z\neq 0 \land 0 < margin\left(alpha, z\right)\right) \Rightarrow Tendsto\left((n:Nat \mapsto integral\left((y:Real \mapsto kernel\left(alpha, alpha - 1, z, leftLine\left(n\right) + y \cdot \operatorname{ComplexI}\right))\right)), atTop, nhds\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_left_integral_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

At beta=alpha-1 the real reciprocal-Gamma argument on the line indexed by n is alpha*n+alpha/2-1. Write n=m+1. The retained Gamma denominator then has fixed betaPrime=3*alpha/2-1, so the integral bound is a fixed factor times the m-th norm coefficient of the actual convergent Mittag-Leffler series at betaPrime. Summability forces it to zero. No Barnes identity or asymptotic is assumed.

**Theorem 1.6 (The literal Barnes identity).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; 1 < alpha \Rightarrow \left(\forall z \in Complex,\; \left(z\neq 0 \land 0 < margin\left(alpha, z\right)\right) \Rightarrow E\left(alpha, alpha - 1, z\right) = \frac{1}{2 \cdot \pi } \cdot integral\left((y:Real \mapsto kernel\left(alpha, alpha - 1, z, \frac{1}{2} + y \cdot \operatorname{ComplexI}\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_barnes_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

For every literal source realization, alpha greater than one and nonzero exterior z, the endpoint beta=alpha-1 value is one over 2*pi times the integral in dy on Re(s)=1/2. The proof supplies the actual shifted-Gamma holomorphic numerator, single-pole factorization, all boundary-line integrability, both horizontal limits and moving-left limit. Its residues are exactly z^n/Gamma(alpha*n+beta). The residue HasSum and the original source HasSum agree by uniqueness. The rightward shifts use this literal identity to obtain the endpoint inverse-square expansion.

**Definition 1.7 (The endpoint coefficient).**

$$\forall alpha \in Real,\; endpointCoefficient\left(alpha\right) = \frac{-(1)}{RealGamma\left(-(alpha) - 1\right)}$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.endpointCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The first nonzero inverse-power coefficient is minus the reciprocal of Gamma at minus alpha minus one.

**Theorem 1.8 (The positive endpoint coefficient).**

$$\forall alpha \in Real,\; \left(1 < alpha \land alpha < 2\right) \Rightarrow \left(endpointCoefficient\left(alpha\right) = \frac{alpha \cdot \left(alpha - 1\right) \cdot \left(alpha + 1\right)}{RealGamma\left(2 - alpha\right)} \land 0 < endpointCoefficient\left(alpha\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.endpointCoefficient_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Three Gamma recurrences identify the coefficient with alpha times alpha minus one times alpha plus one divided by Gamma at two minus alpha. It is strictly positive throughout the open alpha interval.

**Theorem 1.9 (The actual endpoint expansion).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; 1 < alpha \Rightarrow \left(\forall z \in Complex,\; \left(z\neq 0 \land 0 < margin\left(alpha, z\right)\right) \Rightarrow E\left(alpha, alpha - 1, z\right) = \frac{endpointCoefficient\left(alpha\right)}{z^{2}} + \frac{1}{2 \cdot \pi } \cdot integral\left((y:Real \mapsto kernel\left(alpha, alpha - 1, z, \frac{5}{2} + y \cdot \operatorname{ComplexI}\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The shifts from one half to three halves and then five halves cross the poles at one and two. The first coefficient vanishes because reciprocal Gamma at minus one is zero. The remainder is the actual integral on the five-halves line, with integration in dy.

**Theorem 1.10 (The endpoint scaled limit).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; 1 < alpha \Rightarrow \left(\forall w \in Complex,\; \left(w\neq 0 \land 0 < margin\left(alpha, w\right)\right) \Rightarrow Tendsto\left((r:Real \mapsto r^{2} \cdot E\left(alpha, alpha - 1, r \cdot w\right)), atTop, nhds\left(\frac{endpointCoefficient\left(alpha\right)}{w^{2}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

Positive radial scaling gives a fixed constant times r to the power minus five halves for the remainder. After multiplication by r squared the error tends to zero. The limit is the endpoint coefficient divided by w squared.

**Definition 1.11 (The prescribed ray tilt).**

$$\forall alpha \in Real,\; rayTilt\left(alpha\right) = tan\left(\frac{\pi  \cdot \left(2 - alpha\right)}{4}\right)$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.rayTilt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The angle is pi times two minus alpha divided by four.

**Definition 1.12 (The prescribed exterior direction).**

$$\forall alpha \in Real,\; rayDirection\left(alpha\right) = -(1) + rayTilt\left(alpha\right) \cdot \operatorname{ComplexI}$$

*Formalization.* `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.rayDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The direction is minus one plus i times the prescribed positive tilt.

**Theorem 1.13 (The ray geometry and angular margin).**

$$\forall alpha \in Real,\; \left(1 < alpha \land alpha < 2\right) \Rightarrow \left(0 < rayTilt\left(alpha\right) \land \left(rayDirection\left(alpha\right)\neq 0 \land \left(0 < margin\left(alpha, rayDirection\left(alpha\right)\right) \land \left(re\left(rayDirection\left(alpha\right)\right) = -(1) \land \left\lVert rayDirection\left(alpha\right) \right\rVert^{2} = 1 + rayTilt\left(alpha\right)^{2}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.ray_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The argument of minus the direction is minus the prescribed angle. The principal argument follows by positive scaling of the unit-circle direction, and the angular margin is strictly positive.

**Theorem 1.14 (One finite endpoint deficit).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \left(1 < alpha \land alpha < 2\right) \Rightarrow \left(\exists r \in Real,\; 0 < r \land \left\lVert E\left(alpha, alpha - 1, r \cdot rayDirection\left(alpha\right)\right) \right\rVert < re\left(E\left(alpha, alpha - 1, val\left(re\left(r \cdot rayDirection\left(alpha\right)\right), Complex\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The scaled negative-axis real part tends to the positive endpoint coefficient. The scaled ray norm tends to that coefficient divided by one plus the squared tilt. Their strict limit gap gives one finite positive radius.

**Theorem 1.15 (The same point on a closed beta interval).**

$$\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \left(1 < alpha \land alpha < 2\right) \Rightarrow \left(\exists z \in Complex,\; \exists epsilon \in Real,\; 0 < epsilon \land \left(epsilon < 1 \land \left(0 < im\left(z\right) \land \left(\left(\exists r \in Real,\; 0 < r \land z = r \cdot rayDirection\left(alpha\right)\right) \land \left(\forall beta \in Real,\; \left(alpha - 1 \le beta \land beta \le alpha - 1 + epsilon\right) \Rightarrow \left\lVert E\left(alpha, beta, z\right) \right\rVert < re\left(E\left(alpha, beta, val\left(re\left(z\right), Complex\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_closed_beta_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

For every alpha between one and two, choose the finite point on the prescribed ray first. Continuity in beta gives an open neighborhood of strict deficits. A positive epsilon smaller than one places the whole closed interval from alpha minus one to alpha minus one plus epsilon inside that neighborhood.

**Theorem 1.16 (The characterization is false).**

$$\neg (\left(\exists E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right)\right) \land \left(\forall E \in Real \to \left(Real \to \left(Complex \to Complex\right)\right),\; IsSourceSeries\left(E\right) \Rightarrow \left(\forall alpha \in Real,\; \forall beta \in Real,\; 1 < alpha \Rightarrow \left(alpha < 2 \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\left(\forall z \in Complex,\; \operatorname{Complex}.\operatorname{re}\left(E\left(alpha, beta, val\left(\operatorname{Complex}.\operatorname{re}\left(z\right), Complex\right)\right)\right) \le \left\lVert E\left(alpha, beta, z\right) \right\rVert\right) \Leftrightarrow \left(alpha - 1 \le beta \land beta \le alpha\right)\right) \land \left(\left(alpha - 1 \le beta \land beta \le alpha\right) \Leftrightarrow \left(\left(\forall x \in Real,\; 0 < x \Rightarrow 0 < reciprocal\left(E, alpha, beta, x\right)\right) \land \operatorname{D5}.\operatorname{S3}.\operatorname{Analytic}.\operatorname{ExpRatioCM}.\operatorname{Defs}.\operatorname{CompletelyMonotoneOn}\left(reciprocal\left(E, alpha, beta\right)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ggps2025` (refuted) by `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ggps2025","declaration_gid":"D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Roberto Garrappa, Stefan Gerhold, Marina Popolizio, Thomas Simon (2025). *On some inequalities for the two-parameter Mittag-Leffler function in the complex plane*. URL: <https://arxiv.org/abs/2410.11852v4>.

*Commentary.*

The literal source family exists for every positive alpha, every real beta and every complex argument. Apply the closed-beta family at alpha three halves and beta one half. The first original global equivalence would force the reverse modulus inequality at its chosen point, contradicting the strict deficit. The source definition and both original global equivalences retain their full quantifiers.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.IsSourceSeries`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.endpointCoefficient`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.endpointCoefficient_formula`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.rayDirection`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.rayTilt`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.ray_parameters`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.reciprocal`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.result`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_barnes_identity`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_closed_beta_family`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_continuous_beta`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_expansion`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_failure`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_endpoint_scaled_limit`
- Truth anchor: `D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation.source_left_integral_tendsto_zero`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../../../S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
- Dependency: [D5/S3/Analytic/Asymptotics/MellinBarnesSeries](MellinBarnesSeries.md)
- Dependency: [D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel](MittagLefflerBarnesKernel.md)
- Dependency: [D5/S3/Analytic/ExpRatioCM/Defs](../ExpRatioCM/Defs.md)
- Dependency: [D5/S3/Analytic/KilbasSaigo/Series](../KilbasSaigo/Series.md)
