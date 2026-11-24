# The high-threshold minimum for two cosine moments

## Abstract

A three-level probability law minimizes squared mass for high joint cosine thresholds.

For a finite index type I, write c for its real readout and use 2c² − 1 as the second readout. The value one occurs at a unique index. With levels ℓ and u, write g(x) = x − (2x² − 1), p = −g(ℓ)/(g(u) − g(ℓ)), b = pu + (1−p)ℓ and r = (1−a)/(1−b). The law gives mass 1−r to that index, rp to the level u, and r(1−p) to the level ℓ. Each level’s mass is divided equally among its indices.

The notation H(c,z,u,ℓ) means c(i)=1 exactly at i=z, u+ℓ<0, and g(ℓ)<0<g(u). Write J(c,z,u,ℓ) for the same conditions with u+ℓ≤0. R(c,u,ℓ) means both levels are attained and each value is either one or belongs to [ℓ,u]. The predicate Certified(a) requires nonnegative weights of mass one, both moments equal to a, the exact squared mass, and the squared-distance lower bound for every feasible competitor. A feasible competitor has nonnegative weights of mass one and both moments at least a. E is the sum of squared weights. StrictlyFeasible(w,a) means w is nonnegative of mass one with both moments strictly above a.

**Theorem 1.1 (A finite interpolation certificate).**

$$\begin{aligned}&\forall c:I \to \mathbb{R}, \forall z \in I, \forall u,l \in \mathbb{R}, \operatorname{H}\left(c, z, u, l\right) \land \operatorname{R}\left(c, u, l\right) \longrightarrow \\&b<a_{crit}<1 \land (\forall a \in [a_{crit},1], \operatorname{Certified}(a))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/HighCosineThreshold.high_threshold_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign assumptions imply ℓ < u < 1 by g(x)=(1−x)(2x+1). Interpolate the three weights by a quadratic P with moment coefficients β and γ in the basis 1, x, 2x² − 1. For each of β, γ and the values −P(x) at intermediate levels, take the slope 1 − f(1)/f(0) as a function of r. Let B be the maximum of those slopes and one. The cutoff lies strictly between b and one. At thresholds a in [1 − (1−b)/B, 1] the two moments equal a. The squared mass is (1−r)² + r²(p²/nᵤ + (1−p)²/nₗ), where nᵤ and nₗ are level counts. The excess squared mass of any feasible law bounds its squared distance from the candidate, which gives uniqueness.

**Theorem 1.2 (A feasible descent below the cutoff).**

$$\begin{aligned}&\forall c:I \to \mathbb{R}, \forall z,j,k \in I, \forall u,l \in \mathbb{R}, \operatorname{J}\left(c, z, u, l\right) \land \operatorname{c}\left(j\right)=u \land \operatorname{c}\left(k\right)=l \longrightarrow \\&\forall a \in [b,a_{crit}), \exists w, \operatorname{StrictlyFeasible}(w,a) \land E(w)<E(v_{a})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/HighCosineThreshold.exists_smaller_energy_below_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If u+ℓ=0, the first multiplier has zero intercept and its slope is assigned one, already included in the maximum. When b < a is below the cutoff, all three supporting levels have positive weight. If a moment coefficient is negative, a perturbation within the support increases that moment and preserves the other. If an intermediate value of P is positive, a perturbation adds weight there and uses the three support levels to preserve both moments. A sufficiently small positive step decreases the squared mass in either case. At a = b, the weight at z is zero. A small mixture toward the point mass at z raises both moments and lowers squared mass. For any strict energy decrease, a further small mixture with this point mass preserves the energy inequality and makes both moment constraints strict.

**Theorem 1.3 (The sharp high-threshold interval on a cycle).**

$$\begin{aligned}&\forall q \in \mathbb{N}, q\ge4 \longrightarrow [b<a_{crit}<1,\\&\forall a \in [a_{crit},1], \operatorname{Certified}(a),\\&\forall a \in [b,a_{crit}), \exists w, \operatorname{StrictlyFeasible}(w,a) \land E(w)<E(v_{a})]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/HighCosineThreshold.cyclic_high_threshold_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q at least four use c(k) = cos(2πk/q) on its canonical residue representatives. The first off-center maximum occurs at k = 1, and a minimum occurs at the integer part of q/2. Reflecting angles into [0, π] proves the required level order and strict signs. The cutoff lies strictly between b and one. The law minimizes squared mass from the cutoff through one, and a feasible law has smaller squared mass with both moments strictly above the threshold at every a from b up to the cutoff, excluding the cutoff.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/HighCosineThreshold.cyclic_high_threshold_certificate`
- Truth anchor: `D5/S3/Fourier/Concentration/HighCosineThreshold.exists_smaller_energy_below_threshold`
- Truth anchor: `D5/S3/Fourier/Concentration/HighCosineThreshold.high_threshold_certificate`
