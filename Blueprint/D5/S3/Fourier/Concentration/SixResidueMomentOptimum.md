# Minimum squared mass for two modes modulo six

## Abstract

Two real character modes on six residues have an exact common-threshold minimum squared mass.

Use the residues k = 0 through 5 and the real modes c(k) = cos(πk/3) and d(k) = cos(2πk/3). Write E for the sum of squared weights and M₁, M₂ for the respective weighted moments, with each sum over the six residues. For a ≤ 1/2 take v = ((1+4a)/6, 1/6, (1−2a)/6, 1/6, (1−2a)/6, 1/6). For a > 1/2 take v = (a, (1−a)/3, 0, (1−a)/3, 0, (1−a)/3). For every real t, put uₜ(k) = max(0, 1 − t(1−c(k))) and pₜ(k) = uₜ(k)/∑ⱼuₜ(j).

**Theorem 1.1 (The common-threshold optimum and the one-mode comparison).**

$$\begin{aligned}&\forall a \in \mathbb{R},\quad0 \le a \le 1:\\&\forall k, \operatorname{v}\left(k\right) \ge0,\quad \sum_{k}\operatorname{v}\left(k\right)=1,\quad \left(M_{1}\right)\left(v\right)=\left(M_{2}\right)\left(v\right)=a,\\&a \le \frac{1}{2} \longrightarrow \operatorname{E}\left(v\right)=\frac{1+4a^{2}}{6},\\&\frac{1}{2}<a \longrightarrow \operatorname{E}\left(v\right)=a^{2}+\frac{(1-a)^{2}}{3},\\&\forall w:\operatorname{Fin}\left(6\right) \to \mathbb{R},\quad(\forall k, \operatorname{w}\left(k\right) \ge0) \land \sum_{k}\operatorname{w}\left(k\right)=1 \land \left(M_{1}\right)\left(w\right)+\left(M_{2}\right)\left(w\right) \ge 2a\\&\quad \longrightarrow \operatorname{E}\left(w-v\right) \le \operatorname{E}\left(w\right)-\operatorname{E}\left(v\right),\\&\forall t \in \mathbb{R},\quad0<a<1 \land \left(M_{1}\right)\left(p_{t}\right)=a \longrightarrow \left(M_{2}\right)\left(p_{t}\right)<a.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/SixResidueMomentOptimum.six_two_mode_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The energy comparison applies to every nonnegative probability law w for which M₁(w) + M₂(w) ≥ 2a. This includes arbitrary nonsymmetric laws satisfying the two individual bounds.

The combined readout c+d takes the values 2, 0 and −1. On each set where c+d is constant the differences c−d sum to zero. A weight depending only on c+d therefore has equal moments M₁ and M₂. Apply the one-moment optimizer to c+d at threshold 2a and anchor 2. The cutoff is 1/2. The indices with aggregate readout −1 vanish when t reaches 1/3, corresponding to a = 1/2. Evaluating the remaining affine weights yields the two formulas.

For the optimizer of the first mode alone, attaining an interior moment requires 0 < t < 2. Its raw weight at residue 1 then exceeds its raw weight at residue 3, and residues 1 and 5 have equal weight. Since M₁(p)−M₂(p) = p(1)+p(5)−2p(3), this gives the strict comparison.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/SixResidueMomentOptimum.six_two_mode_optimum`
- Dependency: [D5/S3/Fourier/Concentration/ClippedMomentWeights](ClippedMomentWeights.md)
