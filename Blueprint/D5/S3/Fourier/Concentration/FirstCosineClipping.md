# First clipping threshold for two cosine moments

## Abstract

The first support change for two cosine constraints has an exact threshold and a quadratic rate in the modulus.

For k modulo q write c(k) = cos(2πk/q), d(k) = cos(4πk/q), and s(k) = c(k)+d(k). Let M₁ and M₂ denote the corresponding weighted moments, and let E be squared mass. The threshold attached to an attained minimum m of s is T(m) = −1/(2m).

For each real a, set v(k) = (1+2as(k))/q, L = (1+4a²)/q, D(w) = E(w−v), and N(v) = Σₖ max(0,−v(k))². The notation P(w) means w is a nonnegative real weight of total mass one with both moments at least a. All competitors are real functions on the residues, and all k-sums run over the residues.

**Theorem 1.1 (Sharp squared mass before clipping).**

$$\begin{aligned}&\forall q \in \mathbb{N},\quad q \ge 5:\\&\exists m \in \mathbb{R},\quad(\exists k, m=\operatorname{s}\left(k\right)) \land (\forall k, m \le \operatorname{s}\left(k\right))\\&\quad \land \frac{4}{9}<\operatorname{T}\left(m\right) \le \frac{4}{9}+\frac{16\pi^{2}}{9q^{2}},\\&\quad \forall a \in \mathbb{R}:\\&\quad \sum_{k}\operatorname{v}\left(k\right)=1,\quad \left(M_{1}\right)\left(v\right)=\left(M_{2}\right)\left(v\right)=a,\\&\quad \forall w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R},\quad \sum_{k}\operatorname{w}\left(k\right)=1 \longrightarrow \operatorname{E}\left(w\right)-L=\operatorname{D}\left(w\right)+\frac{4a}{q}(\left(M_{1}\right)\left(w\right)+\left(M_{2}\right)\left(w\right)-2a),\\&\quad a \ge 0 \longrightarrow [\\&\quad\quad (\forall k, \operatorname{v}\left(k\right) \ge 0) \iff a \le \operatorname{T}\left(m\right),\\&\quad\quad \operatorname{T}\left(m\right) < a \longrightarrow 0 < \operatorname{N}\left(v\right),\\&\quad \forall w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R},\quad \operatorname{P}\left(w\right) \longrightarrow L+\operatorname{N}\left(v\right) \le \operatorname{E}\left(w\right) \land (\operatorname{E}\left(w\right)=L \iff w=v),\\&\quad (\exists w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R}, \operatorname{P}\left(w\right) \land \operatorname{E}\left(w\right)=L) \iff a \le \operatorname{T}\left(m\right)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FirstCosineClipping.first_cosine_clipping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Character orthogonality gives the affine law total mass one and the two moments a. Expanding its squared distance from a mass-one competitor gives the exact remainder. For a ≥ 0, any feasible competitor pays at least the squared negative entries of that affine law. Above the cutoff a minimizing residue has a negative affine entry, so the penalty is positive. Equality with L forces all Euclidean distance terms to vanish.

Completing the square gives s(k) = 2(c(k)+1/4)²−9/8. Niven’s theorem excludes the value −1/4 for c(k) because the angle is a rational multiple of π. This gives the strict lower bound on T(m). Rounding the angle whose cosine is −1/4 to the nearest grid point controls the squared error by (π/q)². The mean-zero and second-moment identities imply m ≤ −1/2 by summing (2−s(k))(s(k)−m). These two bounds control the reciprocal threshold.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FirstCosineClipping.first_cosine_clipping`
- Dependency: [D5/S3/Fourier/Concentration/AggregateCosineBalance](AggregateCosineBalance.md)
