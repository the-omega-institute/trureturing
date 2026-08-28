# Coarse Poisson Semigroup

## Abstract

Poisson convolution transports the observed profile from sigma to sigma plus eta.

**Theorem 1.1 (Coarse Poisson smoothing is a semigroup).**

$$\forall star: \mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall P: \mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall d: \mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall source: \mathbb{R}\to\mathbb{R}, \left(\forall f \in \mathbb{R}\to\mathbb{R}, g \in \mathbb{R}\to\mathbb{R}, h \in \mathbb{R}\to\mathbb{R},\; star(f)(star(g)(h)) = star(star(f)(g))(h)\right) \land \left(\left(\forall sigma \in \mathbb{R}, eta \in \mathbb{R},\; \left(1 < sigma \land 0 < eta\right) \Rightarrow star(P(eta))(P(sigma)) = P(sigma + eta)\right) \land \left(\forall sigma \in \mathbb{R},\; d(sigma) = star(P(sigma))(source)\right)\right) \Rightarrow \forall sigma \in \mathbb{R}, eta \in \mathbb{R},\; \left(1 < sigma \land 0 < eta\right) \Rightarrow d(sigma + eta) = star(P(eta))(d(sigma))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PoissonSemigroup/PoissonSemigroup.coarse_poisson_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-function carrier exposes the source convolution channel, the Poisson kernels P, the observed profiles d, and a fixed source profile. Associativity, the kernel scale-addition law, and the profile representation are independent hypotheses.

At sigma greater than one and eta positive, rewriting the two profile representations and applying the kernel law reduces the result to associativity of convolution.

## References

- Truth anchor: `D5/S3/Weil/PoissonSemigroup/PoissonSemigroup.coarse_poisson_semigroup`
