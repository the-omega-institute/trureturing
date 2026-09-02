# Positive Poisson Semigroup

## Abstract

Every positive completion depth propagates by further Poisson smoothing alone.

**Theorem 1.1 (Positive completion depths form a Poisson semigroup).**

$$\forall star: \mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall P: \mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall completion: \mathbb{R}\to\mathbb{R}\to\mathbb{R}, \forall source: \mathbb{R}\to\mathbb{R}, \left(\forall f \in \mathbb{R}\to\mathbb{R}, g \in \mathbb{R}\to\mathbb{R}, k \in \mathbb{R}\to\mathbb{R},\; star(f)(star(g)(k)) = star(star(f)(g))(k)\right) \land \left(\left(\forall x \in \mathbb{R}, h \in \mathbb{R},\; \left(0 < x \land 0 < h\right) \Rightarrow star(P(h))(P(x)) = P(x + h)\right) \land \left(\forall x \in \mathbb{R},\; completion(x) = star(P(x))(source)\right)\right) \Rightarrow \forall x \in \mathbb{R}, h \in \mathbb{R},\; \left(0 < x \land 0 < h\right) \Rightarrow completion(x + h) = star(P(h))(completion(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/PositivePoissonSemigroup.positive_poisson_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public statement exposes the real-line convolution channel, the Poisson kernel family, the completion profiles, and their fixed boundary source. Associativity, kernel scale addition, and the profile representation are independent source laws.

For every positive initial depth and positive increment, the deeper profile is obtained solely by applying the increment kernel to the shallower profile. No additional source term occurs.

The proof positively rescales the depth coordinate and applies the frozen coarse semigroup theorem.

## References

- Truth anchor: `D5/S3/Weil/Scattering/PositivePoissonSemigroup.positive_poisson_semigroup`
- Dependency: [D5/S3/Weil/Scattering/PoissonSemigroup](PoissonSemigroup.md)
