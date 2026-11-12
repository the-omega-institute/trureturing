# Discrete Hyperbolic-Secant Path

## Abstract

Every finite step on a discrete hyperbolic-secant path stays strictly above zero.

**Theorem 1.1 (The discrete sech path is positive).**

$$\forall k : \mathbb{N}, 0 < \frac{1}{\operatorname{cosh}(eta0 + (k : \mathbb{R}) \cdot delta)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/SechPath.discrete_sech_path_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real hyperbolic cosine is strictly positive at every real argument. Taking its reciprocal therefore keeps every finite discrete step strictly above zero, independently of the starting rapidity and step size.

## References

- Truth anchor: `D5/S0/Diagonal/SechPath.discrete_sech_path_positive`
