# Euler Characteristic of a Three-Term Finite-Dimensional Complex

## Abstract

A finite-dimensional three-term chain complex satisfies an explicit Euler characteristic identity.

**Theorem 1.1 (Three-term Euler identity).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.finrank_three_term_euler`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.finrank_three_term_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Charles A. Weibel (1994). *An Introduction to Homological Algebra*. DOI: [10.1017/CBO9781139644136](https://doi.org/10.1017/CBO9781139644136).

*Commentary.*

Let f : U to V and g : V to W be maps of finite-dimensional vector spaces over a field with g composed with f equal to zero. The map f is codomain-restricted to ker(g), so its range is a submodule of ker(g). The dimensions of U and W together with the middle quotient ker(g) / range(f) equal the dimension of V together with the endpoint quotient W / range(g) and ker(f).

The proof is a rank-nullity calculation for f, g, and the codomain-restricted map, followed by the quotient rank formula. It is stated as an additive equality in natural dimensions, so no subtraction convention is needed.

Weibel's Chapter 1 supplies the standard finite-dimensional Euler-characteristic context. The explicit Lean quotient types and the machine-checked equality are repository-derived; no splitting or infinite-dimensional statement is asserted.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.finrank_three_term_euler`
