# Euler Characteristic of a Three-Term Finite-Dimensional Complex

## Abstract

A finite-dimensional chain U to V to W over a field satisfies the Euler
characteristic identity after writing its homology as explicit kernel and
quotient spaces.

**Theorem 1.1 (Three-term Euler identity).** Let f : U to V and
g : V to W be maps between finite-dimensional K-vector spaces with
g.comp f = 0. Restrict f to the codomain ker g, so its range is a
submodule of ker g. Then

$$
dim U + dim W + dim(ker g / range f)
=
dim V + dim(W / range g) + dim ker f.
$$

*Proof.* Machine-checked in Lean as
D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.finrank_three_term_euler
(standard tier). ∎

*Source.* The finite-dimensional Euler characteristic calculation is the
standard rank-nullity argument for a bounded chain complex. The explicit
kernel and quotient formulation is repository-derived.

## Commentary

The restricted map is middleDifferential f g hgf; its range is a submodule of
ker g, making the middle homology quotient a concrete Lean type. The proof
uses Mathlib's rank-nullity theorem for f, g, and the restricted map, then
uses the quotient rank formula for ker g / range(f) and W / range(g). No
subtraction in Nat is used: the identity is stated as an additive equality.

The theorem is a finite-dimensional three-term specialization. It does not
claim a categorical homology object, a splitting, or an extension to
infinite-dimensional complexes.

## References

- Truth anchor:
  D5/S3/HomologicalAlgebra/FiniteDimensionalEulerCharacteristic.finrank_three_term_euler
- Charles A. Weibel, An Introduction to Homological Algebra (1994), Chapter 1,
  https://doi.org/10.1017/CBO9781139644136
