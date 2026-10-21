# Product Lorentz cones

## Abstract

Self-duality and polynomial square certificates for product Lorentz cones.

**Theorem 1.1 (Self-duality for the standard pairing).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Lorentz.dualCone_cone`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Lorentz.dualCone_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A direct product of a nonnegative orthant and Lorentz cones equals its dual for the coordinate dot product. The dimensions of the orthant and the spatial blocks may be zero. Cauchy-Schwarz gives nonnegativity of each block pairing. Coordinate vectors test orthant positivity; the block vectors (1,0) and (norm(w),-w) recover the Lorentz inequality in the reverse direction.

**Theorem 1.2 (A linear square certificate for the Jordan pullback).**

Lean statement: `D5/S3/QuadraticForms/ConicGDNN/Lorentz.pullback_eq_sum_sq`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ConicGDNN/Lorentz.pullback_eq_sum_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pairing a vector in the product cone with the Jordan square yields a finite sum of squares of homogeneous linear polynomials. An orthant coordinate uses the square root of its nonnegative coefficient. For a Lorentz block with time coefficient alpha and spatial vector w, alpha=0 forces w=0. For alpha>0 the certificate is the sum over i of (alpha z_i+w_i t)^2/alpha, plus ((alpha^2-sum_i w_i^2)/alpha)t^2. Expanding the squares recovers alpha(t^2+sum_i z_i^2)+2t sum_i w_i z_i. All coefficients are nonnegative and are absorbed into the linear factors by their real square roots.

## References

- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Lorentz.dualCone_cone`
- Truth anchor: `D5/S3/QuadraticForms/ConicGDNN/Lorentz.pullback_eq_sum_sq`
- Dependency: [D5/S3/QuadraticForms/ConicGDNN/Defs](Defs.md)
