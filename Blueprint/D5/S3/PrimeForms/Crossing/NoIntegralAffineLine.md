# No Integral Affine Line on the Crossing Surface

## Abstract

The crossing quadratic surface contains no nonconstant integral affine line.

**Theorem 1.1 (Every integral affine line on the surface is constant).**

$$\forall b,c,t,u,v,w\in\mathbb{Z}, (\forall n\in\mathbb{Z}, (b+nu)^{2}-(b+nu)(c+nv)+(c+nv)^{2}-(t+nw)^{2}=-1) \Rightarrow u=0 \land v=0 \land w=0$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/NoIntegralAffineLine.crossing_surface_has_no_nonconstant_integral_affine_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every integer point of the affine line with base point (b,c,t) and direction (u,v,w) lies on b^2 - bc + c^2 - t^2 = -1. Then its direction is zero, so the line is constant.

Evaluating at n = 0, 1, and -1 separates the base-point equation, the direction's null-cone equation, and their bilinear orthogonality. The binary quadratic identity 4 q(b,c) q(u,v) - B^2 = 3 (bv-cu)^2 then turns the surface value -1 into a sum-of-squares obstruction, forcing w, v, and u successively to vanish.

Repository and pinned-Mathlib searches found no exact theorem excluding integral affine lines from this indefinite quadratic surface. LeanSearch returned only generic affine-line and quadratic-map declarations, including AffineMap.lineMap_eq_lineMap_iff and QuadraticMap.PosDef.anisotropic, neither of which proves this case. The proof therefore uses Mathlib's ring and nlinarith tactics for the explicit polynomial and nonnegativity steps.

This formalizes only appendix E.33's explicitly named no-integral-line lemma. It does not claim the surrounding half-dimension theorem or any counting estimate for the exceptional set.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/NoIntegralAffineLine.crossing_surface_has_no_nonconstant_integral_affine_line`
