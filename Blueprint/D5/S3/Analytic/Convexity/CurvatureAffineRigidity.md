# Affine rigidity and curvature support

## Abstract

Local affine rigidity of a convex function forces full support of its right-derivative Stieltjes curvature unless the function is globally affine.

Let f be a real convex function on (0,infinity). Affine rigidity means that for every real a,b,alpha,beta with 0<a<b, equality f(x)=alpha*x+beta for all a<x<b implies that same equality for every x>0. Nonaffineness means there are no real alpha,beta representing f on the entire positive ray. These are the complete hypotheses of the theorem below. Curvature is the existing actual right-derivative Stieltjes measure, and support is taken in the subtype Positive=(0,infinity).

**Theorem 1.1 (Full support from local affine rigidity).**

$$\forall f : \mathbb{R}\to\mathbb{R}, (\forall hf : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), (\operatorname{AffineRigidity}\left(f\right) \Rightarrow \left(\operatorname{Nonaffine}\left(f\right) \Rightarrow \operatorname{support}\left(\operatorname{curvature}\left(hf\right)\right) = \operatorname{univPositive}\left(\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/CurvatureAffineRigidity.full_support_of_affine_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem quantifies over every real function f, its scalar convexity proof hf, the full local-to-global rigidity property stated above, and global nonaffineness. If the right derivatives at two positive endpoints were equal, the convex secant slope is squeezed between them. This gives an affine formula throughout their open interval. Rigidity would then contradict nonaffineness. Thus the right derivative is strictly increasing. The exact curvature_Ioc identity gives positive mass to every positive half-open interval. Every neighborhood in Positive contains such an interval, which proves the displayed support equality.

This scalar bridge assumes no curvature support, strict convexity, smoothness, atomlessness, finite total mass or endpoint regularity. OperatorConvexCurvature supplies its affine rigidity property by actual two-dimensional operator-convex functional calculus. The bridge is a classical necessary supplier; it does not settle the Hiai–Mosonyi–Tomamichel divergence equality classification.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/CurvatureAffineRigidity.full_support_of_affine_rigidity`
- Dependency: [D5/S3/Analytic/Convexity/CurvatureHingeRepresentation](CurvatureHingeRepresentation.md)
