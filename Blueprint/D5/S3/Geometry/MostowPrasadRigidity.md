# Mostow--Prasad rigidity: metric uniqueness interface

## Abstract

The first reusable interface for the Mostow--Prasad endpoint is the metric
uniqueness principle: an isometry equivalence is determined by its values on a
dense subset. The full theorem additionally requires complete finite-volume
hyperbolic three-manifolds, curvature normalization, the existence theorem, and
the homotopy-to-isometry bridge. None of those geometric hypotheses is hidden
in this module.

**Theorem 1.1 (Dense-set uniqueness of isometries).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`

*Proof.* Machine-checked in Lean as
`D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense` (`✓ std3`).
∎

*Source.* Repository-derived from Mathlib's `DenseRange.equalizer` and
`IsometryEquiv.ext`.

*Commentary.*

If two isometries agree on a dense subset of the source, continuity extends the
agreement to every point. This supplies the equality step after a geometric
argument has reduced two candidate Mostow--Prasad maps to a dense family of
points.

**Theorem 1.2 (Dense-range uniqueness).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`

*Proof.* Machine-checked in Lean as
`D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range` (`✓ std3`).
∎

*Source.* Repository-derived from Mathlib's `DenseRange.equalizer`.

*Commentary.*

The pointwise form accepts a dense parametrization directly, which is useful for
developing boundary or orbit models without introducing a second copy of the
dense subset as a set.

## Full endpoint still open

The intended endpoint is: every homotopy equivalence between connected,
complete, finite-volume, curvature `-1` hyperbolic three-manifolds is homotopic
to a unique isometry. The present module proves only the metric uniqueness
interface; it does not prove existence, finite-volume rigidity, or the
hyperbolic lattice conjugacy theorem.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`
