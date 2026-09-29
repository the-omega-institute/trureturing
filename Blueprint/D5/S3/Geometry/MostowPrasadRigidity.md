# Mostow--Prasad rigidity: metric uniqueness interface

## Abstract

The reusable interfaces for the Mostow--Prasad endpoint have two layers. The
metric layer says that an isometry equivalence is determined by its values on a
dense subset. The group layer records the statement that an abstract group
isomorphism between holonomy domains is realized by conjugacy in an ambient
group, and isolates the centralizer condition needed for uniqueness. The full
theorem additionally requires complete finite-volume hyperbolic three-manifolds,
curvature normalization, the existence theorem, and the homotopy-to-isometry
bridge. None of those geometric hypotheses is hidden in this module.

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

**Definition 1.3 (Group conjugacy interface).**

Lean definition:
`D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`

For `e : G ≃* H`, `ρ : G →* K`, and `σ : H →* K`, this means that there is
an ambient element `a : K` such that
`σ (e g) = a * ρ g * a⁻¹` for every `g`. This is the exact algebraic shape of
the lattice-conjugacy statement used by Mostow--Prasad.

**Theorem 1.4 (Conjugacy is symmetric and compositional).**

Lean statements:

- `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`
- `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`

*Proof.* Machine-checked in Lean. ∎

**Theorem 1.5 (Uniqueness of the conjugator under trivial centralizer).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`

If the centralizer of the image of `ρ` is trivial, two ambient conjugators
implementing the same group isomorphism are equal. This exposes the precise
remaining geometric input needed to turn algebraic conjugacy into uniqueness.

*Proof.* Machine-checked in Lean. ∎

**Definition 1.6 (Dense holonomy orbit).**

Lean definition:
`D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`

For a representation into the isometry group of a metric space, `DenseOrbit`
records that the orbit of a chosen basepoint is dense.

**Theorem 1.7 (Dense orbit implies trivial centralizer under basepoint control).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`

If every centralizing isometry fixes the basepoint and its orbit is dense, then
the centralizer of the representation image is trivial. The proof uses
continuity and the dense-set uniqueness theorem above.

*Proof.* Machine-checked in Lean. ∎

## Full endpoint still open

The intended endpoint is: every homotopy equivalence between connected,
complete, finite-volume, curvature `-1` hyperbolic three-manifolds is homotopic
to a unique isometry. The present module proves only the metric and algebraic
interfaces; it does not prove existence, finite-volume rigidity, the holonomy
construction, or the hyperbolic lattice conjugacy theorem.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`
