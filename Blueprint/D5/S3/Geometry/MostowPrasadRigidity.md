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

**Definition 1.3 (Existence and uniqueness obligations).**

The endpoint is split into explicit predicates:

- `D5/S3/Geometry/MostowPrasadRigidity.HasIsometryRepresentative`
- `D5/S3/Geometry/MostowPrasadRigidity.UniqueIsometryRepresentative`
- `D5/S3/Geometry/MostowPrasadRigidity.MostowPrasadRigidityEndpoint`

The first says that a given homotopy equivalence has an isometric representative;
the second says that such a representative is unique within its homotopy class;
the third combines them into the exact `∀ h, ∃! e` target for one pair of
metric spaces.

**Theorem 1.4 (An isometry supplies its own representative).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.hasIsometryRepresentative_of_isometry`

Every isometry equivalence induces a homotopy equivalence, and is itself a
representative of that homotopy equivalence.

*Proof.* Machine-checked in Lean. ∎

**Theorem 1.5 (Dense boundary criterion for uniqueness).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.uniqueIsometryRepresentative_of_eqOn_dense`

If a future boundary or holonomy argument proves equality on a dense subset for
any two representatives, the representatives are equal. This is the exact
handoff from the geometric boundary argument to the metric uniqueness layer.

*Proof.* Machine-checked in Lean. ∎

**Theorem 1.6 (Existence plus uniqueness gives the endpoint).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.existsUnique_isometryRepresentative_of_parts`

The two obligations combine to the required unique-isometry conclusion without
introducing any hidden axiom.

*Proof.* Machine-checked in Lean. ∎

**Definition 1.7 (Group conjugacy interface).**

Lean definition:
`D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`

For `e : G ≃* H`, `ρ : G →* K`, and `σ : H →* K`, this means that there is
an ambient element `a : K` such that
`σ (e g) = a * ρ g * a⁻¹` for every `g`. This is the exact algebraic shape of
the lattice-conjugacy statement used by Mostow--Prasad.

**Theorem 1.8 (Conjugacy is symmetric and compositional).**

Lean statements:

- `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`
- `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`

*Proof.* Machine-checked in Lean. ∎

**Theorem 1.9 (Uniqueness of the conjugator under trivial centralizer).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`

If the centralizer of the image of `ρ` is trivial, two ambient conjugators
implementing the same group isomorphism are equal. This exposes the precise
remaining geometric input needed to turn algebraic conjugacy into uniqueness.

*Proof.* Machine-checked in Lean. ∎

**Definition 1.10 (Dense holonomy orbit).**

Lean definition:
`D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`

For a representation into the isometry group of a metric space, `DenseOrbit`
records that the orbit of a chosen basepoint is dense.

**Theorem 1.11 (Dense orbit implies trivial centralizer under basepoint control).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`

If every centralizing isometry fixes the basepoint and its orbit is dense, then
the centralizer of the representation image is trivial. The proof uses
continuity and the dense-set uniqueness theorem above.

*Proof.* Machine-checked in Lean. ∎

**Theorem 1.12 (Dense attracting poles imply a trivial centralizer).**

Lean statement:
`D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_attracting_poles`

```lean
theorem rangeCentralizerTrivial_of_dense_attracting_poles
    {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
    (rho : G →* (X ≃ₜ X))
    (hthree : ∀ b c : X, ∃ x : X, x ≠ b ∧ x ≠ c)
    (hdense : Dense {a : X | ∃ (g : G) (b : X), a ≠ b ∧
      ∀ x : X, x ≠ b →
        Tendsto (fun n : ℕ => ((rho g : X → X)^[n]) x) atTop (𝓝 a)}) :
    RangeCentralizerTrivial rho
```

*Proof.* Machine-checked in Lean at
`D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_attracting_poles`.
For each attracting pole, choose a point away from both the repelling point
and its inverse image under a centralizing homeomorphism. Commutation of all
iterates and continuity give two limits for the same orbit, so Hausdorff
uniqueness fixes that pole. Density and `DenseRange.equalizer` then fix every
point, and `Homeomorph.ext` gives the identity. ∎

*Source.* Repository-derived using Mathlib's `Function.Commute.iterate_right`,
`tendsto_nhds_unique`, and `DenseRange.equalizer`.

## Full endpoint still open

The intended endpoint is: every homotopy equivalence between connected,
complete, finite-volume, curvature `-1` hyperbolic three-manifolds is homotopic
to a unique isometry. The attracting-poles criterion is conditional: it does
not construct an ideal boundary, establish north-south dynamics or density of
attracting poles for a lattice, prove faithfulness, or construct a conjugator.
The full endpoint also still needs complete finite-volume hyperbolic geometry,
the holonomy bridge, conjugator existence, and the homotopy-to-isometry
existence theorem.

## References

- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_eqOn_dense`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.isometry_equiv_eq_of_dense_range`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.HasIsometryRepresentative`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.UniqueIsometryRepresentative`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.MostowPrasadRigidityEndpoint`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.hasIsometryRepresentative_of_isometry`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.uniqueIsometryRepresentative_of_eqOn_dense`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.existsUnique_isometryRepresentative_of_parts`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.GroupConjugacy`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_symm`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_trans`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.groupConjugacy_conjugator_unique`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.DenseOrbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_orbit`
- Truth anchor: `D5/S3/Geometry/MostowPrasadRigidity.rangeCentralizerTrivial_of_dense_attracting_poles`
