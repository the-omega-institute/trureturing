/- GID: D5/S3/Arith/IcosahedralAxisNormalizerDecomposition
   generality: I
   mirror-B: D5/B/S3/Arith/IcosahedralAxisNormalizerDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The 6/10/15 projective axis classes have normalizer orders 10/6/4. -/

/- Library-search audit trail (2026-08-31):
   * Repository searches for the combined decomposition-and-normalizer statement
     found no exact declaration. The canonical component theorems are in
     `D5.S3.Arith.IcosahedralAxisDecomposition` and are reused below.
   * Pinned Mathlib searches found generic orbit-stabilizer and Sylow normalizer
     results, but no theorem about these concrete projective classes or axes.
   * No new object is introduced: the public theorem uses the frozen family's
     projective classes, cyclic axes, normalizer, centralizer, and equivalences. -/

import D5.S3.Arith.IcosahedralAxisDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.IcosahedralAxisNormalizerDecomposition

open D5.S3.Arith.IcosahedralAxisDecomposition

/- The finite projective plane is the disjoint union of its three axis classes.
Their cardinalities are 6, 10, and 15, the classes biject with the corresponding
cyclic-axis families, and the normalizer orders are 10, 6, and 4. At order two,
the normalizer is the generator centralizer. -/
theorem finite_icosahedral_axis_decomposition_with_normalizers :
    (projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
          projectiveAxisPointSet .twofold = Finset.univ ∧
        Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) ∧
        Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) ∧
        Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold)) ∧
      (Fintype.card FivefoldProjectivePoints = 6 ∧
        Fintype.card ThreefoldProjectivePoints = 10 ∧
        Fintype.card TwofoldProjectivePoints = 15) ∧
      (Fintype.card FivefoldProjectivePoints = Fintype.card FivefoldAxes ∧
        Fintype.card ThreefoldProjectivePoints = Fintype.card ThreefoldAxes ∧
        Fintype.card TwofoldProjectivePoints = Fintype.card TwofoldAxes) ∧
      (Fintype.card FivefoldAxes = 6 ∧
        Fintype.card ThreefoldAxes = 10 ∧
        Fintype.card TwofoldAxes = 15 ∧
        (∀ g h : FivefoldAxes, axesAreConjugate 5 g h) ∧
        (∀ g h : ThreefoldAxes, axesAreConjugate 3 g h) ∧
        (∀ g h : TwofoldAxes, axesAreConjugate 2 g h)) ∧
      ((∀ g : FivefoldAxes, (cyclicAxisNormalizer 5 g).card = 10) ∧
        (∀ g : ThreefoldAxes, (cyclicAxisNormalizer 3 g).card = 6) ∧
        (∀ g : TwofoldAxes, (cyclicAxisNormalizer 2 g).card = 4) ∧
        (∀ g : TwofoldAxes, cyclicAxisNormalizer 2 g = elementCentralizer g)) := by
  have projectiveCards := finite_projective_axis_cardinalities
  have axisOrbits := icosahedral_axis_orbits
  exact ⟨finite_projective_axis_partition, projectiveCards,
    ⟨projectiveCards.1.trans axisOrbits.1.symm,
      projectiveCards.2.1.trans axisOrbits.2.1.symm,
      projectiveCards.2.2.trans axisOrbits.2.2.1.symm⟩,
    axisOrbits, icosahedral_axis_stabilizer_orders⟩

#print axioms finite_icosahedral_axis_decomposition_with_normalizers

-- The concrete projective carrier is inhabited independently of the theorem.
example : FiniteProjectivePlane := .inr (.inr ())

end D5.S3.Arith.IcosahedralAxisNormalizerDecomposition
