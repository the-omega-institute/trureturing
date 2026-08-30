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

/- The standard five-coordinate permutation module has a sum-zero subspace. In
characteristic five its constant vector lies in that subspace, and the quotient
has dimension three. The representative below fixes the last coordinate at zero. -/
def boundaryModuleRepresentative (v : BoundaryVector) : Fin 5 → ZMod 5 :=
  ![v 0, v 1, v 2, -(v 0 + v 1 + v 2), 0]

/- Subtracting the last coordinate chooses the same representative after a
permutation of the five coordinates. -/
def boundaryModuleProjection (v : Fin 5 → ZMod 5) : BoundaryVector :=
  ![v 0 - v 4, v 1 - v 4, v 2 - v 4]

/-- The faithful three-dimensional action induced by the natural `A₅`
permutation action on the sum-zero module modulo its constant line. -/
def icosahedralBoundaryAction
    (g : IcosahedralRotationGroup) (v : BoundaryVector) : BoundaryVector :=
  boundaryModuleProjection fun i => boundaryModuleRepresentative v ((g.1)⁻¹ i)

/-- A represented cyclic axis is incident to a projective direction when its
canonical generator fixes that direction in the three-dimensional action. -/
def axisFixesProjectivePoint {order : Nat}
    (axis : CyclicAxes order) (point : FiniteProjectivePlane) : Prop :=
  icosahedralBoundaryAction axis.1 (projectiveVector point) = projectiveVector point

private instance axisFixesProjectivePointDecidable {order : Nat}
    (axis : CyclicAxes order) (point : FiniteProjectivePlane) :
    Decidable (axisFixesProjectivePoint axis point) :=
  inferInstanceAs (Decidable
    (icosahedralBoundaryAction axis.1 (projectiveVector point) = projectiveVector point))

private theorem fivefold_axis_unique_for_point :
    ∀ point : FivefoldProjectivePoints,
      ∃ axis : FivefoldAxes,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : FivefoldAxes,
            axisFixesProjectivePoint other point.1 → other = axis := by
  set_option maxRecDepth 100000 in
    decide

private theorem threefold_axis_unique_for_point :
    ∀ point : ThreefoldProjectivePoints,
      ∃ axis : ThreefoldAxes,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : ThreefoldAxes,
            axisFixesProjectivePoint other point.1 → other = axis := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_axis_unique_for_point :
    ∀ point : TwofoldProjectivePoints,
      ∃ axis : TwofoldAxes,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : TwofoldAxes,
            axisFixesProjectivePoint other point.1 → other = axis := by
  set_option maxRecDepth 100000 in
    decide

private theorem fivefold_point_unique_for_axis :
    ∀ axis : FivefoldAxes,
      ∃ point : FivefoldProjectivePoints,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : FivefoldProjectivePoints,
            axisFixesProjectivePoint axis other.1 → other = point := by
  set_option maxRecDepth 100000 in
    decide

private theorem threefold_point_unique_for_axis :
    ∀ axis : ThreefoldAxes,
      ∃ point : ThreefoldProjectivePoints,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : ThreefoldProjectivePoints,
            axisFixesProjectivePoint axis other.1 → other = point := by
  set_option maxRecDepth 100000 in
    decide

private theorem twofold_point_unique_for_axis :
    ∀ axis : TwofoldAxes,
      ∃ point : TwofoldProjectivePoints,
        axisFixesProjectivePoint axis point.1 ∧
          ∀ other : TwofoldProjectivePoints,
            axisFixesProjectivePoint axis other.1 → other = point := by
  set_option maxRecDepth 100000 in
    decide

/-- The fivefold axis is the unique order-five cyclic axis fixing the point. -/
noncomputable def fivefoldProjectiveAxisMap
    (point : FivefoldProjectivePoints) : FivefoldAxes :=
  Classical.choose (fivefold_axis_unique_for_point point)

/-- The threefold axis is the unique order-three cyclic axis fixing the point. -/
noncomputable def threefoldProjectiveAxisMap
    (point : ThreefoldProjectivePoints) : ThreefoldAxes :=
  Classical.choose (threefold_axis_unique_for_point point)

/-- The twofold axis is the unique order-two cyclic axis fixing the point. -/
noncomputable def twofoldProjectiveAxisMap
    (point : TwofoldProjectivePoints) : TwofoldAxes :=
  Classical.choose (twofold_axis_unique_for_point point)

theorem fivefoldProjectiveAxisMap_fixes (point : FivefoldProjectivePoints) :
    axisFixesProjectivePoint (fivefoldProjectiveAxisMap point) point.1 :=
  (Classical.choose_spec (fivefold_axis_unique_for_point point)).1

theorem threefoldProjectiveAxisMap_fixes (point : ThreefoldProjectivePoints) :
    axisFixesProjectivePoint (threefoldProjectiveAxisMap point) point.1 :=
  (Classical.choose_spec (threefold_axis_unique_for_point point)).1

theorem twofoldProjectiveAxisMap_fixes (point : TwofoldProjectivePoints) :
    axisFixesProjectivePoint (twofoldProjectiveAxisMap point) point.1 :=
  (Classical.choose_spec (twofold_axis_unique_for_point point)).1

private theorem bijective_of_unique_incidence
    {Point Axis : Type}
    (incidence : Point → Axis → Prop)
    (axisMap : Point → Axis)
    (axisMap_spec : ∀ point, incidence point (axisMap point))
    (axis_unique : ∀ point,
      ∃ axis, incidence point axis ∧
        ∀ other, incidence point other → other = axis)
    (point_unique : ∀ axis,
      ∃ point, incidence point axis ∧
        ∀ other, incidence other axis → other = point) :
    Function.Bijective axisMap := by
  constructor
  · intro left right h
    have hleft := axisMap_spec left
    have hright := axisMap_spec right
    rw [h] at hleft
    rcases point_unique (axisMap right) with ⟨point, _, unique⟩
    exact (unique left hleft).trans (unique right hright).symm
  · intro axis
    rcases point_unique axis with ⟨point, hpoint, _⟩
    rcases axis_unique point with ⟨fixedAxis, _, unique⟩
    exact ⟨point,
      (unique (axisMap point) (axisMap_spec point)).trans
        (unique axis hpoint).symm⟩

private theorem fivefoldProjectiveAxisMap_bijective :
    Function.Bijective fivefoldProjectiveAxisMap :=
  bijective_of_unique_incidence
    (fun point axis => axisFixesProjectivePoint axis point.1)
    fivefoldProjectiveAxisMap fivefoldProjectiveAxisMap_fixes
    fivefold_axis_unique_for_point fivefold_point_unique_for_axis

private theorem threefoldProjectiveAxisMap_bijective :
    Function.Bijective threefoldProjectiveAxisMap :=
  bijective_of_unique_incidence
    (fun point axis => axisFixesProjectivePoint axis point.1)
    threefoldProjectiveAxisMap threefoldProjectiveAxisMap_fixes
    threefold_axis_unique_for_point threefold_point_unique_for_axis

private theorem twofoldProjectiveAxisMap_bijective :
    Function.Bijective twofoldProjectiveAxisMap :=
  bijective_of_unique_incidence
    (fun point axis => axisFixesProjectivePoint axis point.1)
    twofoldProjectiveAxisMap twofoldProjectiveAxisMap_fixes
    twofold_axis_unique_for_point twofold_point_unique_for_axis

/- The finite projective plane is the disjoint union of its three axis classes.
The structural maps send a point to its unique fixed cyclic axis. Their
cardinalities are 6, 10, and 15, and the normalizer orders are 10, 6, and 4.
At order two, the normalizer is the generator centralizer. -/
theorem finite_icosahedral_axis_decomposition_with_normalizers :
    (projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
          projectiveAxisPointSet .twofold = Finset.univ ∧
        Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) ∧
        Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) ∧
        Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold)) ∧
      ((Function.Bijective fivefoldProjectiveAxisMap ∧
          Function.Bijective threefoldProjectiveAxisMap ∧
          Function.Bijective twofoldProjectiveAxisMap) ∧
        ((∀ point : FivefoldProjectivePoints,
            axisFixesProjectivePoint (fivefoldProjectiveAxisMap point) point.1) ∧
          (∀ point : ThreefoldProjectivePoints,
            axisFixesProjectivePoint (threefoldProjectiveAxisMap point) point.1) ∧
          (∀ point : TwofoldProjectivePoints,
            axisFixesProjectivePoint (twofoldProjectiveAxisMap point) point.1))) ∧
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
  exact ⟨finite_projective_axis_partition,
    ⟨⟨fivefoldProjectiveAxisMap_bijective,
        threefoldProjectiveAxisMap_bijective,
        twofoldProjectiveAxisMap_bijective⟩,
      ⟨fivefoldProjectiveAxisMap_fixes,
        threefoldProjectiveAxisMap_fixes,
        twofoldProjectiveAxisMap_fixes⟩⟩,
    projectiveCards,
    ⟨projectiveCards.1.trans axisOrbits.1.symm,
      projectiveCards.2.1.trans axisOrbits.2.1.symm,
      projectiveCards.2.2.trans axisOrbits.2.2.1.symm⟩,
    axisOrbits, icosahedral_axis_stabilizer_orders⟩

#print axioms finite_icosahedral_axis_decomposition_with_normalizers

-- Each source clause is independently extractable from the deposited statement.
example :
    projectiveAxisPointSet .fivefold ∪ projectiveAxisPointSet .threefold ∪
        projectiveAxisPointSet .twofold = Finset.univ :=
  finite_icosahedral_axis_decomposition_with_normalizers.1.1

example :
    Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .threefold) :=
  finite_icosahedral_axis_decomposition_with_normalizers.1.2.1

example :
    Disjoint (projectiveAxisPointSet .fivefold) (projectiveAxisPointSet .twofold) :=
  finite_icosahedral_axis_decomposition_with_normalizers.1.2.2.1

example :
    Disjoint (projectiveAxisPointSet .threefold) (projectiveAxisPointSet .twofold) :=
  finite_icosahedral_axis_decomposition_with_normalizers.1.2.2.2

example : Function.Bijective fivefoldProjectiveAxisMap :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.1.1

example : Function.Bijective threefoldProjectiveAxisMap :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.1.2.1

example : Function.Bijective twofoldProjectiveAxisMap :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.1.2.2

example : ∀ point : FivefoldProjectivePoints,
    axisFixesProjectivePoint (fivefoldProjectiveAxisMap point) point.1 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.2.1

example : ∀ point : ThreefoldProjectivePoints,
    axisFixesProjectivePoint (threefoldProjectiveAxisMap point) point.1 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.2.2.1

example : ∀ point : TwofoldProjectivePoints,
    axisFixesProjectivePoint (twofoldProjectiveAxisMap point) point.1 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.1.2.2.2

example : Fintype.card FivefoldProjectivePoints = 6 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.1.1

example : Fintype.card ThreefoldProjectivePoints = 10 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.1.2.1

example : Fintype.card TwofoldProjectivePoints = 15 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.1.2.2

example : Fintype.card FivefoldProjectivePoints = Fintype.card FivefoldAxes :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.1.1

example : Fintype.card ThreefoldProjectivePoints = Fintype.card ThreefoldAxes :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.1.2.1

example : Fintype.card TwofoldProjectivePoints = Fintype.card TwofoldAxes :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.1.2.2

example : Fintype.card FivefoldAxes = 6 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.1

example : Fintype.card ThreefoldAxes = 10 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.2.1

example : Fintype.card TwofoldAxes = 15 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.2.2.1

example : ∀ g h : FivefoldAxes, axesAreConjugate 5 g h :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.2.2.2.1

example : ∀ g h : ThreefoldAxes, axesAreConjugate 3 g h :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.2.2.2.2.1

example : ∀ g h : TwofoldAxes, axesAreConjugate 2 g h :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.1.2.2.2.2.2

example : ∀ g : FivefoldAxes, (cyclicAxisNormalizer 5 g).card = 10 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.2.1

example : ∀ g : ThreefoldAxes, (cyclicAxisNormalizer 3 g).card = 6 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.2.2.1

example : ∀ g : TwofoldAxes, (cyclicAxisNormalizer 2 g).card = 4 :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.2.2.2.1

example : ∀ g : TwofoldAxes, cyclicAxisNormalizer 2 g = elementCentralizer g :=
  finite_icosahedral_axis_decomposition_with_normalizers.2.2.2.2.2.2.2.2

-- The concrete projective carrier is inhabited independently of the theorem.
example : FiniteProjectivePlane := .inr (.inr ())

end D5.S3.Arith.IcosahedralAxisNormalizerDecomposition
