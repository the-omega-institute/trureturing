/- GID: D5/S3/Geometry/FiniteComponentClosure/ConeSplits
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/ConeSplits
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Explicit cone-cover and disjoint-join quotient decompositions. -/
import D5.S3.Geometry.FiniteComponentClosure.Models

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  D5.S3.Geometry.FiniteComponentClosure.joinHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.TopologicalCone
  D5.S3.Geometry.FiniteComponentClosure.coneHeight
  D5.S3.Geometry.FiniteComponentClosure.coneBaseSuspensionHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.singleton_coordinates
  from D5.S3.Geometry.FiniteComponentClosure.Transport

open private
  D5.S3.Geometry.FiniteComponentClosure.vertexComplex
  from D5.S3.Geometry.FiniteComponentClosure.Models

section ConeCovers

private def wedgeSubsingletonHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton Y] (a : X) (b : Y) :
    FiniteConeUnionWedge.Wedge a b ≃ₜ X := by
  let f : X ⊕ Y → X := Sum.elim id (fun _ => a)
  have hc : Continuous f := continuous_id.sumElim continuous_const
  have hq : IsQuotientMap f := IsQuotientMap.of_inverse continuous_inl hc (fun _ => rfl)
  refine (Homeomorph.Quotient.congrRight (r' := Setoid.ker f) ?_).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨f, hc⟩) hq)
  intro z w
  change (z = w ∨
    ((z = Sum.inl a ∨ z = Sum.inr b) ∧ (w = Sum.inl a ∨ w = Sum.inr b))) ↔ f z = f w
  rcases z with x | y <;> rcases w with x' | y'
  · simp [f]
    intro hx hx'
    exact hx.trans hx'.symm
  · have hy : y' = b := Subsingleton.elim _ _
    simp [f, hy]
  · have hy : y = b := Subsingleton.elim _ _
    simp [f, hy, eq_comm]
  · have hy : y = y' := Subsingleton.elim _ _
    simp [f, hy]

private def wedgeHomeomorph {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (a : X) (b : Y) (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    FiniteConeUnionWedge.Wedge a b ≃ₜ FiniteConeUnionWedge.Wedge (e a) (d b) := by
  apply Homeomorph.Quotient.congr (e.sumCongr d)
  intro x y
  have h (w : X ⊕ Y) :
      (e.sumCongr d) w ∈ FiniteConeUnionWedge.wedgePoints (e a) (d b) ↔
        w ∈ FiniteConeUnionWedge.wedgePoints a b := by
    cases w <;> simp [FiniteConeUnionWedge.wedgePoints, Homeomorph.sumCongr,
      e.injective.eq_iff, d.injective.eq_iff]
  change (x = y ∨ (_ ∧ _)) ↔ (_ = _ ∨ (_ ∧ _))
  rw [(e.sumCongr d).injective.eq_iff, h x, h y]

private def coverCollapseRightHomeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {a : X} {b : Y} {C : Set Z}
    (P : FiniteConeUnionWedge.CollapseCover a b C)
    (hY : ∀ y, P.right y ∈ C) :
    FiniteConeUnionWedge.Collapse C ≃ₜ
      FiniteConeUnionWedge.Collapse (P.left ⁻¹' C) := by
  letI : Subsingleton (FiniteConeUnionWedge.Collapse (P.right ⁻¹' C)) :=
    ⟨fun x y => Quotient.inductionOn₂ x y
      (fun x y => Quotient.sound (Or.inr ⟨hY x, hY y⟩))⟩
  exact P.quotientWedgeHomeomorph.symm.trans
    (wedgeSubsingletonHomeomorph (Quotient.mk _ a) (Quotient.mk _ b))

variable {V : Type*} [Fintype V] [DecidableEq V]

private def finiteConeCover (X Y C : PreAbstractSimplicialComplex V)
    (a b : V) (ha : ({a} : Finset V) ∈ X) (hb : ({b} : Finset V) ∈ Y)
    (haC : ({a} : Finset V) ∈ C) (hbC : ({b} : Finset V) ∈ C)
    (hXY : X ⊓ Y ≤ C) :
    FiniteConeUnionWedge.CollapseCover
      (FiniteVertexCylinder.vertexPoint X a ha) (FiniteVertexCylinder.vertexPoint Y b hb)
      {z : FiniteSimplicialJoin.Space (X ⊔ Y) | z.val ∈ FiniteConeCollapse.realization C} where
  left := FiniteConeUnionWedge.realizationInclusion le_sup_left
  right := FiniteConeUnionWedge.realizationInclusion le_sup_right
  left_injective := fun x y h => Subtype.ext
    (congrArg (fun z : FiniteSimplicialJoin.Space (X ⊔ Y) => z.val) h)
  right_injective := fun x y h => Subtype.ext
    (congrArg (fun z : FiniteSimplicialJoin.Space (X ⊔ Y) => z.val) h)
  left_closed := by
    letI := FiniteSimplicialJoin.realizationCompactSpace X
    exact (FiniteConeUnionWedge.realizationInclusion
      (show X ≤ X ⊔ Y from le_sup_left)).continuous.isClosedMap
  right_closed := by
    letI := FiniteSimplicialJoin.realizationCompactSpace Y
    exact (FiniteConeUnionWedge.realizationInclusion
      (show Y ≤ X ⊔ Y from le_sup_right)).continuous.isClosedMap
  covers := by
    intro z
    obtain ⟨s, hs, hz⟩ := z.property
    rcases hs with hs | hs
    · exact ⟨Sum.inl ⟨z.val, s, hs, hz⟩, Subtype.ext rfl⟩
    · exact ⟨Sum.inr ⟨z.val, s, hs, hz⟩, Subtype.ext rfl⟩
  overlap := by
    intro x y h
    have hy : x.val ∈ FiniteConeCollapse.realization Y :=
      (congrArg Subtype.val h).symm ▸ y.property
    obtain ⟨s, hs, hx⟩ := (Set.ext_iff.mp
      (FiniteConeUnionWedge.realization_intersection X Y) x.val).mpr ⟨x.property, hy⟩
    exact ⟨s, hXY hs, hx⟩
  left_base := (FiniteVertexCylinder.vertexPoint C a haC).property
  right_base := (FiniteVertexCylinder.vertexPoint C b hbC).property

private def coneCoverEquiv (X Y C : PreAbstractSimplicialComplex V)
    (a b : V) (ha : ({a} : Finset V) ∈ X) (hb : ({b} : Finset V) ∈ Y)
    (haC : ({a} : Finset V) ∈ C) (hbC : ({b} : Finset V) ∈ C)
    (hC : C ≤ X ⊔ Y) (hXY : X ⊓ Y ≤ C)
    (hcone : ∀ s ∈ C, insert a s ∈ C) :
    let P := finiteConeCover X Y C a b ha hb haC hbC hXY
    FiniteSimplicialJoin.Space (X ⊔ Y) ≃ₕ
      FiniteConeUnionWedge.Wedge
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (P.left ⁻¹'
          {z | z.val ∈ FiniteConeCollapse.realization C}))
          (FiniteVertexCylinder.vertexPoint X a ha))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (P.right ⁻¹'
          {z | z.val ∈ FiniteConeCollapse.realization C}))
          (FiniteVertexCylinder.vertexPoint Y b hb)) := by
  let Q : FiniteConeCollapse.ConePair V :=
    ⟨X ⊔ Y, C, hC, a, haC, hcone⟩
  let P := finiteConeCover X Y C a b ha hb haC hbC hXY
  exact Q.collapseEquiv.trans P.quotientWedgeHomeomorph.symm.toHomotopyEquiv

/-- Collapsing a whole closed summand leaves the other summand modulo their actual intersection.
No contractibility of either summand or of the intersection is used. -/
private def unionCollapseRightHomeomorph (X Y : PreAbstractSimplicialComplex V)
    (a : V) (haX : ({a} : Finset V) ∈ X) (haY : ({a} : Finset V) ∈ Y) :
    FiniteConeUnionWedge.Collapse
      {z : FiniteSimplicialJoin.Space (X ⊔ Y) |
        z.val ∈ FiniteConeCollapse.realization Y} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {x : FiniteSimplicialJoin.Space X |
          x.val ∈ FiniteConeCollapse.realization Y} :=
  coverCollapseRightHomeomorph
    (finiteConeCover X Y Y a a haX haY haY haY inf_le_right)
    (fun y => y.property)

end ConeCovers

section DisjointJoin

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private theorem join_left_vertex (M : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (a : V) (ha : ({a} : Finset V) ∈ M) :
    ({Sum.inl a} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin M Z := by
  have hl : ({Sum.inl a} : Finset (V ⊕ W)).toLeft = {a} := by ext v; simp
  have hr : ({Sum.inl a} : Finset (V ⊕ W)).toRight = ∅ := by ext v; simp
  exact ⟨by simp, Or.inr (hl.symm ▸ ha), Or.inl hr⟩

private theorem join_right_vertex (M : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (b : W) (hb : ({b} : Finset W) ∈ Z) :
    ({Sum.inr b} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin M Z := by
  have hl : ({Sum.inr b} : Finset (V ⊕ W)).toLeft = ∅ := by ext v; simp
  have hr : ({Sum.inr b} : Finset (V ⊕ W)).toRight = {b} := by ext v; simp
  exact ⟨by simp, Or.inl hl, Or.inr (hr.symm ▸ hb)⟩

private theorem join_mono_left {M N : PreAbstractSimplicialComplex V}
    (h : M ≤ N) (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin M Z ≤ FiniteSimplicialJoin.simplicialJoin N Z := by
  rintro s ⟨hs, hl, hr⟩
  exact ⟨hs, hl.imp id (fun hm => h hm), hr⟩

private theorem vertexComplex_le (M : PreAbstractSimplicialComplex V)
    (a : V) (ha : ({a} : Finset V) ∈ M) : vertexComplex a ≤ M := by
  rintro s rfl
  exact ha

private theorem join_union (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z =
      FiniteSimplicialJoin.simplicialJoin M Z ⊔ FiniteSimplicialJoin.simplicialJoin N Z := by
  apply SetLike.ext
  intro s
  change (s.Nonempty ∧ (s.toLeft = ∅ ∨ (s.toLeft ∈ M ∨ s.toLeft ∈ N)) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ↔
    ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∨
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z)))
  tauto

private theorem disjoint_join_overlap (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (hMN : M ⊓ N = ⊥) :
    FiniteSimplicialJoin.simplicialJoin M Z ⊓ FiniteSimplicialJoin.simplicialJoin N Z =
      FiniteSimplicialJoin.simplicialJoin ⊥ Z := by
  apply SetLike.ext
  intro s
  have hno : ¬(s.toLeft ∈ M ∧ s.toLeft ∈ N) := by
    intro h
    have hb : s.toLeft ∈ (⊥ : PreAbstractSimplicialComplex V) := hMN ▸ h
    exact hb
  change ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∧
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z))) ↔
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ False) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z))
  tauto

private theorem join_vertex_cone (Z : PreAbstractSimplicialComplex W) (a : V) :
    ∀ s ∈ FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z,
      insert (Sum.inl a) s ∈ FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z := by
  rintro s ⟨_, hl, hr⟩
  refine ⟨Finset.insert_nonempty _ _, Or.inr ?_, ?_⟩
  · change (insert (Sum.inl a) s).toLeft = {a}
    rw [Finset.toLeft_insert_inl]
    rcases hl with hl | hl
    · rw [hl]; simp
    · change s.toLeft = {a} at hl
      rw [hl]; simp
  · simpa only [Finset.toRight_insert_inl] using hr

private theorem vertexSpace_eq (a : V) (x : FiniteSimplicialJoin.Space (vertexComplex a)) :
    x.val = Pi.single a 1 := by
  obtain ⟨s, hs, hx⟩ := x.property
  change s = {a} at hs
  rw [hs, ← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  exact singleton_coordinates a hx

private def vertexSpaceHomeomorph (a : V) :
    FiniteSimplicialJoin.Space (vertexComplex a) ≃ₜ Unit where
  toFun _ := ()
  invFun _ := FiniteVertexCylinder.vertexPoint (vertexComplex a) a rfl
  left_inv x := Subtype.ext (vertexSpace_eq a x).symm
  right_inv _ := rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

private def nativeConeHomeomorph (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z) ≃ₜ
      TopologicalCone (FiniteSimplicialJoin.Space Z) :=
  (FiniteSimplicialJoin.joinHomeomorph (vertexComplex a) Z
    ⟨FiniteVertexCylinder.vertexPoint _ a rfl⟩ ⟨z⟩).symm.trans
    (joinHomeomorph (vertexSpaceHomeomorph a) (Homeomorph.refl _))

private theorem join_base_mem (Z : PreAbstractSimplicialComplex W)
    (z : FiniteSimplicialJoin.Space Z) :
    (Sum.elim (fun _ : V => (0 : ℝ)) z.val) ∈
      FiniteConeCollapse.realization
        (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z) := by
  obtain ⟨s, hs, hz⟩ := z.property
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hz
  refine ⟨(∅ : Finset V).disjSum s, ?_, ?_⟩
  · refine ⟨?_, Or.inl Finset.toLeft_disjSum,
      Or.inr (by simpa only [Finset.toRight_disjSum] using hs)⟩
    obtain ⟨w, hw⟩ := (Z.isRelLowerSet_faces hs).1
    exact ⟨Sum.inr w, by simpa using hw⟩
  · rw [← FiniteConeCollapse.faceSimplex_eq_convexHull]
    refine ⟨?_, ?_, ?_⟩
    · intro v; cases v with
      | inl v => exact le_refl 0
      | inr w => exact hz.1 w
    · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const_zero, zero_add] using hz.2.1
    · intro v hv
      cases v with
      | inl v => rfl
      | inr w => exact hz.2.2 w (by simpa using hv)

private theorem nativeCone_base (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z)
    (x : FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)) :
    x.val ∈ FiniteConeCollapse.realization
      (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z) ↔
      coneHeight (nativeConeHomeomorph Z a z x) = 1 := by
  let e := FiniteSimplicialJoin.joinHomeomorph (vertexComplex a) Z
    ⟨FiniteVertexCylinder.vertexPoint _ a rfl⟩ ⟨z⟩
  obtain ⟨p, rfl⟩ := e.surjective x
  induction p using Quotient.inductionOn with
  | h p =>
    have hr : coneHeight (nativeConeHomeomorph Z a z (e (Quotient.mk _ p))) = p.2.2 := by
      change coneHeight ((joinHomeomorph (vertexSpaceHomeomorph a) (Homeomorph.refl _))
        (e.symm (e (Quotient.mk _ p)))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hr]
    change FiniteSimplicialJoin.representative (vertexComplex a) Z p ∈ _ ↔ _
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
      have hl : s.toLeft = ∅ := hs.2.1.resolve_right (fun h => h)
      have hn : Sum.inl a ∉ s := by
        simpa only [Finset.mem_toLeft] using
          (show a ∉ s.toLeft by rw [hl]; simp)
      have hcoord := hx.2.2 (Sum.inl a) hn
      have hpa : p.1.val a = 1 := by rw [vertexSpace_eq a p.1]; simp
      change (1 - (p.2.2 : ℝ)) * p.1.val a = 0 at hcoord
      apply Subtype.ext
      change (p.2.2 : ℝ) = 1
      rw [hpa] at hcoord
      linarith
    · intro ht
      have he : FiniteSimplicialJoin.representative (vertexComplex a) Z p =
          Sum.elim (fun _ : V => (0 : ℝ)) p.2.1.val := by
        ext v; cases v <;> simp [FiniteSimplicialJoin.representative, ht]
      rw [he]
      exact join_base_mem Z p.2.1

private def nativeConeBaseHomeomorph (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z) :
    FiniteConeUnionWedge.Collapse
      {x : FiniteSimplicialJoin.Space
        (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z) |
        x.val ∈ FiniteConeCollapse.realization
          (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} ≃ₜ
      FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool :=
  (Homeomorph.Quotient.congr (nativeConeHomeomorph Z a z) (by
    intro x y
    change (x = y ∨ (_ ∧ _)) ↔ (_ = _ ∨ (_ ∧ _))
    simp only [Set.mem_setOf_eq]
    rw [(nativeConeHomeomorph Z a z).injective.eq_iff,
      nativeCone_base Z a z x, nativeCone_base Z a z y])).trans
    coneBaseSuspensionHomeomorph

private theorem realization_pullback_intersection
    (X Y D : PreAbstractSimplicialComplex (V ⊕ W)) (h : X ⊓ Y = D) :
    {x : FiniteSimplicialJoin.Space X | x.val ∈ FiniteConeCollapse.realization Y} =
      {x : FiniteSimplicialJoin.Space X | x.val ∈ FiniteConeCollapse.realization D} := by
  ext x
  rw [← h, FiniteConeUnionWedge.realization_intersection]
  exact ⟨fun hy => ⟨x.property, hy⟩, fun hxy => hxy.2⟩

/-- The auxiliary cone quotient is the other join with precisely its base collapsed. -/
private def auxiliaryConeQuotientHomeomorph
    (N : PreAbstractSimplicialComplex V) (Z : PreAbstractSimplicialComplex W)
    (d : V) (hNd : N ⊓ vertexComplex d = ⊥)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    FiniteConeUnionWedge.Collapse
      {z : FiniteSimplicialJoin.Space
          (FiniteSimplicialJoin.simplicialJoin N Z ⊔
            FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z) |
        z.val ∈ FiniteConeCollapse.realization
          (FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z)} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {y : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
          y.val ∈ FiniteConeCollapse.realization
            (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} := by
  refine (unionCollapseRightHomeomorph _ _ (Sum.inr b)
    (join_right_vertex N Z b hb)
    (join_right_vertex (vertexComplex d) Z b hb)).trans ?_
  apply Homeomorph.Quotient.congrRight
  have h := realization_pullback_intersection _ _ _ (disjoint_join_overlap N _ Z hNd)
  intro x y
  rw [h]

/-- The auxiliary space is collapsed along either of two actual cones.
The remaining cone modulo its base is identified by its actual suspension homeomorphism. -/
private def auxiliaryBaseSplit (N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W)
    (d : V) (hNd : N ⊓ vertexComplex d = ⊥)
    (v : V) (hv : ({v} : Finset V) ∈ N)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    Σ y : FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool,
      FiniteConeUnionWedge.Collapse
        {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
          x.val ∈ FiniteConeCollapse.realization
            (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} ≃ₕ
        FiniteConeUnionWedge.Wedge
          (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
            {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
              x.val ∈ FiniteConeCollapse.realization
                (FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z)})
            (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex N Z v hv))) y := by
  let X := FiniteSimplicialJoin.simplicialJoin N Z
  let D := FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z
  let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z
  let B := FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z
  have hCX : C ≤ X := join_mono_left (vertexComplex_le N v hv) Z
  have hXD : X ⊓ D ≤ C := by
    rw [disjoint_join_overlap N (vertexComplex d) Z hNd]
    exact join_mono_left bot_le Z
  have hdv : vertexComplex d ⊓ vertexComplex v = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    have h : s ∈ N ⊓ vertexComplex d :=
      ⟨vertexComplex_le N v hv hs.2, hs.1⟩
    exact hNd ▸ h
  have hDC : D ⊓ C = B := disjoint_join_overlap _ _ Z hdv
  let Q : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨X ⊔ D, D, le_sup_right, Sum.inl d,
      join_left_vertex (vertexComplex d) Z d rfl, join_vertex_cone Z d⟩
  let A := auxiliaryConeQuotientHomeomorph N Z d hNd b hb
  let E : FiniteConeUnionWedge.Collapse
      {x : FiniteSimplicialJoin.Space D | x.val ∈ FiniteConeCollapse.realization C} ≃ₜ
      FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool :=
    (Homeomorph.Quotient.congrRight (by
      intro x y
      have h := realization_pullback_intersection D C B hDC
      change (x = y ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
      rw [h])).trans
      (nativeConeBaseHomeomorph Z d (FiniteVertexCylinder.vertexPoint Z b hb))
  let xa := FiniteVertexCylinder.vertexPoint X (Sum.inl v) (join_left_vertex N Z v hv)
  let yb := FiniteVertexCylinder.vertexPoint D (Sum.inr b)
    (join_right_vertex (vertexComplex d) Z b hb)
  let e := coneCoverEquiv X D C (Sum.inl v) (Sum.inr b)
    (join_left_vertex N Z v hv) (join_right_vertex (vertexComplex d) Z b hb)
    (join_left_vertex (vertexComplex v) Z v rfl)
    (join_right_vertex (vertexComplex v) Z b hb)
    (hCX.trans le_sup_left) hXD (join_vertex_cone Z v)
  refine ⟨E (Quotient.mk _ yb), ?_⟩
  exact (A.symm.toHomotopyEquiv.trans Q.collapseEquiv.symm).trans
    (e.trans (wedgeHomeomorph (Quotient.mk _ xa) (Quotient.mk _ yb)
      (Homeomorph.refl _) E).toHomotopyEquiv)

/-- The first actual two-component split collapses `a*Z`, and retains the right base quotient. -/
private def disjointJoinConeSplit (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (hMN : M ⊓ N = ⊥)
    (a : V) (ha : ({a} : Finset V) ∈ M) (b : W) (hb : ({b} : Finset W) ∈ Z) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z) ≃ₕ
      FiniteConeUnionWedge.Wedge
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
          {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin M Z) |
            x.val ∈ FiniteConeCollapse.realization
              (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)})
          (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex M Z a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
          {y : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
            y.val ∈ FiniteConeCollapse.realization
              (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)})
          (FiniteVertexCylinder.vertexPoint _ _ (join_right_vertex N Z b hb))) := by
  rw [join_union]
  have hCX : FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z ≤
      FiniteSimplicialJoin.simplicialJoin M Z := join_mono_left (vertexComplex_le M a ha) Z
  have hXY : FiniteSimplicialJoin.simplicialJoin M Z ⊓
      FiniteSimplicialJoin.simplicialJoin N Z ≤
      FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z := by
    rw [disjoint_join_overlap M N Z hMN]
    exact join_mono_left bot_le Z
  exact coneCoverEquiv _ _ _ (Sum.inl a) (Sum.inr b)
    (join_left_vertex M Z a ha) (join_right_vertex N Z b hb)
    (join_left_vertex (vertexComplex a) Z a rfl)
    (join_right_vertex (vertexComplex a) Z b hb)
    (hCX.trans le_sup_left) hXY (join_vertex_cone Z a)

private theorem join_intersection (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin M Z ⊓ FiniteSimplicialJoin.simplicialJoin N Z =
      FiniteSimplicialJoin.simplicialJoin (M ⊓ N) Z := by
  apply SetLike.ext
  intro s
  change ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∧
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z))) ↔
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ (s.toLeft ∈ M ∧ s.toLeft ∈ N)) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z))
  tauto

end DisjointJoin

end D5.S3.Geometry.FiniteComponentClosure
