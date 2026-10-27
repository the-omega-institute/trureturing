/- GID: D5/S3/Geometry/FiniteConeUnionWedge
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteConeUnionWedge
   mirror-E: none(waiver:finite-cone-union-wedge)
   anchors: [D5/S3/Geometry/FiniteConeCollapse, mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Actual finite realizations meeting in a nonempty cone are homotopy equivalent to their quotient wedge. -/
import D5.S3.Geometry.FiniteConeCollapse
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Quotient

/-!
# A finite union along a cone

The wedge is the quotient of the disjoint sum identifying precisely the two
chosen points. Closedness, the intersection of realizations, the quotient
homeomorphism, and the descent of the based homotopies are proved here.
The finite cone contractions are those of `FiniteConeCollapse`.

This is the classical topological cone-union lemma used in the single-vertex
substitution route for Carnero Bravo, arXiv:2505.06457v2, Question 22. The graph
substitution, join comparison, induction, and sphere identifications are not
asserted by this lemma.
-/

noncomputable section
open Set Topology
open scoped unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteConeUnionWedge

/-- Equality, together with identification of all points in the given subset. -/
def subsetSetoid {X : Type*} (C : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ C ∧ y ∈ C)
  iseqv := ⟨fun _ => Or.inl rfl,
    by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩,
    by
      rintro x y z (rfl | ⟨hx, hy⟩) hz
      · exact hz
      · rcases hz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩⟩

/-- The subset collapse with its quotient topology. -/
abbrev Collapse {X : Type*} (C : Set X) := Quotient (subsetSetoid C)

private def collapseMap {X : Type*} [TopologicalSpace X] (C : Set X) : C(X, Collapse C) :=
  ⟨Quotient.mk (subsetSetoid C), continuous_quotient_mk'⟩

private theorem collapse_eq {X : Type*} (C : Set X) (x y : X) :
    Quotient.mk (subsetSetoid C) x = Quotient.mk (subsetSetoid C) y ↔
      x = y ∨ (x ∈ C ∧ y ∈ C) := Quotient.eq

private theorem collapse_eq_base {X : Type*} (C : Set X) {c : X} (hc : c ∈ C) (x : X) :
    Quotient.mk (subsetSetoid C) x = Quotient.mk (subsetSetoid C) c ↔ x ∈ C := by
  rw [collapse_eq]
  constructor
  · rintro (rfl | h)
    · exact hc
    · exact h.1
  · exact fun hx => Or.inr ⟨hx, hc⟩

/-- Exactly the two distinguished points of the disjoint sum. -/
def wedgePoints {X Y : Type*} (a : X) (b : Y) : Set (X ⊕ Y) :=
  {z | z = Sum.inl a ∨ z = Sum.inr b}

/-- The actual quotient wedge, with the quotient topology. -/
abbrev Wedge {X Y : Type*} (a : X) (b : Y) := Collapse (wedgePoints a b)

private theorem wedge_respects {X Y X' Y' : Type*}
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (f : X → X') (g : Y → Y') (hf : f a = a') (hg : g b = b') :
    ∀ z w, (subsetSetoid (wedgePoints a b)).r z w →
      (subsetSetoid (wedgePoints a' b')).r (Sum.map f g z) (Sum.map f g w) := by
  rintro z w (rfl | ⟨hz, hw⟩)
  · exact Or.inl rfl
  · apply Or.inr
    constructor
    · rcases hz with rfl | rfl <;> simp [wedgePoints, hf, hg]
    · rcases hw with rfl | rfl <;> simp [wedgePoints, hf, hg]

private def wedgeLift {X Y X' Y' : Type*}
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (f : X → X') (g : Y → Y') (hf : f a = a') (hg : g b = b') :
    Wedge a b → Wedge a' b' :=
  Quotient.map (Sum.map f g) (wedge_respects f g hf hg)

private def wedgeMap {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (f : C(X, X')) (g : C(Y, Y')) (hf : f a = a') (hg : g b = b') :
    C(Wedge a b, Wedge a' b') :=
  ⟨wedgeLift f g hf hg, (f.continuous.sumMap g.continuous).quotient_map' _⟩

private def wedgeInverseHomotopy {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (f : C(X, X')) (g : C(Y, Y')) (f' : C(X', X)) (g' : C(Y', Y))
    (hf : f a = a') (hg : g b = b') (hf' : f' a' = a) (hg' : g' b' = b)
    (H : (ContinuousMap.id X).HomotopyRel (f'.comp f) {a})
    (K : (ContinuousMap.id Y).HomotopyRel (g'.comp g) {b}) :
    (ContinuousMap.id (Wedge a b)).Homotopy
      ((wedgeMap f' g' hf' hg').comp (wedgeMap f g hf hg)) where
  toFun z := wedgeLift (fun x => H (z.1, x)) (fun y => K (z.1, y))
    (H.eq_fst z.1 (by simp)) (K.eq_fst z.1 (by simp)) z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    let q := collapseMap (wedgePoints a b)
    have h : Continuous (Sum.elim
        (fun z : I × X => q (Sum.inl (H z)))
        (fun z : I × Y => q (Sum.inr (K z)))) :=
      (q.continuous.comp (continuous_inl.comp H.continuous)).sumElim
        (q.continuous.comp (continuous_inr.comp K.continuous))
    convert h.comp (Homeomorph.prodSumDistrib I X Y).continuous using 1
    funext z
    rcases z with ⟨t, x | y⟩ <;> rfl
  map_zero_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> simp [wedgeLift, H.apply_zero, K.apply_zero]
  map_one_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> simp [wedgeMap, wedgeLift, H.apply_one, K.apply_one]

private def wedgeEquiv {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (f : C(X, X')) (g : C(Y, Y')) (f' : C(X', X)) (g' : C(Y', Y))
    (hf : f a = a') (hg : g b = b') (hf' : f' a' = a) (hg' : g' b' = b)
    (H : (ContinuousMap.id X).HomotopyRel (f'.comp f) {a})
    (K : (ContinuousMap.id Y).HomotopyRel (g'.comp g) {b})
    (H' : (ContinuousMap.id X').HomotopyRel (f.comp f') {a'})
    (K' : (ContinuousMap.id Y').HomotopyRel (g.comp g') {b'}) :
    Wedge a b ≃ₕ Wedge a' b' where
  toFun := wedgeMap f g hf hg
  invFun := wedgeMap f' g' hf' hg'
  left_inv := ⟨(wedgeInverseHomotopy f g f' g' hf hg hf' hg' H K).symm⟩
  right_inv := ⟨(wedgeInverseHomotopy f' g' f g hf' hg' hf hg H' K').symm⟩

section Cover

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Closed embedded summands covering a space, whose overlap lies in the collapse subset.
The subset may be the whole space or either summand. -/
structure CollapseCover (a : X) (b : Y) (C : Set Z) where
  left : C(X, Z)
  right : C(Y, Z)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  left_closed : IsClosedMap left
  right_closed : IsClosedMap right
  covers : Function.Surjective (Sum.elim left right)
  overlap : ∀ x y, left x = right y → left x ∈ C
  left_base : left a ∈ C
  right_base : right b ∈ C

namespace CollapseCover

variable {a : X} {b : Y} {C : Set Z} (P : CollapseCover a b C)

private def leftQuotient : C(Collapse (P.left ⁻¹' C), Collapse C) where
  toFun := Quotient.lift (fun x => Quotient.mk (subsetSetoid C) (P.left x)) (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact Quotient.sound (Or.inr ⟨hx, hy⟩))
  continuous_toFun := (continuous_quotient_mk'.comp P.left.continuous).quotient_lift _

private def rightQuotient : C(Collapse (P.right ⁻¹' C), Collapse C) where
  toFun := Quotient.lift (fun y => Quotient.mk (subsetSetoid C) (P.right y)) (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact Quotient.sound (Or.inr ⟨hx, hy⟩))
  continuous_toFun := (continuous_quotient_mk'.comp P.right.continuous).quotient_lift _

private def quotientSum : C(Collapse (P.left ⁻¹' C) ⊕ Collapse (P.right ⁻¹' C), Collapse C) :=
  ⟨Sum.elim P.leftQuotient P.rightQuotient,
    P.leftQuotient.continuous.sumElim P.rightQuotient.continuous⟩

private theorem quotientSum_isQuotientMap : IsQuotientMap P.quotientSum := by
  let p : X ⊕ Y → Z := Sum.elim P.left P.right
  have hp : IsQuotientMap p :=
    (P.left_closed.sumElim P.right_closed).isQuotientMap
      (P.left.continuous.sumElim P.right.continuous) P.covers
  let s : X ⊕ Y → Collapse (P.left ⁻¹' C) ⊕ Collapse (P.right ⁻¹' C) :=
    Sum.map (Quotient.mk (subsetSetoid (P.left ⁻¹' C)))
      (Quotient.mk (subsetSetoid (P.right ⁻¹' C)))
  have hs : Continuous s := continuous_quotient_mk'.sumMap continuous_quotient_mk'
  apply IsQuotientMap.of_comp hs P.quotientSum.continuous
  have he : P.quotientSum ∘ s = Quotient.mk (subsetSetoid C) ∘ p := by
    funext z
    cases z <;> rfl
  rw [he]
  exact isQuotientMap_quotient_mk'.comp hp

private theorem left_kernel (x x' : X) :
    Quotient.mk (subsetSetoid C) (P.left x) = Quotient.mk (subsetSetoid C) (P.left x') ↔
      Quotient.mk (subsetSetoid (P.left ⁻¹' C)) x =
        Quotient.mk (subsetSetoid (P.left ⁻¹' C)) x' := by
  simp only [collapse_eq, Set.mem_preimage, P.left_injective.eq_iff]

private theorem right_kernel (y y' : Y) :
    Quotient.mk (subsetSetoid C) (P.right y) = Quotient.mk (subsetSetoid C) (P.right y') ↔
      Quotient.mk (subsetSetoid (P.right ⁻¹' C)) y =
        Quotient.mk (subsetSetoid (P.right ⁻¹' C)) y' := by
  simp only [collapse_eq, Set.mem_preimage, P.right_injective.eq_iff]

private theorem cross_kernel (x : X) (y : Y) :
    Quotient.mk (subsetSetoid C) (P.left x) = Quotient.mk (subsetSetoid C) (P.right y) ↔
      P.left x ∈ C ∧ P.right y ∈ C := by
  rw [collapse_eq]
  constructor
  · rintro (h | h)
    · exact ⟨P.overlap x y h, h ▸ P.overlap x y h⟩
    · exact h
  · exact Or.inr

private theorem wedge_kernel : ∀ z w,
    (subsetSetoid (wedgePoints
      (Quotient.mk (subsetSetoid (P.left ⁻¹' C)) a)
      (Quotient.mk (subsetSetoid (P.right ⁻¹' C)) b))).r z w ↔
        P.quotientSum z = P.quotientSum w := by
  intro z w
  rcases z with z | z <;> rcases w with w | w
  all_goals
    induction z using Quotient.inductionOn with
    | h z =>
      induction w using Quotient.inductionOn with
      | h w =>
        change (_ = _ ∨ (_ ∧ _)) ↔ _
        simp only [wedgePoints, Set.mem_setOf_eq, Sum.inl.injEq, Sum.inr.injEq,
          Sum.inl_ne_inr, Sum.inr_ne_inl, or_false, false_or]
  · change (_ = _ ∨ (_ ∧ _)) ↔ _
    rw [P.left_kernel]
    constructor
    · rintro (h | ⟨hz, hw⟩)
      · exact h
      · exact hz.trans hw.symm
    · exact Or.inl
  · rw [P.cross_kernel]
    simp only [collapse_eq_base _ P.left_base, collapse_eq_base _ P.right_base,
      Set.mem_preimage]
  · rw [eq_comm, P.cross_kernel]
    simp only [collapse_eq_base _ P.left_base, collapse_eq_base _ P.right_base,
      Set.mem_preimage, and_comm]
  · change (_ = _ ∨ (_ ∧ _)) ↔ _
    rw [P.right_kernel]
    constructor
    · rintro (h | ⟨hz, hw⟩)
      · exact h
      · exact hz.trans hw.symm
    · exact Or.inl

/-- The actual collapse is homeomorphic to the wedge of the two actual summand collapses. -/
def quotientWedgeHomeomorph :
    Wedge (Quotient.mk (subsetSetoid (P.left ⁻¹' C)) a)
      (Quotient.mk (subsetSetoid (P.right ⁻¹' C)) b) ≃ₜ Collapse C :=
  (Homeomorph.Quotient.congrRight P.wedge_kernel).trans
    (Topology.IsQuotientMap.homeomorph (f := P.quotientSum) P.quotientSum_isQuotientMap)

end CollapseCover
end Cover

open FiniteConeCollapse
open scoped BigOperators

section FiniteRealizations

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem realization_mono {M N : PreAbstractSimplicialComplex V} (h : M ≤ N) :
    realization M ⊆ realization N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, h hs, hx⟩

private theorem realization_union (M N : PreAbstractSimplicialComplex V) :
    realization (M ⊔ N) = realization M ∪ realization N := by
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩

/-- Realization preserves the actual intersection of downward-closed finite complexes.
The common face is nonempty because the coordinate sum is one. -/
theorem realization_intersection (M N : PreAbstractSimplicialComplex V) :
    realization (M ⊓ N) = realization M ∩ realization N := by
  apply le_antisymm
  · exact fun x hx => ⟨realization_mono inf_le_left hx, realization_mono inf_le_right hx⟩
  · rintro x ⟨⟨s, hs, hx⟩, ⟨t, ht, hy⟩⟩
    rw [← faceSimplex_eq_convexHull] at hx hy
    have hn : (s ∩ t).Nonempty := by
      obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (show (∑ v, x v) ≠ 0 by rw [hx.2.1]; norm_num)
      refine ⟨v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · by_contra h
        exact hv (hx.2.2 v h)
      · by_contra h
        exact hv (hy.2.2 v h)
    refine ⟨s ∩ t, ⟨(M.isRelLowerSet_faces hs).2 Finset.inter_subset_left hn,
      (N.isRelLowerSet_faces ht).2 Finset.inter_subset_right hn⟩, ?_⟩
    rw [← faceSimplex_eq_convexHull]
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro v hv
    by_cases hs : v ∈ s
    · exact hy.2.2 v (fun ht => hv (Finset.mem_inter.mpr ⟨hs, ht⟩))
    · exact hx.2.2 v hs

private theorem realization_closed (M : PreAbstractSimplicialComplex V) :
    IsClosed (realization M) := by
  have he : realization M = ⋃ s : {s : Finset V // s ∈ M},
      convexHull ℝ ((fun v : V => Pi.single v (1 : ℝ)) '' (s.val : Set V)) := by
    ext x
    simp only [realization, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨⟨s, hs⟩, hx⟩
    · rintro ⟨⟨s, hs⟩, hx⟩
      exact ⟨s, hs, hx⟩
  rw [he]
  apply isClosed_iUnion_of_finite
  intro s
  exact (s.val.finite_toSet.image (fun v : V => Pi.single v (1 : ℝ))).isClosed_convexHull ℝ

/-- Finite face data for two complexes meeting in a specified nonempty cone. -/
structure ConeUnion (V : Type*) [Fintype V] [DecidableEq V] where
  left : PreAbstractSimplicialComplex V
  right : PreAbstractSimplicialComplex V
  cone : PreAbstractSimplicialComplex V
  intersection : left ⊓ right = cone
  apex : V
  apex_face : ({apex} : Finset V) ∈ cone
  cone_face : ∀ s ∈ cone, insert apex s ∈ cone

namespace ConeUnion

variable (P : ConeUnion V)

private theorem cone_le_left : P.cone ≤ P.left := by
  rw [← P.intersection]
  exact inf_le_left

private theorem cone_le_right : P.cone ≤ P.right := by
  rw [← P.intersection]
  exact inf_le_right

/-- The cone pair in the left native coordinate realization. -/
def leftPair : ConePair V :=
  ⟨P.left, P.cone, P.cone_le_left, P.apex, P.apex_face, P.cone_face⟩

/-- The cone pair in the right native coordinate realization. -/
def rightPair : ConePair V :=
  ⟨P.right, P.cone, P.cone_le_right, P.apex, P.apex_face, P.cone_face⟩

/-- The same actual cone inside the union complex. -/
def unionPair : ConePair V :=
  ⟨P.left ⊔ P.right, P.cone, P.cone_le_left.trans le_sup_left,
    P.apex, P.apex_face, P.cone_face⟩

private def leftInclusion : C(P.leftPair.Space, P.unionPair.Space) :=
  ⟨fun x => ⟨x.val, realization_mono le_sup_left x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def rightInclusion : C(P.rightPair.Space, P.unionPair.Space) :=
  ⟨fun x => ⟨x.val, realization_mono le_sup_right x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def closedCover :
    CollapseCover P.leftPair.apexPoint P.rightPair.apexPoint P.unionPair.coneSet where
  left := P.leftInclusion
  right := P.rightInclusion
  left_injective := by
    intro x y h
    exact Subtype.ext (congrArg Subtype.val h)
  right_injective := by
    intro x y h
    exact Subtype.ext (congrArg Subtype.val h)
  left_closed := (realization_closed P.left).isClosedMap_subtype_val.subtype_mk _
  right_closed := (realization_closed P.right).isClosedMap_subtype_val.subtype_mk _
  covers := by
    intro z
    have hz : z.val ∈ realization P.left ∪ realization P.right :=
      (realization_union P.left P.right) ▸ z.property
    rcases hz with hz | hz
    · exact ⟨Sum.inl ⟨z.val, hz⟩, Subtype.ext rfl⟩
    · exact ⟨Sum.inr ⟨z.val, hz⟩, Subtype.ext rfl⟩
  overlap := by
    intro x y h
    change x.val ∈ realization P.cone
    rw [← P.intersection, realization_intersection]
    exact ⟨x.property, (congrArg Subtype.val h).symm ▸ y.property⟩
  left_base := by
    change Pi.single P.apex (1 : ℝ) ∈ realization P.cone
    exact ⟨{P.apex}, P.apex_face, subset_convexHull ℝ _ ⟨P.apex, by simp, rfl⟩⟩
  right_base := by
    change Pi.single P.apex (1 : ℝ) ∈ realization P.cone
    exact ⟨{P.apex}, P.apex_face, subset_convexHull ℝ _ ⟨P.apex, by simp, rfl⟩⟩

private def collapseIdentification (Q : ConePair V) :
    Q.Collapse ≃ₜ Collapse Q.coneSet :=
  Homeomorph.Quotient.congrRight (fun _ _ => Iff.rfl)

private def quotientHomeomorph :
    Wedge (P.leftPair.quotientMap P.leftPair.apexPoint)
      (P.rightPair.quotientMap P.rightPair.apexPoint) ≃ₜ P.unionPair.Collapse := by
  exact P.closedCover.quotientWedgeHomeomorph.trans (collapseIdentification P.unionPair).symm

private def localWedgeEquiv :
    Wedge P.leftPair.apexPoint P.rightPair.apexPoint ≃ₕ
      Wedge (P.leftPair.quotientMap P.leftPair.apexPoint)
        (P.rightPair.quotientMap P.rightPair.apexPoint) :=
  wedgeEquiv P.leftPair.quotientMap P.rightPair.quotientMap
    P.leftPair.collapseInverse P.rightPair.collapseInverse rfl rfl
    (P.leftPair.basedCollapse.1.fst_eq_snd (by simp)).symm
    (P.rightPair.basedCollapse.1.fst_eq_snd (by simp)).symm
    P.leftPair.basedCollapse.1 P.rightPair.basedCollapse.1
    P.leftPair.basedCollapse.2 P.rightPair.basedCollapse.2

/-- The actual coordinate union is homotopy equivalent to the actual quotient wedge
of the two native coordinate realizations, based at the common cone apex.
No properness of the cone or positive-dimensional face is required. -/
def homotopyEquiv :
    ↥(realization (P.left ⊔ P.right)) ≃ₕ
      Wedge P.leftPair.apexPoint P.rightPair.apexPoint :=
  (P.unionPair.collapseEquiv.trans P.quotientHomeomorph.symm.toHomotopyEquiv).trans
    P.localWedgeEquiv.symm

end ConeUnion
end FiniteRealizations

end D5.S3.Geometry.FiniteConeUnionWedge
