/- GID: D5/S3/Geometry/FiniteConeUnionWedge
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteConeUnionWedge
   mirror-E: none(waiver:finite-cone-union-wedge)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: A finite union along a nonempty cone is equivalent to the actual quotient wedge. -/
import D5.S3.Geometry.FiniteConeCollapse
import D5.S3.Geometry.SingletonRetractionBasedInverse
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.CompactOpen

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

/-- The canonical continuous map to the existing subset collapse. -/
def collapseMap {X : Type*} [TopologicalSpace X] (C : Set X) : C(X, Collapse C) :=
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

/-- The literal collapse of a closed contractible subspace, with inverse
homotopies fixing the chosen point and its quotient class. The geometric input
is a retraction onto the WHOLE bottom-or-subspace cylinder, fixing every point
of that cylinder, and the existing singleton-cylinder data on the subspace.
The forward map is exactly the original `collapseMap`, not an adjusted map.

This is the classical contractible-cofibration quotient argument.
The downstream finite-coordinate supplier in `FiniteSubcomplexCylinder`
constructs `R`; the closed-cover consumer in `FiniteComponentClosure.ConeSplits`
uses it without an `R` or `hR` premise. -/
def contractibleCollapse {X : Type*} [TopologicalSpace X] [T1Space X]
    (C : Set X) (hC : IsClosed C) (a : C) [ContractibleSpace C]
    (R : C(X × I, {z : X × I | z.2 = 0 ∨ z.1 ∈ C}))
    (hR : ∀ z : X × I, (z.2 = 0 ∨ z.1 ∈ C) → (R z).val = z)
    (Ra : SingletonRetractionBasedInverse.CylinderRetraction a) :
    {E : SingletonRetractionBasedInverse.BasedEquivalence
      a.val (collapseMap C a.val) // E.forward = collapseMap C} := by
  classical
  -- Rectify ONLY the contraction of C. No based_inverse is applied to X -> X/C.
  let e : C ≃ₕ Unit := Classical.choice (ContractibleSpace.hequiv_unit C)
  let RU : SingletonRetractionBasedInverse.CylinderRetraction (() : Unit) :=
    { map := ⟨fun z => ⟨z, Or.inr (Subsingleton.elim _ _)⟩,
        continuous_id.subtype_mk _⟩
      fixed := fun _ _ => rfl }
  let γ : Path (e.toFun a) (() : Unit) :=
    (Path.refl ()).cast (Subsingleton.elim _ _) rfl
  let B := Classical.choose (SingletonRetractionBasedInverse.based_inverse
    a () Ra RU e.toFun e.invFun
    (Classical.choice e.left_inv) (Classical.choice e.right_inv) γ)
  have hconst : B.backward.comp B.forward = ContinuousMap.const C a := by
    apply ContinuousMap.ext
    intro x
    change B.backward (B.forward x) = a
    rw [Subsingleton.elim (B.forward x) (), B.backward_point]
  let c : (ContinuousMap.id C).HomotopyRel (ContinuousMap.const C a) {a} :=
    B.left.symm.cast rfl hconst

  -- Actual closed pasting on the supplied target. The bottom and vertical
  -- restrictions meet at c(0,x)=x; no extension or quotient equivalence is assumed.
  let T : Set (X × I) := {z | z.2 = 0 ∨ z.1 ∈ C}
  let k : T → X := fun z =>
    if hx : z.val.1 ∈ C then (c (z.val.2, ⟨z.val.1, hx⟩)).val else z.val.1
  have hk_bottom (z : T) (hz : z.val.2 = 0) : k z = z.val.1 := by
    dsimp only [k]
    split_ifs with hx
    · have hc : c (z.val.2, ⟨z.val.1, hx⟩) = ⟨z.val.1, hx⟩ := by
        rw [hz]
        exact c.apply_zero _
      exact congrArg Subtype.val hc
    · rfl
  have hk_side (z : T) (hz : z.val.1 ∈ C) :
      k z = (c (z.val.2, ⟨z.val.1, hz⟩)).val := by
    dsimp only [k]
    rw [dif_pos hz]
  have hk : Continuous k := by
    let T₀ : Set T := {z | z.val.2 = 0}
    let T₁ : Set T := {z | z.val.1 ∈ C}
    have hT₀ : IsClosed T₀ :=
      isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
    have hT₁ : IsClosed T₁ :=
      hC.preimage (continuous_fst.comp continuous_subtype_val)
    have hk₀ : ContinuousOn k T₀ := by
      apply (continuous_fst.comp continuous_subtype_val).continuousOn.congr
      intro z hz
      exact hk_bottom z hz
    have hk₁ : ContinuousOn k T₁ := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let j : T₁ → I × C := fun z => (z.val.val.2, ⟨z.val.val.1, z.property⟩)
      have hj : Continuous j := by
        exact (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
      have hc : Continuous (fun z : T₁ => (c (j z)).val) :=
        continuous_subtype_val.comp (c.continuous.comp hj)
      apply hc.congr
      intro z
      exact (hk_side z.val z.property).symm
    have hcover : T₀ ∪ T₁ = univ := by
      ext z
      simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
      exact z.property
    rw [← continuousOn_univ, ← hcover]
    exact hk₀.union_of_isClosed hk₁ hT₀ hT₁
  let E : C(I × X, X) :=
    ⟨fun z => k (R (z.2, z.1)), hk.comp (R.continuous.comp continuous_swap)⟩
  have hE₀ (x : X) : E (0, x) = x := by
    have hr : R (x, 0) = ⟨(x, 0), Or.inl rfl⟩ :=
      Subtype.ext (hR (x, 0) (Or.inl rfl))
    change k (R (x, 0)) = x
    rw [hr]
    exact hk_bottom _ rfl
  have hEC (t : I) (x : C) : E (t, x.val) = (c (t, x)).val := by
    have hr : R (x.val, t) = ⟨(x.val, t), Or.inr x.property⟩ :=
      Subtype.ext (hR (x.val, t) (Or.inr x.property))
    change k (R (x.val, t)) = (c (t, x)).val
    rw [hr]
    exact hk_side _ x.property
  have hE₁ (x : C) : E (1, x.val) = a.val :=
    (hEC 1 x).trans (congrArg Subtype.val (c.apply_one x))
  have hEa (t : I) : E (t, a.val) = a.val :=
    (hEC t a).trans (congrArg Subtype.val (c.eq_fst t (by simp)))
  have hEmem (t : I) (x : X) (hx : x ∈ C) : E (t, x) ∈ C := by
    rw [hEC t ⟨x, hx⟩]
    exact (c (t, ⟨x, hx⟩)).property

  -- The endpoint factors through the EXISTING setoid. The inverse is a
  -- continuous Quotient.lift; its continuity is proved from the endpoint map.
  let q := collapseMap C
  have hendpoint (x y : X) (h : (subsetSetoid C).r x y) :
      E (1, x) = E (1, y) := by
    rcases h with rfl | ⟨hx, hy⟩
    · rfl
    · exact (hE₁ ⟨x, hx⟩).trans (hE₁ ⟨y, hy⟩).symm
  let g : C(Collapse C, X) :=
    { toFun := Quotient.lift (fun x => E (1, x)) hendpoint
      continuous_toFun := (E.continuous.comp
        (continuous_const.prodMk continuous_id)).quotient_lift _ }
  have hquot (t : I) (x y : X) (h : (subsetSetoid C).r x y) :
      q (E (t, x)) = q (E (t, y)) := by
    apply Quotient.sound
    rcases h with rfl | ⟨hx, hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hEmem t x hx, hEmem t y hy⟩
  let D : I → Collapse C → Collapse C := fun t =>
    Quotient.lift (fun x => q (E (t, x))) (hquot t)
  have hD : Continuous (fun z : I × Collapse C => D z.1 z.2) := by
    -- Locally compact I is the parameter. No blanket product-quotient claim.
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact q.continuous.comp E.continuous
  let L : (ContinuousMap.id X).HomotopyRel (g.comp q) {a.val} :=
    { toFun := E
      continuous_toFun := E.continuous
      map_zero_left := hE₀
      map_one_left := fun _ => rfl
      prop' := by
        intro t x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        exact hEa t }
  let K : (ContinuousMap.id (Collapse C)).HomotopyRel (q.comp g) {q a.val} :=
    { toFun := fun z => D z.1 z.2
      continuous_toFun := hD
      map_zero_left := by
        intro z
        induction z using Quotient.inductionOn with
        | h x => exact congrArg q (hE₀ x)
      map_one_left := by
        intro z
        induction z using Quotient.inductionOn with
        | h x => rfl
      prop' := by
        intro t z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact congrArg q (hEa t) }
  exact ⟨{
    forward := q
    backward := g
    forward_point := rfl
    backward_point := hE₁ a
    left := L.symm
    right := K.symm }, rfl⟩

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
  Quotient.map' (Sum.map f g) (wedge_respects f g hf hg)

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
    convert h.comp (Homeomorph.prodSumDistrib (X := I) (Y := X) (Z := Y)).continuous using 1
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

/-- Based wedge replacement, using the native quotient maps and their existing homotopies. -/
def basedWedgeEquivalence {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {a : X} {b : Y} {a' : X'} {b' : Y'}
    (E : SingletonRetractionBasedInverse.BasedEquivalence a a')
    (F : SingletonRetractionBasedInverse.BasedEquivalence b b') :
    SingletonRetractionBasedInverse.BasedEquivalence
      (Quotient.mk (subsetSetoid (wedgePoints a b)) (Sum.inl a))
      (Quotient.mk (subsetSetoid (wedgePoints a' b')) (Sum.inl a')) := by
  let H : (ContinuousMap.id (Wedge a b)).HomotopyRel
      ((wedgeMap E.backward F.backward E.backward_point F.backward_point).comp
        (wedgeMap E.forward F.forward E.forward_point F.forward_point))
      {Quotient.mk _ (Sum.inl a)} :=
    { wedgeInverseHomotopy E.forward F.forward E.backward F.backward
        E.forward_point F.forward_point E.backward_point F.backward_point
        E.left.symm F.left.symm with
      prop' := by
        intro t z hz
        have hz' : z = Quotient.mk _ (Sum.inl a) := hz
        subst z
        change Quotient.mk _ (Sum.inl (E.left.symm (t, a))) = Quotient.mk _ (Sum.inl a)
        rw [E.left.symm.eq_fst t (by simp)]
        rfl }
  let K : (ContinuousMap.id (Wedge a' b')).HomotopyRel
      ((wedgeMap E.forward F.forward E.forward_point F.forward_point).comp
        (wedgeMap E.backward F.backward E.backward_point F.backward_point))
      {Quotient.mk _ (Sum.inl a')} :=
    { wedgeInverseHomotopy E.backward F.backward E.forward F.forward
        E.backward_point F.backward_point E.forward_point F.forward_point
        E.right.symm F.right.symm with
      prop' := by
        intro t z hz
        have hz' : z = Quotient.mk _ (Sum.inl a') := hz
        subst z
        change Quotient.mk _ (Sum.inl (E.right.symm (t, a'))) = Quotient.mk _ (Sum.inl a')
        rw [E.right.symm.eq_fst t (by simp)]
        rfl }
  exact {
    forward := wedgeMap E.forward F.forward E.forward_point F.forward_point
    backward := wedgeMap E.backward F.backward E.backward_point F.backward_point
    forward_point := congrArg (fun x => Quotient.mk _ (Sum.inl x)) E.forward_point
    backward_point := congrArg (fun x => Quotient.mk _ (Sum.inl x)) E.backward_point
    left := H.symm
    right := K.symm }

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
    refine Quotient.inductionOn₂ z w ?_
    intro z w
    change (_ = _ ∨ (_ ∧ _)) ↔ _
    simp only [wedgePoints, Set.mem_ofPred_eq, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, or_false, false_or]
  · rename_i z w
    change (_ = _ ∨ (_ ∧ _)) ↔
      Quotient.mk (subsetSetoid C) (P.left z) = Quotient.mk (subsetSetoid C) (P.left w)
    rw [P.left_kernel]
    constructor
    · rintro (h | ⟨hz, hw⟩)
      · exact h
      · exact hz.trans hw.symm
    · exact Or.inl
  · rename_i z w
    change (_ ∧ _) ↔
      Quotient.mk (subsetSetoid C) (P.left z) = Quotient.mk (subsetSetoid C) (P.right w)
    rw [P.cross_kernel]
    exact and_congr (collapse_eq_base (P.left ⁻¹' C) P.left_base z)
      (collapse_eq_base (P.right ⁻¹' C) P.right_base w)
  · rename_i z w
    change (_ ∧ _) ↔
      Quotient.mk (subsetSetoid C) (P.right z) = Quotient.mk (subsetSetoid C) (P.left w)
    conv_rhs => rw [eq_comm]
    rw [P.cross_kernel]
    exact and_comm.trans (and_congr (collapse_eq_base (P.left ⁻¹' C) P.left_base w)
      (collapse_eq_base (P.right ⁻¹' C) P.right_base z))
  · rename_i z w
    change (_ = _ ∨ (_ ∧ _)) ↔
      Quotient.mk (subsetSetoid C) (P.right z) = Quotient.mk (subsetSetoid C) (P.right w)
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

/-- Closedness of the original finite-coordinate realization. -/
theorem realization_closed (M : PreAbstractSimplicialComplex V) :
    IsClosed (realization M) := by
  have he : realization M = ⋃ s : {s : Finset V // s ∈ M},
      convexHull ℝ ((fun v : V => Pi.single v (1 : ℝ)) '' (s.val : Set V)) := by
    ext x
    simp only [realization, Set.mem_ofPred_eq, Set.mem_iUnion]
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
    apply Subtype.ext
    exact congrArg (fun z : P.unionPair.Space => z.val) h
  right_injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : P.unionPair.Space => z.val) h
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

/-- The actual coordinate inclusion induced by a finite subcomplex inclusion. -/
def realizationInclusion {M N : PreAbstractSimplicialComplex V} (h : M ≤ N) :
    C(↥(realization M), ↥(realization N)) :=
  ⟨fun x => ⟨x.val, realization_mono h x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

end FiniteRealizations

end D5.S3.Geometry.FiniteConeUnionWedge
