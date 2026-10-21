/- GID: D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Region charge expressibility is characterized by a common constant past tail. -/

import D5.S3.ConceptDynamics.Spacetime.InteriorArchiveTimeInvisibility

/-! Exact charge expressibility of arbitrary spacetime regions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.SourceTreeEncoding
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge TotalCopyNormalization TaggedPresentation
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Word := List (Generator nativeSignature)
abbrev Region := Set (Int × (Fin 3 → Int))

def TailAt (R : Region) (c : Int) : Prop :=
  ∀ p t t', t < c → t' < c → ((t, p) ∈ R ↔ (t', p) ∈ R)

def Tail (R : Region) : Prop := ∃ c, TailAt R c

def regionReadout (R : Region) (X : B) : Int :=
  ∑ e ∈ X.val.2.val.filter (fun e =>
    ((X.val.1.archive.attributes e).time, (X.val.1.archive.attributes e).position) ∈ R),
      contribution X.val.1 e

def QExpressible (R : Region) : Prop :=
  ∃ w : Word, ∀ X : B, ∃ Y : B,
    contextDenote nativeSignature w X = some Y ∧ q Y.val = regionReadout R X

structure TimeVariantData (X Y : B) where
  eventEquiv : X.val.1.Event ≃ Y.val.1.Event
  name_eq : ∀ e, (eventEquiv e).val = e.val
  exceptional : X.val.1.Event
  attributes_other : ∀ e, e ≠ exceptional →
    Y.val.1.archive.attributes (eventEquiv e) = X.val.1.archive.attributes e
  position_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).position =
    (X.val.1.archive.attributes exceptional).position
  positive_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).positive =
    (X.val.1.archive.attributes exceptional).positive
  source_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).source =
    (X.val.1.archive.attributes exceptional).source
  causal_iff : ∀ e f, Y.val.1.archive.causal (eventEquiv e) (eventEquiv f) ↔
    X.val.1.archive.causal e f
  current_image : X.val.1.current.map eventEquiv.toEmbedding = Y.val.1.current
  selection_image : X.val.2.val.map eventEquiv.toEmbedding = Y.val.2.val
  earlier : ∃ e, e ≠ exceptional ∧
    (X.val.1.archive.attributes e).time < (X.val.1.archive.attributes exceptional).time ∧
    (X.val.1.archive.attributes e).time <
      (Y.val.1.archive.attributes (eventEquiv exceptional)).time
  later : ∃ e, e ≠ exceptional ∧
    (X.val.1.archive.attributes exceptional).time < (X.val.1.archive.attributes e).time ∧
    (Y.val.1.archive.attributes (eventEquiv exceptional)).time <
      (X.val.1.archive.attributes e).time

def SelectedVariant (X Y : B) (p : Fin 3 → Int) (t t' : Int) : Prop :=
  ∃ h : TimeVariantData X Y,
    X.val.2.val = {h.exceptional} ∧
    (X.val.1.archive.attributes h.exceptional).position = p ∧
    (X.val.1.archive.attributes h.exceptional).positive = true ∧
    (X.val.1.archive.attributes h.exceptional).time = t ∧
    (Y.val.1.archive.attributes (h.eventEquiv h.exceptional)).time = t'

private abbrev StarNode (m : Nat) := ((Option (Fin m)) × Bool) ⊕ Bool

private def starCode (m : Nat) : StarNode m ↪ HF where
  toFun x := natCode ((Fintype.equivFin (StarNode m)) x).val
  inj' _ _ h := (Fintype.equivFin (StarNode m)).injective (Fin.ext (natCode_inj.mp h))

private def starExceptional (m : Nat) : StarNode m := .inl (none, true)

private def starCurrent (m : Nat) : Finset (StarNode m) :=
  Finset.univ.disjSum ∅

private def starRelation {m : Nat} (a b : StarNode m) : Prop :=
  a = starExceptional m ∧ ∃ i : Fin m, b = .inl (some i, true)

private def starAttributes {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) : StarNode m → Attributes 3
  | .inl (none, true) => ⟨t, p, true, FreeMagma.of 0⟩
  | .inl (some i, true) => v i
  | .inl (none, false) => ⟨0, fun _ => 0, false, FreeMagma.of 0⟩
  | .inl (some i, false) => ⟨0, fun _ => 0, !(v i).positive, FreeMagma.of 0⟩
  | .inr b => ⟨if b then hi else lo, fun _ => 0, true, FreeMagma.of 0⟩

private theorem star_irrefl {m : Nat} (a : StarNode m) : ¬ starRelation a a := by
  rintro ⟨rfl, i, h⟩
  simp [starExceptional] at h

private theorem star_trans {m : Nat} (a b d : StarNode m) :
    starRelation a b → starRelation b d → starRelation a d := by
  rintro ⟨rfl, i, rfl⟩ ⟨h, _⟩
  simp [starExceptional] at h

private theorem star_time {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (a b : StarNode m) :
    starRelation a b → (starAttributes v p lo hi t a).time <
      (starAttributes v p lo hi t b).time := by
  rintro ⟨rfl, i, rfl⟩
  exact ht i

private def starContext {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) : Context 3 :=
  contextOf (starCode m) (starAttributes v p lo hi t) starRelation
    star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m)

private theorem star_balanced {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) :
    ComplementCharge.Balanced (starContext v p lo hi t ht) := by
  refine (charge_map (starCode m) (starAttributes v p lo hi t) starRelation
    star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m)
      (starCurrent m)).trans ?_
  simp only [starCurrent, Finset.sum_disjSum, Finset.sum_empty, add_zero]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  cases i with
  | none => simp [starAttributes]
  | some i => cases h : (v i).positive <;> simp [starAttributes, h]

private def starInput {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) : B :=
  ⟨⟨starContext v p lo hi t ht,
    selectionOf (starCode m) (starAttributes v p lo hi t) starRelation
      star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m)
      {starExceptional m} (by simp [starExceptional, starCurrent])⟩,
    star_balanced v p lo hi t ht⟩

private theorem star_attributes_eq {m : Nat} (v : Fin m → Attributes 3)
    (p : Fin 3 → Int) (lo hi t : Int) (ht : ∀ i, t < (v i).time) (a : StarNode m) :
    (starInput v p lo hi t ht).val.1.archive.attributes
      (eventEquiv (starCode m) a) = starAttributes v p lo hi t a :=
  attributes_eventEquiv (starCode m) (starAttributes v p lo hi t) starRelation
    star_irrefl star_trans (star_time v p lo hi t ht) a

private theorem star_pair {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t t' : Int) (ht : ∀ i, t < (v i).time) (ht' : ∀ i, t' < (v i).time)
    (hlo : lo < t ∧ lo < t') (hhi : t < hi ∧ t' < hi) :
    SelectedVariant (starInput v p lo hi t ht) (starInput v p lo hi t' ht') p t t' := by
  let eqv := eventEquiv (starCode m)
  refine ⟨{
    eventEquiv := Equiv.refl _
    name_eq := fun _ => rfl
    exceptional := eqv (starExceptional m)
    attributes_other := ?_
    position_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]
    positive_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]
    source_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]
    causal_iff := fun _ _ => Iff.rfl
    current_image := Finset.map_refl
    selection_image := Finset.map_refl
    earlier := ?_
    later := ?_ }, ?_, by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes], by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes], by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes], by simp [eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]⟩
  · intro e he
    obtain ⟨a, rfl⟩ := eqv.surjective e
    have ha : a ≠ starExceptional m := fun h => he (congrArg eqv h)
    change starAttributes v p lo hi t' ((eventEquiv (starCode m)).symm (eqv a)) =
      starAttributes v p lo hi t ((eventEquiv (starCode m)).symm (eqv a))
    dsimp only [eqv]
    rw [Equiv.symm_apply_apply]
    cases a with
    | inr b => rfl
    | inl a =>
      rcases a with ⟨i, b⟩
      cases i <;> cases b <;> first | rfl | exact (ha rfl).elim
  · refine ⟨eqv (.inr false), ?_, ?_, ?_⟩
    · intro h
      have he := eqv.injective h
      cases he
    · simpa [eqv, starInput, starContext, contextOf, archiveOf,
        starExceptional, starAttributes] using hlo.1
    · simpa [eqv, starInput, starContext, contextOf, archiveOf,
        starExceptional, starAttributes] using hlo.2
  · refine ⟨eqv (.inr true), ?_, ?_, ?_⟩
    · intro h
      have he := eqv.injective h
      cases he
    · simpa [eqv, starInput, starContext, contextOf, archiveOf,
        starExceptional, starAttributes] using hhi.1
    · simpa [eqv, starInput, starContext, contextOf, archiveOf,
        starExceptional, starAttributes] using hhi.2
  · exact Finset.map_singleton _ _

open InteriorArchiveTimeInvisibility

private def star_current_variant {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t t' : Int) (ht : ∀ i, t < (v i).time) (ht' : ∀ i, t' < (v i).time) :
    PreVariant (starInput v p lo hi t ht) (starInput v p lo hi t' ht') := by
  let eqv := eventEquiv (starCode m)
  let e : ↥(starInput v p lo hi t ht).val.1.current :=
    ⟨eqv (starExceptional m), by simp [starInput, starContext, contextOf, starCurrent,
      starExceptional, eqv]⟩
  refine {
    equiv := Equiv.refl _
    causal_iff := fun _ _ => Iff.rfl
    selected_iff := fun _ => Iff.rfl
    exceptional := e
    attributes_other := ?_
    position_eq := by simp [e, eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]
    positive_eq := by simp [e, eqv, starInput, starContext, contextOf, archiveOf,
      starExceptional, starAttributes]
    source_eq := by
      simp [e, eqv, starInput, starContext, contextOf, archiveOf,
        starExceptional, starAttributes]
    no_incoming := ?_ }
  · intro a ha
    obtain ⟨b, hb⟩ := eqv.surjective a.val
    have hb' : b ≠ starExceptional m := by
      intro h
      apply ha
      apply Subtype.ext
      exact hb.symm.trans (congrArg eqv h)
    change starAttributes v p lo hi t' (eqv.symm a.val) =
      starAttributes v p lo hi t (eqv.symm a.val)
    rw [← hb, Equiv.symm_apply_apply]
    cases b with
    | inr b => rfl
    | inl b =>
      rcases b with ⟨i, b⟩
      cases i <;> cases b <;> first | rfl | exact (hb' rfl).elim
  · intro a
    change ¬ starRelation (eqv.symm a.val) (eqv.symm (eqv (starExceptional m)))
    rw [Equiv.symm_apply_apply]
    rintro ⟨_, i, h⟩
    simp [starExceptional] at h

private def starPoint {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (i : Option (Fin m)) (b : Bool) :
    ↥(starInput v p lo hi t ht).val.1.current :=
  ⟨eventEquiv (starCode m) (.inl (i, b)), by
    simp [starInput, starContext, contextOf, starCurrent]⟩

private theorem star_hit {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (i : Fin m)
    (Q : Set (Attributes 3)) (hv : v i ∈ Q) :
    mask (starInput v p lo hi t ht) (starPoint v p lo hi t ht none true) Q := by
  refine ⟨starPoint v p lo hi t ht (some i) true, ?_, Or.inr ?_⟩
  · simpa only [starPoint, starInput, starContext, contextOf, archiveOf,
      Equiv.symm_apply_apply, starAttributes] using hv
  · simpa only [starInput, starContext, contextOf, archiveOf, starPoint,
      Equiv.symm_apply_apply, starExceptional] using
        (show starRelation (starExceptional m) (.inl (some i, true)) from ⟨rfl, i, rfl⟩)

private theorem finite_joint_input (Qs : List (Set (Attributes 3))) (K : Int) :
    ∃ c : Int, c ≤ K ∧ ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
      ∃ X Y : B, SelectedVariant X Y p t t' ∧
        ∃ h : PreVariant X Y,
          (X.val.1.archive.attributes h.exceptional.val).time = t ∧
          (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time = t' ∧
          Saturated h Qs := by
  let v (i : Fin Qs.length) : Attributes 3 :=
    if h : (Qs.get i).Nonempty then Classical.choose h
    else ⟨0, fun _ => 0, true, FreeMagma.of 0⟩
  have hv (i : Fin Qs.length) (h : (Qs.get i).Nonempty) : v i ∈ Qs.get i := by
    simp only [v, dif_pos h]
    exact Classical.choose_spec h
  let S : Int := ∑ i, |(v i).time|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have lower (i : Fin Qs.length) : -S - 1 ≤ (v i).time := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin Qs.length))) =>
      abs_nonneg (v j).time) (Finset.mem_univ i)
    have hi' := neg_abs_le (v i).time
    change |(v i).time| ≤ S at hi
    omega
  let c := min K (min 0 (-S - 1))
  refine ⟨c, min_le_left _ _, fun p t t' ht ht' => ?_⟩
  have hc0 : c ≤ 0 := (min_le_right _ _).trans (min_le_left _ _)
  have hcl : c ≤ -S - 1 := (min_le_right _ _).trans (min_le_right _ _)
  have htv (i) : t < (v i).time := ht.trans_le (hcl.trans (lower i))
  have ht'v (i) : t' < (v i).time := ht'.trans_le (hcl.trans (lower i))
  let lo := min t t' - S - 1
  let hi := S + 1
  have hlo : lo < t ∧ lo < t' := by
    have ha := min_le_left t t'
    have hb := min_le_right t t'
    dsimp only [lo]
    omega
  have hhi : t < hi ∧ t' < hi := by
    dsimp only [hi]
    omega
  let X := starInput v p lo hi t htv
  let Y := starInput v p lo hi t' ht'v
  let h := star_current_variant v p lo hi t t' htv ht'v
  refine ⟨X, Y, star_pair v p lo hi t t' htv ht'v hlo hhi, h, ?_, ?_, ?_⟩
  · change ((starInput v p lo hi t htv).val.1.archive.attributes
      (eventEquiv (starCode Qs.length) (starExceptional Qs.length))).time = t
    exact congrArg Attributes.time (star_attributes_eq v p lo hi t htv _)
  · change ((starInput v p lo hi t' ht'v).val.1.archive.attributes
      (eventEquiv (starCode Qs.length) (starExceptional Qs.length))).time = t'
    exact congrArg Attributes.time (star_attributes_eq v p lo hi t' ht'v _)
  · intro Q hQ hn
    obtain ⟨i, hiQ⟩ := List.mem_iff_get.mp hQ
    have hvQ : v i ∈ Q := hiQ ▸ hv i (hiQ ▸ hn)
    exact ⟨star_hit v p lo hi t htv i Q hvQ, star_hit v p lo hi t' ht'v i Q hvQ⟩


private theorem normalize_word (w : Word)
    (ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :
    ∃ w' : Word, WordTemporalFree w' ∧
      ∀ X, contextDenote nativeSignature w X = contextDenote nativeSignature w' X := by
  have hc : DiagonalTotal (wordToCopy w) := by
    intro X
    simpa only [word_to_copy_denote] using ht X
  obtain ⟨_, _, _, N, _, _, he, _, ws, hw, hd, _, _⟩ :=
    total_copy_normalization (wordToCopy w) (by decide) hc
  refine ⟨ws 0, (hw 0).1, fun X => ?_⟩
  have hv : sliceAssignment (0 : Fin 1) X = fun _ => X := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [hd, hv]
  exact (word_to_copy_denote w X).symm.trans (he X)

theorem total_word_saturation (w : Word)
    (hw : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :
    ∃ c : Int, ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
      ∃ X Y : B, SelectedVariant X Y p t t' ∧
        (contextDenote nativeSignature w X).map (fun Z => q Z.val) =
          (contextDenote nativeSignature w Y).map (fun Z => q Z.val) := by
  obtain ⟨w', hf, he⟩ := normalize_word w hw
  obtain ⟨v, hv⟩ := reify_temporal_free w' hf
  obtain ⟨c, hc, hs⟩ := finite_joint_input (requiredPredicates v) (timeThreshold v)
  refine ⟨c, fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, h, hx, hy, sat⟩ := hs p t t' ht ht'
  refine ⟨X, Y, pair, ?_⟩
  rw [he X, he Y, hv X, hv Y]
  change some (q (runSteps v X).val) = some (q (runSteps v Y).val)
  apply congrArg some
  apply saturated_runSteps v h
  · rw [hx]
    exact ht.trans_le hc
  · rw [hy]
    exact ht'.trans_le hc
  · exact sat

private theorem selected_region_values (R : Region) (X Y : B)
    (p : Fin 3 → Int) (t t' : Int) (pair : SelectedVariant X Y p t t') :
    regionReadout R X = (if (t, p) ∈ R then 1 else 0) ∧
      regionReadout R Y = (if (t', p) ∈ R then 1 else 0) := by
  obtain ⟨v, selected, pos, positive, time, time'⟩ := pair
  have selected' : Y.val.2.val = {v.eventEquiv v.exceptional} := by
    rw [← v.selection_image, selected, Finset.map_singleton]
    rfl
  have pos' := v.position_eq.trans pos
  have positive' := v.positive_eq.trans positive
  constructor
  · unfold regionReadout
    rw [selected, Finset.sum_filter, Finset.sum_singleton]
    simp only [time, pos, contribution, positive, ite_true]
  · unfold regionReadout
    rw [selected', Finset.sum_filter, Finset.sum_singleton]
    simp only [time', pos', contribution, positive', ite_true]

private theorem tail_necessary (R : Region) : QExpressible R → Tail R := by
  rintro ⟨w, hw⟩
  have ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y := fun X => by
    obtain ⟨Y, hY, _⟩ := hw X
    exact ⟨Y, hY⟩
  obtain ⟨c, hc⟩ := total_word_saturation w ht
  refine ⟨c, fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, same⟩ := hc p t t' ht ht'
  obtain ⟨U, hu, hU⟩ := hw X
  obtain ⟨V, hv, hV⟩ := hw Y
  rw [hu, hv] at same
  have values : regionReadout R X = regionReadout R Y :=
    hU.symm.trans ((Option.some.inj same).trans hV)
  obtain ⟨hX, hY⟩ := selected_region_values R X Y p t t' pair
  rw [hX, hY] at values
  split_ifs at values <;> simp_all

abbrev unitBalanced : B := ComplementFibers.balancedSection 3 1

def tailCausalPredicate (R : Region) (k : Int) : Set SourceTimedAttribute :=
  {a | k + 1 ≤ a.2.2.2 ∧ (a.2.2.2 - 1, a.1) ∈ R}

def tailConstruction (R : Region) (k : Int) (X : B) : B :=
  unary (.causal (tailCausalPredicate R k))
    (GeneratedProduct.productBalanced X (unary (.shift k) unitBalanced))

private theorem generated_mask (X Z : B) (Q : Set SourceTimedAttribute)
    (p : ProductNodes.Parents X.val.1 Z.val.1) :
    (∃ d ∈ (GeneratedProduct.context X.val.1 Z.val.1).current,
      sourceAttributeEquiv ((GeneratedProduct.archive X.val.1 Z.val.1).attributes d) ∈ Q ∧
        (GeneratedProduct.generatedMap X.val.1 Z.val.1 p = d ∨
          (GeneratedProduct.archive X.val.1 Z.val.1).causal
            (GeneratedProduct.generatedMap X.val.1 Z.val.1 p) d)) ↔
      sourceAttributeEquiv (ProductNodes.generatedAttributes X.val.1 Z.val.1 p) ∈ Q := by
  constructor
  · rintro ⟨d, _, hQ, he | hc⟩
    · subst d
      simpa only [GeneratedProduct.attributes_generated] using hQ
    · obtain ⟨d, rfl⟩ := (GeneratedProduct.equiv X.val.1 Z.val.1).surjective d
      exact (ProductPaths.generated_no_path X.val.1 Z.val.1 p d
        ((GeneratedProduct.causal_equiv _ _ _ _).mp hc)).elim
  · intro hQ
    exact ⟨GeneratedProduct.generatedMap _ _ p, GeneratedProduct.generated_mem_current _ _ p,
      by simpa only [GeneratedProduct.attributes_generated] using hQ, Or.inl rfl⟩

private theorem filtered_product_readout (X Z : B) (Q : Set SourceTimedAttribute) :
    q (unary (.causal Q) (GeneratedProduct.productBalanced X Z)).val =
      ∑ p ∈ ProductNodes.selectedParents X.val.2 ×ˢ ProductNodes.selectedParents Z.val.2,
        if sourceAttributeEquiv (ProductNodes.generatedAttributes X.val.1 Z.val.1 p) ∈ Q
        then contribution X.val.1 p.1.val * contribution Z.val.1 p.2.val else 0 := by
  let P : (GeneratedProduct.archive X.val.1 Z.val.1).Event → Prop := fun e =>
    ∃ d ∈ (GeneratedProduct.context X.val.1 Z.val.1).current,
      sourceAttributeEquiv ((GeneratedProduct.archive X.val.1 Z.val.1).attributes d) ∈ Q ∧
        (e = d ∨ (GeneratedProduct.archive X.val.1 Z.val.1).causal e d)
  change (∑ e ∈ @Finset.filter _ P (fun e => Classical.propDecidable (P e))
    (GeneratedProduct.selection X.val.2 Z.val.2).val,
      contribution (GeneratedProduct.context X.val.1 Z.val.1) e) = _
  rw [Finset.sum_filter]
  change (∑ e ∈ (ProductNodes.selectedParents X.val.2 ×ˢ
    ProductNodes.selectedParents Z.val.2).map (GeneratedProduct.generatedMap _ _),
      @ite Int (P e) (Classical.propDecidable (P e))
        (contribution (GeneratedProduct.context X.val.1 Z.val.1) e) 0) = _
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  have hm := generated_mask X Z Q p
  change P (GeneratedProduct.generatedMap _ _ p) ↔ _ at hm
  simp only [hm]
  split_ifs
  · have ha := GeneratedProduct.attributes_generated X.val.1 Z.val.1 p
    exact (congrArg (fun a : Attributes 3 => if a.positive then (1 : Int) else -1) ha).trans
      (ProductNodes.generated_contribution X.val.1 Z.val.1 p)
  · rfl

private theorem shifted_unit_selected (k : Int) :
    ∃ u : ↥(unary (.shift k) unitBalanced).val.1.current,
      ProductNodes.selectedParents (unary (.shift k) unitBalanced).val.2 = {u} ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).time = k ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).position = (fun _ => 0) ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).positive = true := by
  have hc : unitBalanced.val.2.val.card = 1 :=
    by exact IntegerRepresentatives.representative_selected_card 3 1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have ham : a ∈ unitBalanced.val.2.val := by simp [ha]
  let u : ↥(unary (.shift k) unitBalanced).val.1.current :=
    ⟨a, unitBalanced.val.2.property ham⟩
  have hs : ProductNodes.selectedParents (unary (.shift k) unitBalanced).val.2 = {u} := by
    ext e
    simp only [ProductNodes.mem_selectedParents, Finset.mem_singleton]
    change e.val ∈ unitBalanced.val.2.val ↔ e = u
    rw [ha, Finset.mem_singleton]
    exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  have hq : q unitBalanced.val = 1 := IntegerRepresentatives.representative_readout 3 1
  have hp : (unitBalanced.val.1.archive.attributes a).positive = true := by
    change (∑ e ∈ unitBalanced.val.2.val, contribution unitBalanced.val.1 e) = 1 at hq
    rw [ha, Finset.sum_singleton] at hq
    unfold contribution at hq
    cases he : (unitBalanced.val.1.archive.attributes a).positive <;> simp_all
  refine ⟨u, hs, ?_, rfl, hp⟩
  change 0 + k = k
  omega

theorem tail_construction_q (R : Region) (c k : Int) (hR : TailAt R c) (hk : k ≤ c - 1)
    (X : B) : q (tailConstruction R k X).val = regionReadout R X := by
  obtain ⟨u, hu, htime, hpos, hsign⟩ := shifted_unit_selected k
  unfold tailConstruction
  rw [filtered_product_readout, hu, Finset.sum_product]
  simp only [Finset.sum_singleton]
  have htest (e : ↥X.val.1.current) :
      sourceAttributeEquiv (ProductNodes.generatedAttributes X.val.1
        (unary (.shift k) unitBalanced).val.1 (e, u)) ∈ tailCausalPredicate R k ↔
        ((X.val.1.archive.attributes e.val).time,
          (X.val.1.archive.attributes e.val).position) ∈ R := by
    change (k + 1 ≤ max (X.val.1.archive.attributes e.val).time
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).time + 1 ∧
        (max (X.val.1.archive.attributes e.val).time
          ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).time + 1 - 1,
            fun i => (X.val.1.archive.attributes e.val).position i +
              ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).position i) ∈ R) ↔ _
    rw [htime, hpos]
    simp only [add_sub_cancel_right, add_zero]
    have hb : k + 1 ≤ max (X.val.1.archive.attributes e.val).time k + 1 := by omega
    simp only [hb, true_and]
    by_cases he : (X.val.1.archive.attributes e.val).time ≤ k
    · rw [max_eq_right he]
      exact (hR _ _ _ (by omega) (by omega)).symm
    · rw [max_eq_left (by omega)]
  calc
    _ = ∑ e ∈ ProductNodes.selectedParents X.val.2,
        if ((X.val.1.archive.attributes e.val).time,
          (X.val.1.archive.attributes e.val).position) ∈ R
        then contribution X.val.1 e.val else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [htest e, contribution, hsign, ite_true, mul_one]
    _ = regionReadout R X := by
      exact (ProductNodes.sum_selectedParents X.val.2
        (fun e => if ((X.val.1.archive.attributes e).time,
          (X.val.1.archive.attributes e).position) ∈ R then contribution X.val.1 e else 0)).trans
          (Finset.sum_filter _ _).symm

private def constructionWord (R : Region) (k : Int) : Word :=
  [⟨.inr .product, 0, fun _ => unary (.shift k) unitBalanced⟩,
    ⟨.inl (.causal (tailCausalPredicate R k)), 0, fun j =>
      (j.property (Subsingleton.elim (j.val : Fin 1) 0)).elim⟩]

theorem q_expressible_iff_tail (R : Region) : QExpressible R ↔ Tail R := by
  refine ⟨tail_necessary R, ?_⟩
  rintro ⟨c, hc⟩
  refine ⟨constructionWord R (c - 1), fun X =>
    ⟨tailConstruction R (c - 1) X, rfl, tail_construction_q R c (c - 1) hc (by omega) X⟩⟩

#print axioms total_word_saturation
#print axioms tail_construction_q
#print axioms q_expressible_iff_tail

end
end D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
