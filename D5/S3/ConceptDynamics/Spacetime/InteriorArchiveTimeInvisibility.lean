/- GID: D5/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/InteriorArchiveTimeInvisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Temporal-free observations depend only on the induced current region. -/

import D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
import D5.S3.ConceptDynamics.Spacetime.CoarseObservation

/-! Current correspondences and synchronized finite prefixes for native operations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.InteriorArchiveTimeInvisibility

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge TotalCopyNormalization ProductNodes
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Only current attributes and the induced causal relation are retained. -/
structure CurrentIsoData (X Y : B) where
  equiv : ↥X.val.1.current ≃ ↥Y.val.1.current
  attributes_eq : ∀ e, Y.val.1.archive.attributes (equiv e).val =
    X.val.1.archive.attributes e.val
  causal_iff : ∀ e f, Y.val.1.archive.causal (equiv e).val (equiv f).val ↔
    X.val.1.archive.causal e.val f.val
  selected_iff : ∀ e, (equiv e).val ∈ Y.val.2.val ↔ e.val ∈ X.val.2.val

private theorem q_as_current_sum (X : B) :
    q X.val = ∑ e : ↥X.val.1.current,
      if e.val ∈ X.val.2.val then contribution X.val.1 e.val else 0 := by
  change (∑ e ∈ X.val.2.val, contribution X.val.1 e) = _
  rw [← sum_selectedParents X.val.2 (contribution X.val.1)]
  have hs : selectedParents X.val.2 = Finset.univ.filter
      (fun e : ↥X.val.1.current => e.val ∈ X.val.2.val) := by
    ext e
    simp
  rw [hs, Finset.sum_filter]

private theorem current_readout_eq {X Y : B} (h : CurrentIsoData X Y) : q X.val = q Y.val := by
  rw [q_as_current_sum, q_as_current_sum, ← h.equiv.sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  simp only [h.selected_iff, contribution, h.attributes_eq]

private theorem causal_mask_iff {X Y : B} (h : CurrentIsoData X Y)
    (Q : Set SourceTimedAttribute) (e : ↥X.val.1.current) :
    (∃ d ∈ Y.val.1.current, sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧
      ((h.equiv e).val = d ∨ Y.val.1.archive.causal (h.equiv e).val d)) ↔
    (∃ d ∈ X.val.1.current, sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
      (e.val = d ∨ X.val.1.archive.causal e.val d)) := by
  constructor
  · rintro ⟨d, hd, hQ, hr⟩
    obtain ⟨f, hf⟩ := h.equiv.surjective ⟨d, hd⟩
    have hd' : d = (h.equiv f).val := (congrArg Subtype.val hf).symm
    subst d
    refine ⟨f.val, f.property, ?_, ?_⟩
    · simpa only [h.attributes_eq] using hQ
    · rcases hr with hr | hr
      · exact Or.inl (congrArg Subtype.val (h.equiv.injective (Subtype.ext hr)))
      · exact Or.inr ((h.causal_iff _ _).mp hr)
  · rintro ⟨d, hd, hQ, hr⟩
    let f : ↥X.val.1.current := ⟨d, hd⟩
    refine ⟨(h.equiv f).val, (h.equiv f).property, ?_, ?_⟩
    · simpa only [h.attributes_eq] using hQ
    · rcases hr with hr | hr
      · have he : e = f := Subtype.ext hr
        exact Or.inl (congrArg (fun z => (h.equiv z).val) he)
      · exact Or.inr ((h.causal_iff _ _).mpr hr)

private theorem mem_classical_filter {α : Type} (P : α → Prop) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α P (fun z => Classical.propDecidable (P z)) s ↔ a ∈ s ∧ P a :=
  @Finset.mem_filter α P (fun z => Classical.propDecidable (P z)) s a

private def unary_data {X Y : B} (h : CurrentIsoData X Y) (f : Unary) :
    CurrentIsoData (unary f X) (unary f Y) := by
  classical
  cases f with
  | complement =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e
    change (h.equiv e).val ∈ Y.val.1.current \ Y.val.2.val ↔
      e.val ∈ X.val.1.current \ X.val.2.val
    have he : e.val ∈ X.val.1.current := e.property
    simp only [Finset.mem_sdiff, (h.equiv e).property, he, true_and, h.selected_iff]
  | spatial S =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e
    exact (Finset.mem_filter.trans (and_congr (h.selected_iff e)
      (by first | (dsimp only; rw [h.attributes_eq]) | rw [h.attributes_eq]))).trans Finset.mem_filter.symm
  | source L =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e
    exact (Finset.mem_filter.trans (and_congr (h.selected_iff e)
      (by first | (dsimp only; rw [h.attributes_eq]) | rw [h.attributes_eq]))).trans Finset.mem_filter.symm
  | causal Q =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e
    let PX : X.val.1.Event → Prop := fun a => ∃ d ∈ X.val.1.current,
      sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
        (a = d ∨ X.val.1.archive.causal a d)
    let PY : Y.val.1.Event → Prop := fun a => ∃ d ∈ Y.val.1.current,
      sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧
        (a = d ∨ Y.val.1.archive.causal a d)
    exact (mem_classical_filter PY Y.val.2.val (h.equiv e).val).trans
      ((and_congr (h.selected_iff e) (causal_mask_iff h Q e)).trans
        (mem_classical_filter PX X.val.2.val e.val).symm)
  | shift k =>
    refine ⟨h.equiv, ?_, h.causal_iff, h.selected_iff⟩
    intro e
    exact congrArg (fun a : Attributes 3 => {a with time := a.time + k})
      (h.attributes_eq e)

/-- A correspondence of current events, order and selection without an attribute claim. -/
structure CurrentPairData (X Y : B) where
  equiv : ↥X.val.1.current ≃ ↥Y.val.1.current
  causal_iff : ∀ e f, Y.val.1.archive.causal (equiv e).val (equiv f).val ↔
    X.val.1.archive.causal e.val f.val
  selected_iff : ∀ e, (equiv e).val ∈ Y.val.2.val ↔ e.val ∈ X.val.2.val

private def parallel_pair {X X' Y Y' : B} (h : CurrentPairData X X')
    (k : CurrentPairData Y Y') :
    CurrentPairData (ParallelComposition.parallelBalanced X Y)
      (ParallelComposition.parallelBalanced X' Y') := by
  let a := CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1
  let b := CoarseObservation.parallelCurrentEquiv X'.val.1 Y'.val.1
  let e := a.symm.trans ((Equiv.sumCongr h.equiv k.equiv).trans b)
  have he (u) : e (a u) = b ((Equiv.sumCongr h.equiv k.equiv) u) := by
    change b ((Equiv.sumCongr h.equiv k.equiv) (a.symm (a u))) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨e, ?_, ?_⟩
  · intro u v
    obtain ⟨u, rfl⟩ := a.surjective u
    obtain ⟨v, rfl⟩ := a.surjective v
    dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel,
      GeneratedProduct.productBalanced, GeneratedProduct.product]
    rw [he, he]
    change (ParallelComposition.archive X'.val.1.archive Y'.val.1.archive).causal
      (ParallelComposition.equiv _ _ (Sum.map Subtype.val Subtype.val
        ((Equiv.sumCongr h.equiv k.equiv) u)))
      (ParallelComposition.equiv _ _ (Sum.map Subtype.val Subtype.val
        ((Equiv.sumCongr h.equiv k.equiv) v))) ↔
      (ParallelComposition.archive X.val.1.archive Y.val.1.archive).causal
      (ParallelComposition.equiv _ _ (Sum.map Subtype.val Subtype.val u))
      (ParallelComposition.equiv _ _ (Sum.map Subtype.val Subtype.val v))
    rw [ParallelComposition.causal_cases, ParallelComposition.causal_cases]
    cases u <;> cases v
    · exact h.causal_iff _ _
    · exact Iff.rfl
    · exact Iff.rfl
    · exact k.causal_iff _ _
  · intro u
    obtain ⟨u, rfl⟩ := a.surjective u
    dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel,
      GeneratedProduct.productBalanced, GeneratedProduct.product]
    rw [he]
    cases u with
    | inl u =>
      change ParallelComposition.equiv _ _ (.inl (h.equiv u).val) ∈
        (X'.val.2.val.disjSum Y'.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding ↔
        ParallelComposition.equiv _ _ (.inl u.val) ∈
        (X.val.2.val.disjSum Y.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inl_mem_disjSum]
        using h.selected_iff u
    | inr u =>
      change ParallelComposition.equiv _ _ (.inr (k.equiv u).val) ∈
        (X'.val.2.val.disjSum Y'.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding ↔
        ParallelComposition.equiv _ _ (.inr u.val) ∈
        (X.val.2.val.disjSum Y.val.2.val).map (ParallelComposition.equiv _ _).toEmbedding
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inr_mem_disjSum]
        using k.selected_iff u

private def product_pair {X X' Y Y' : B} (h : CurrentPairData X X')
    (k : CurrentPairData Y Y') :
    CurrentPairData (GeneratedProduct.productBalanced X Y)
      (GeneratedProduct.productBalanced X' Y') := by
  let a := CoarseObservation.generatedCurrentEquiv X.val.1 Y.val.1
  let b := CoarseObservation.generatedCurrentEquiv X'.val.1 Y'.val.1
  let e := a.symm.trans ((Equiv.prodCongr h.equiv k.equiv).trans b)
  have he (u) : e (a u) = b ((Equiv.prodCongr h.equiv k.equiv) u) := by
    change b ((Equiv.prodCongr h.equiv k.equiv) (a.symm (a u))) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨e, ?_, ?_⟩
  · intro u v
    obtain ⟨u, rfl⟩ := a.surjective u
    obtain ⟨v, rfl⟩ := a.surjective v
    dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel,
      GeneratedProduct.productBalanced, GeneratedProduct.product]
    rw [he, he]
    change (GeneratedProduct.archive _ _).causal
      (GeneratedProduct.equiv _ _ (.inr _)) (GeneratedProduct.equiv _ _ (.inr _)) ↔
      (GeneratedProduct.archive _ _).causal
      (GeneratedProduct.equiv _ _ (.inr _)) (GeneratedProduct.equiv _ _ (.inr _))
    rw [GeneratedProduct.causal_equiv, GeneratedProduct.causal_equiv]
    exact iff_of_false (ProductPaths.generated_no_path _ _ _ _)
      (ProductPaths.generated_no_path _ _ _ _)
  · intro u
    obtain ⟨u, rfl⟩ := a.surjective u
    dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel,
      GeneratedProduct.productBalanced, GeneratedProduct.product]
    rw [he]
    change GeneratedProduct.generatedMap _ _ (h.equiv u.1, k.equiv u.2) ∈
      (GeneratedProduct.selection X'.val.2 Y'.val.2).val ↔
      GeneratedProduct.generatedMap _ _ u ∈ (GeneratedProduct.selection X.val.2 Y.val.2).val
    simp only [GeneratedProduct.generated_mem_selection, h.selected_iff, k.selected_iff]

private def iso_pair {X Y : B} (h : CurrentIsoData X Y) : CurrentPairData X Y :=
  ⟨h.equiv, h.causal_iff, h.selected_iff⟩

private def parallel_data {X X' Y Y' : B} (h : CurrentIsoData X X')
    (k : CurrentIsoData Y Y') :
    CurrentIsoData (ParallelComposition.parallelBalanced X Y)
      (ParallelComposition.parallelBalanced X' Y') := by
  let hp := parallel_pair (iso_pair h) (iso_pair k)
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro u
  obtain ⟨u, rfl⟩ := (CoarseObservation.parallelCurrentEquiv X.val.1 Y.val.1).surjective u
  dsimp only [ParallelComposition.parallelBalanced, ParallelComposition.parallel,
    hp, parallel_pair, iso_pair, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  cases u with
  | inl u =>
    exact (ParallelComposition.attributes_left _ _ _).trans
      ((h.attributes_eq u).trans (ParallelComposition.attributes_left _ _ _).symm)
  | inr u =>
    exact (ParallelComposition.attributes_right _ _ _).trans
      ((k.attributes_eq u).trans (ParallelComposition.attributes_right _ _ _).symm)

private def product_data {X X' Y Y' : B} (h : CurrentIsoData X X')
    (k : CurrentIsoData Y Y') :
    CurrentIsoData (GeneratedProduct.productBalanced X Y)
      (GeneratedProduct.productBalanced X' Y') := by
  let hp := product_pair (iso_pair h) (iso_pair k)
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro u
  obtain ⟨u, rfl⟩ := (CoarseObservation.generatedCurrentEquiv X.val.1 Y.val.1).surjective u
  dsimp only [GeneratedProduct.productBalanced, GeneratedProduct.product,
    hp, product_pair, iso_pair, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (GeneratedProduct.archive X'.val.1 Y'.val.1).attributes
    (GeneratedProduct.generatedMap _ _ (h.equiv u.1, k.equiv u.2)) =
    (GeneratedProduct.archive _ _).attributes (GeneratedProduct.generatedMap _ _ u)
  simp only [GeneratedProduct.attributes_generated, ProductNodes.generatedAttributes,
    h.attributes_eq, k.attributes_eq]

private def refl_data (X : B) : CurrentIsoData X X :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

inductive Step where
  | unary (f : Unary)
  | parallelLeft (Z : B)
  | parallelRight (Z : B)
  | productLeft (Z : B)
  | productRight (Z : B)

def applyStep : Step → B → B
  | .unary f, X => unary f X
  | .parallelLeft Z, X => ParallelComposition.parallelBalanced X Z
  | .parallelRight Z, X => ParallelComposition.parallelBalanced Z X
  | .productLeft Z, X => GeneratedProduct.productBalanced X Z
  | .productRight Z, X => GeneratedProduct.productBalanced Z X

def runSteps : List Step → B → B
  | [], X => X
  | s :: w, X => runSteps w (applyStep s X)

private theorem step_reify (g : Generator nativeSignature)
    (hg : g.symbol ≠ .inr .temporal) :
    ∃ s : Step, ∀ X, strictStep nativeSignature g (some X) = some (applyStep s X) := by
  rcases g with ⟨f, i, p⟩
  cases f with
  | inl f =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim (i : Fin 1) _
    subst i
    exact ⟨.unary f, fun _ => rfl⟩
  | inr f =>
    change Fin 2 at i
    change {j : Fin 2 // j ≠ i} → B at p
    have hi : i = (0 : Fin 2) ∨ i = 1 := by omega
    cases f with
    | temporal => exact (hg rfl).elim
    | parallel =>
      rcases hi with rfl | rfl
      · exact ⟨.parallelLeft (p ⟨1, by decide⟩), fun _ => rfl⟩
      · exact ⟨.parallelRight (p ⟨0, by decide⟩), fun _ => rfl⟩
    | product =>
      rcases hi with rfl | rfl
      · exact ⟨.productLeft (p ⟨1, by decide⟩), fun _ => rfl⟩
      · exact ⟨.productRight (p ⟨0, by decide⟩), fun _ => rfl⟩

theorem reify_temporal_free (w : List (Generator nativeSignature)) (hw : WordTemporalFree w) :
    ∃ v : List Step, ∀ X, contextDenote nativeSignature w X = some (runSteps v X) := by
  induction w with
  | nil => exact ⟨[], fun _ => rfl⟩
  | cons g w ih =>
    obtain ⟨s, hs⟩ := step_reify g (hw g (by simp))
    obtain ⟨v, hv⟩ := ih (fun g hg => hw g (by simp [hg]))
    refine ⟨s :: v, fun X => ?_⟩
    change D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord
      (strictStep nativeSignature) w (strictStep nativeSignature g (some X)) = _
    rw [hs]
    exact hv (applyStep s X)

private def step_data {X Y : B} (h : CurrentIsoData X Y) (s : Step) :
    CurrentIsoData (applyStep s X) (applyStep s Y) := by
  cases s with
  | unary f => exact unary_data h f
  | parallelLeft Z => exact parallel_data h (refl_data Z)
  | parallelRight Z => exact parallel_data (refl_data Z) h
  | productLeft Z => exact product_data h (refl_data Z)
  | productRight Z => exact product_data (refl_data Z) h

private theorem temporal_free_readout {X Y : B} (h : CurrentIsoData X Y) (w : List Step) :
    q (runSteps w X).val = q (runSteps w Y).val := by
  induction w generalizing X Y with
  | nil => exact current_readout_eq h
  | cons s w ih => exact ih (step_data h s)

structure PreVariant (X Y : B) extends CurrentPairData X Y where
  exceptional : ↥X.val.1.current
  attributes_other : ∀ e, e ≠ exceptional →
    Y.val.1.archive.attributes (equiv e).val = X.val.1.archive.attributes e.val
  position_eq : (Y.val.1.archive.attributes (equiv exceptional).val).position =
    (X.val.1.archive.attributes exceptional.val).position
  positive_eq : (Y.val.1.archive.attributes (equiv exceptional).val).positive =
    (X.val.1.archive.attributes exceptional.val).positive
  source_eq : (Y.val.1.archive.attributes (equiv exceptional).val).source =
    (X.val.1.archive.attributes exceptional.val).source
  no_incoming : ∀ (e : ↥X.val.1.current), ¬ X.val.1.archive.causal e.val exceptional.val

def mask (X : B) (e : ↥X.val.1.current) (Q : Set (Attributes 3)) : Prop :=
  ∃ d : ↥X.val.1.current, X.val.1.archive.attributes d.val ∈ Q ∧
    (e = d ∨ X.val.1.archive.causal e.val d.val)

def Saturated {X Y : B} (h : PreVariant X Y)
    (Qs : List (Set (Attributes 3))) : Prop :=
  ∀ Q ∈ Qs, Q.Nonempty → mask X h.exceptional Q ∧ mask Y (h.equiv h.exceptional) Q

private theorem mask_nonempty (X : B) (e : ↥X.val.1.current) (Q : Set (Attributes 3)) :
    mask X e Q → Q.Nonempty := by
  rintro ⟨d, hd, _⟩
  exact ⟨_, hd⟩

private theorem mask_other {X Y : B} (h : PreVariant X Y)
    (a : ↥X.val.1.current) (ha : a ≠ h.exceptional) (Q : Set (Attributes 3)) :
    mask Y (h.equiv a) Q ↔ mask X a Q := by
  have exclude (d : ↥X.val.1.current)
      (hr : a = d ∨ X.val.1.archive.causal a.val d.val) : d ≠ h.exceptional := by
    intro hd
    rcases hr with hr | hr
    · exact ha (hr.trans hd)
    · exact h.no_incoming a (hd ▸ hr)
  constructor
  · rintro ⟨d, hd, hr⟩
    obtain ⟨b, rfl⟩ := h.equiv.surjective d
    have hb : a = b ∨ X.val.1.archive.causal a.val b.val :=
      hr.elim (fun he => Or.inl (h.equiv.injective he))
        (fun he => Or.inr ((h.causal_iff _ _).mp he))
    exact ⟨b, by simpa only [h.attributes_other b (exclude b hb)] using hd, hb⟩
  · rintro ⟨d, hd, hr⟩
    refine ⟨h.equiv d, ?_, ?_⟩
    · simpa only [h.attributes_other d (exclude d hr)] using hd
    · exact hr.elim (fun he => Or.inl (congrArg h.equiv he))
        (fun he => Or.inr ((h.causal_iff _ _).mpr he))

private theorem same_position {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).position =
      (X.val.1.archive.attributes a.val).position := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.position_eq
  · exact congrArg Attributes.position (h.attributes_other a ha)

private theorem same_positive {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).positive =
      (X.val.1.archive.attributes a.val).positive := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.positive_eq
  · exact congrArg Attributes.positive (h.attributes_other a ha)

private theorem same_source {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).source =
      (X.val.1.archive.attributes a.val).source := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.source_eq
  · exact congrArg Attributes.source (h.attributes_other a ha)

private theorem pre_readout_eq {X Y : B} (h : PreVariant X Y) : q X.val = q Y.val := by
  rw [q_as_current_sum, q_as_current_sum, ← h.equiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [h.selected_iff, contribution, same_positive h a]

private theorem mask_native (X : B) (a : ↥X.val.1.current) (Q : Set SourceTimedAttribute) :
    mask X a (sourceAttributeEquiv ⁻¹' Q) ↔
      ∃ d ∈ X.val.1.current, sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
        (a.val = d ∨ X.val.1.archive.causal a.val d) := by
  constructor
  · rintro ⟨d, hd, hr⟩
    exact ⟨d.val, d.property, hd, hr.elim
      (fun h => Or.inl (congrArg Subtype.val h)) Or.inr⟩
  · rintro ⟨d, hd, hQ, hr⟩
    exact ⟨⟨d, hd⟩, hQ, hr.elim (fun h => Or.inl (Subtype.ext h)) Or.inr⟩

private def unary_variant {X Y : B} (h : PreVariant X Y) (f : Unary)
    (hm : ∀ Q, f = .causal Q →
      (mask Y (h.equiv h.exceptional) (sourceAttributeEquiv ⁻¹' Q) ↔
        mask X h.exceptional (sourceAttributeEquiv ⁻¹' Q))) :
    PreVariant (unary f X) (unary f Y) := by
  classical
  cases f with
  | complement =>
    refine {
      equiv := h.equiv
      causal_iff := h.causal_iff
      selected_iff := ?_
      exceptional := h.exceptional
      attributes_other := h.attributes_other
      position_eq := h.position_eq
      positive_eq := h.positive_eq
      source_eq := h.source_eq
      no_incoming := h.no_incoming }
    intro a
    have ha : a.val ∈ X.val.1.current := a.property
    change (h.equiv a).val ∈ Y.val.1.current \ Y.val.2.val ↔
      a.val ∈ X.val.1.current \ X.val.2.val
    simp only [Finset.mem_sdiff, (h.equiv a).property, ha, true_and, h.selected_iff]
  | spatial S =>
    refine {
      equiv := h.equiv
      causal_iff := h.causal_iff
      selected_iff := ?_
      exceptional := h.exceptional
      attributes_other := h.attributes_other
      position_eq := h.position_eq
      positive_eq := h.positive_eq
      source_eq := h.source_eq
      no_incoming := h.no_incoming }
    intro a
    exact (mem_classical_filter (fun e => (Y.val.1.archive.attributes e).position ∈ S)
      Y.val.2.val (h.equiv a).val).trans ((and_congr (h.selected_iff a)
        (Iff.of_eq (congrArg (fun p => p ∈ S) (same_position h a)))).trans
          (mem_classical_filter (fun e => (X.val.1.archive.attributes e).position ∈ S)
            X.val.2.val a.val).symm)
  | source L =>
    refine {
      equiv := h.equiv
      causal_iff := h.causal_iff
      selected_iff := ?_
      exceptional := h.exceptional
      attributes_other := h.attributes_other
      position_eq := h.position_eq
      positive_eq := h.positive_eq
      source_eq := h.source_eq
      no_incoming := h.no_incoming }
    intro a
    exact (mem_classical_filter (fun e => (Y.val.1.archive.attributes e).source ∈ L)
      Y.val.2.val (h.equiv a).val).trans ((and_congr (h.selected_iff a)
        (Iff.of_eq (congrArg (fun r => r ∈ L) (same_source h a)))).trans
          (mem_classical_filter (fun e => (X.val.1.archive.attributes e).source ∈ L)
            X.val.2.val a.val).symm)
  | causal Q =>
    refine {
      equiv := h.equiv
      causal_iff := h.causal_iff
      selected_iff := ?_
      exceptional := h.exceptional
      attributes_other := h.attributes_other
      position_eq := h.position_eq
      positive_eq := h.positive_eq
      source_eq := h.source_eq
      no_incoming := h.no_incoming }
    intro a
    have hmask : mask Y (h.equiv a) (sourceAttributeEquiv ⁻¹' Q) ↔
        mask X a (sourceAttributeEquiv ⁻¹' Q) := by
      by_cases ha : a = h.exceptional
      · subst a; exact hm Q rfl
      · exact mask_other h a ha _
    let PX : X.val.1.Event → Prop := fun a => ∃ d ∈ X.val.1.current,
      sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
        (a = d ∨ X.val.1.archive.causal a d)
    let PY : Y.val.1.Event → Prop := fun a => ∃ d ∈ Y.val.1.current,
      sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧
        (a = d ∨ Y.val.1.archive.causal a d)
    exact (mem_classical_filter PY Y.val.2.val (h.equiv a).val).trans
      ((and_congr (h.selected_iff a)
        ((mask_native Y (h.equiv a) Q).symm.trans
          (hmask.trans (mask_native X a Q)))).trans
            (mem_classical_filter PX X.val.2.val a.val).symm)
  | shift k =>
    refine {
      equiv := h.equiv
      causal_iff := h.causal_iff
      selected_iff := h.selected_iff
      exceptional := h.exceptional
      attributes_other := ?_
      position_eq := h.position_eq
      positive_eq := h.positive_eq
      source_eq := h.source_eq
      no_incoming := h.no_incoming }
    intro a ha
    exact congrArg (fun z : Attributes 3 => {z with time := z.time + k})
      (h.attributes_other a ha)

private abbrev parEquiv (X Z : B) :=
  CoarseObservation.parallelCurrentEquiv X.val.1 Z.val.1

private theorem par_attr (X Z : B) (a : ↥X.val.1.current ⊕ ↥Z.val.1.current) :
    (ParallelComposition.archive X.val.1.archive Z.val.1.archive).attributes (parEquiv X Z a).val =
      a.elim (fun e => X.val.1.archive.attributes e.val)
        (fun e => Z.val.1.archive.attributes e.val) := by
  cases a with
  | inl a => exact ParallelComposition.attributes_left _ _ _
  | inr a => exact ParallelComposition.attributes_right _ _ _

private theorem par_causal (X Z : B) (a b : ↥X.val.1.current ⊕ ↥Z.val.1.current) :
    (ParallelComposition.archive X.val.1.archive Z.val.1.archive).causal
      (parEquiv X Z a).val (parEquiv X Z b).val ↔
      ParallelComposition.internal X.val.1.archive Z.val.1.archive
        (Sum.map Subtype.val Subtype.val a) (Sum.map Subtype.val Subtype.val b) :=
  ParallelComposition.causal_cases _ _ _ _

private theorem mask_parallel_left (X Z : B) (a : ↥X.val.1.current)
    (Q : Set (Attributes 3)) :
    mask (ParallelComposition.parallelBalanced X Z) (parEquiv X Z (.inl a)) Q ↔
      mask X a Q := by
  constructor
  · rintro ⟨d, hd, hr⟩
    obtain ⟨b, rfl⟩ := (parEquiv X Z).surjective d
    have hd' := Eq.mp (congrArg (fun a : Attributes 3 => a ∈ Q) (par_attr X Z b)) hd
    rcases b with b | b
    · refine ⟨b, hd', ?_⟩
      exact hr.elim (fun he => Or.inl (Sum.inl.inj ((parEquiv X Z).injective he)))
        (fun he => Or.inr ((par_causal X Z _ _).mp he))
    · rcases hr with hr | hr
      · have he := (parEquiv X Z).injective hr
        cases he
      · exact ((par_causal X Z _ _).mp hr).elim
  · rintro ⟨d, hd, hr⟩
    refine ⟨parEquiv X Z (.inl d), ?_, ?_⟩
    · exact Eq.mpr (congrArg (fun a : Attributes 3 => a ∈ Q)
        (par_attr X Z (.inl d))) hd
    · exact hr.elim (fun he => Or.inl (congrArg (fun z => parEquiv X Z (.inl z)) he))
        (fun he => Or.inr ((par_causal X Z _ _).mpr he))

private theorem mask_parallel_right (Z X : B) (a : ↥X.val.1.current)
    (Q : Set (Attributes 3)) :
    mask (ParallelComposition.parallelBalanced Z X) (parEquiv Z X (.inr a)) Q ↔
      mask X a Q := by
  constructor
  · rintro ⟨d, hd, hr⟩
    obtain ⟨b, rfl⟩ := (parEquiv Z X).surjective d
    have hd' := Eq.mp (congrArg (fun a : Attributes 3 => a ∈ Q) (par_attr Z X b)) hd
    rcases b with b | b
    · rcases hr with hr | hr
      · have he := (parEquiv Z X).injective hr
        cases he
      · exact ((par_causal Z X _ _).mp hr).elim
    · refine ⟨b, hd', ?_⟩
      exact hr.elim (fun he => Or.inl (Sum.inr.inj ((parEquiv Z X).injective he)))
        (fun he => Or.inr ((par_causal Z X _ _).mp he))
  · rintro ⟨d, hd, hr⟩
    refine ⟨parEquiv Z X (.inr d), ?_, ?_⟩
    · exact Eq.mpr (congrArg (fun a : Attributes 3 => a ∈ Q)
        (par_attr Z X (.inr d))) hd
    · exact hr.elim (fun he => Or.inl (congrArg (fun z => parEquiv Z X (.inr z)) he))
        (fun he => Or.inr ((par_causal Z X _ _).mpr he))

private def parallel_variant_left {X Y : B} (h : PreVariant X Y) (Z : B) :
    PreVariant (ParallelComposition.parallelBalanced X Z)
      (ParallelComposition.parallelBalanced Y Z) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := parallel_pair h.toCurrentPairData hz
  have he (a) : hp.equiv (parEquiv X Z a) =
      parEquiv Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _)) a) := by
    change parEquiv Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _))
      ((parEquiv X Z).symm (parEquiv X Z a))) = _
    rw [Equiv.symm_apply_apply]
  refine {
      toCurrentPairData := hp
      exceptional := parEquiv X Z (.inl h.exceptional)
      attributes_other := ?_
      position_eq := ?_
      positive_eq := ?_
      source_eq := ?_
      no_incoming := ?_ }
  · intro a ha
    obtain ⟨a, rfl⟩ := (parEquiv X Z).surjective a
    have heattr := congrArg (fun u : ↥(ParallelComposition.context Y.val.1 Z.val.1).current =>
      (ParallelComposition.archive Y.val.1.archive Z.val.1.archive).attributes u.val) (he a)
    refine heattr.trans ((par_attr Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _)) a)).trans (Eq.trans ?_ (par_attr X Z a).symm))
    cases a with
    | inl a =>
      have hne : a ≠ h.exceptional := fun eq => ha (congrArg (fun z => parEquiv X Z (.inl z)) eq)
      exact h.attributes_other a hne
    | inr a => rfl
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Y.val.1 Z.val.1).current =>
        ((ParallelComposition.archive Y.val.1.archive Z.val.1.archive).attributes u.val).position)
      (he (.inl h.exceptional))
    exact hea.trans ((congrArg Attributes.position (par_attr Y Z (.inl (h.equiv h.exceptional)))).trans
      (h.position_eq.trans (congrArg Attributes.position (par_attr X Z (.inl h.exceptional))).symm))
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Y.val.1 Z.val.1).current =>
        ((ParallelComposition.archive Y.val.1.archive Z.val.1.archive).attributes u.val).positive)
      (he (.inl h.exceptional))
    exact hea.trans ((congrArg Attributes.positive (par_attr Y Z (.inl (h.equiv h.exceptional)))).trans
      (h.positive_eq.trans (congrArg Attributes.positive (par_attr X Z (.inl h.exceptional))).symm))
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Y.val.1 Z.val.1).current =>
        ((ParallelComposition.archive Y.val.1.archive Z.val.1.archive).attributes u.val).source)
      (he (.inl h.exceptional))
    exact hea.trans ((congrArg Attributes.source (par_attr Y Z (.inl (h.equiv h.exceptional)))).trans
      (h.source_eq.trans (congrArg Attributes.source (par_attr X Z (.inl h.exceptional))).symm))
  · intro a hr
    obtain ⟨a, rfl⟩ := (parEquiv X Z).surjective a
    have hh := (par_causal X Z a (.inl h.exceptional)).mp hr
    cases a with
    | inl a => exact h.no_incoming a hh
    | inr a => exact hh.elim

private def parallel_variant_right {X Y : B} (h : PreVariant X Y) (Z : B) :
    PreVariant (ParallelComposition.parallelBalanced Z X)
      (ParallelComposition.parallelBalanced Z Y) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := parallel_pair hz h.toCurrentPairData
  have he (a) : hp.equiv (parEquiv Z X a) =
      parEquiv Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv) a) := by
    change parEquiv Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv)
      ((parEquiv Z X).symm (parEquiv Z X a))) = _
    rw [Equiv.symm_apply_apply]
  refine {
      toCurrentPairData := hp
      exceptional := parEquiv Z X (.inr h.exceptional)
      attributes_other := ?_
      position_eq := ?_
      positive_eq := ?_
      source_eq := ?_
      no_incoming := ?_ }
  · intro a ha
    obtain ⟨a, rfl⟩ := (parEquiv Z X).surjective a
    have heattr := congrArg (fun u : ↥(ParallelComposition.context Z.val.1 Y.val.1).current =>
      (ParallelComposition.archive Z.val.1.archive Y.val.1.archive).attributes u.val) (he a)
    refine heattr.trans ((par_attr Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv) a)).trans (Eq.trans ?_ (par_attr Z X a).symm))
    cases a with
    | inl a => rfl
    | inr a =>
      have hne : a ≠ h.exceptional := fun eq => ha (congrArg (fun z => parEquiv Z X (.inr z)) eq)
      exact h.attributes_other a hne
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Z.val.1 Y.val.1).current =>
        ((ParallelComposition.archive Z.val.1.archive Y.val.1.archive).attributes u.val).position)
      (he (.inr h.exceptional))
    exact hea.trans ((congrArg Attributes.position (par_attr Z Y (.inr (h.equiv h.exceptional)))).trans
      (h.position_eq.trans (congrArg Attributes.position (par_attr Z X (.inr h.exceptional))).symm))
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Z.val.1 Y.val.1).current =>
        ((ParallelComposition.archive Z.val.1.archive Y.val.1.archive).attributes u.val).positive)
      (he (.inr h.exceptional))
    exact hea.trans ((congrArg Attributes.positive (par_attr Z Y (.inr (h.equiv h.exceptional)))).trans
      (h.positive_eq.trans (congrArg Attributes.positive (par_attr Z X (.inr h.exceptional))).symm))
  · have hea := congrArg
      (fun u : ↥(ParallelComposition.context Z.val.1 Y.val.1).current =>
        ((ParallelComposition.archive Z.val.1.archive Y.val.1.archive).attributes u.val).source)
      (he (.inr h.exceptional))
    exact hea.trans ((congrArg Attributes.source (par_attr Z Y (.inr (h.equiv h.exceptional)))).trans
      (h.source_eq.trans (congrArg Attributes.source (par_attr Z X (.inr h.exceptional))).symm))
  · intro a hr
    obtain ⟨a, rfl⟩ := (parEquiv Z X).surjective a
    have hh := (par_causal Z X a (.inr h.exceptional)).mp hr
    cases a with
    | inl a => exact hh.elim
    | inr a => exact h.no_incoming a hh

private theorem parallel_variant_left_equiv {X Y : B} (h : PreVariant X Y) (Z : B)
    (a : ↥X.val.1.current ⊕ ↥Z.val.1.current) :
    (parallel_variant_left h Z).equiv (parEquiv X Z a) =
      parEquiv Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _)) a) := by
  change parEquiv Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _))
    ((parEquiv X Z).symm (parEquiv X Z a))) = _
  rw [Equiv.symm_apply_apply]
private theorem parallel_variant_right_equiv {X Y : B} (h : PreVariant X Y) (Z : B)
    (a : ↥Z.val.1.current ⊕ ↥X.val.1.current) :
    (parallel_variant_right h Z).equiv (parEquiv Z X a) =
      parEquiv Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv) a) := by
  change parEquiv Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv)
    ((parEquiv Z X).symm (parEquiv Z X a))) = _
  rw [Equiv.symm_apply_apply]

private def shiftAttributes (k : Int) (a : Attributes 3) : Attributes 3 :=
  {a with time := a.time + k}

def requiredPredicates : List Step → List (Set (Attributes 3))
  | [] => []
  | .unary (.causal Q) :: w => (sourceAttributeEquiv ⁻¹' Q) :: requiredPredicates w
  | .unary (.shift k) :: w => (requiredPredicates w).map (fun Q => shiftAttributes k ⁻¹' Q)
  | .unary _ :: w => requiredPredicates w
  | .parallelLeft _ :: w => requiredPredicates w
  | .parallelRight _ :: w => requiredPredicates w
  | .productLeft _ :: _ => []
  | .productRight _ :: _ => []

private def currentLowerBound (Z : B) : Int :=
  -(∑ e : ↥Z.val.1.current, |(Z.val.1.archive.attributes e.val).time|) - 1

private theorem current_lower_bound (Z : B) (e : ↥Z.val.1.current) :
    currentLowerBound Z ≤ (Z.val.1.archive.attributes e.val).time := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↥Z.val.1.current)) =>
    abs_nonneg (Z.val.1.archive.attributes i.val).time) (Finset.mem_univ e)
  have hl := neg_abs_le (Z.val.1.archive.attributes e.val).time
  unfold currentLowerBound
  omega

def timeThreshold : List Step → Int
  | [] => 0
  | .unary (.shift k) :: w => timeThreshold w - k
  | .unary _ :: w => timeThreshold w
  | .parallelLeft _ :: w => timeThreshold w
  | .parallelRight _ :: w => timeThreshold w
  | .productLeft Z :: _ => currentLowerBound Z
  | .productRight Z :: _ => currentLowerBound Z

private def collapse_left {X Y : B} (h : PreVariant X Y) (Z : B)
    (ht : (X.val.1.archive.attributes h.exceptional.val).time < currentLowerBound Z)
    (ht' : (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < currentLowerBound Z) :
    CurrentIsoData (GeneratedProduct.productBalanced X Z) (GeneratedProduct.productBalanced Y Z) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := product_pair h.toCurrentPairData hz
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro a
  obtain ⟨a, rfl⟩ := (CoarseObservation.generatedCurrentEquiv X.val.1 Z.val.1).surjective a
  dsimp only [GeneratedProduct.productBalanced, GeneratedProduct.product,
    hp, product_pair, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (GeneratedProduct.archive Y.val.1 Z.val.1).attributes
    (GeneratedProduct.generatedMap _ _ (h.equiv a.1, a.2)) =
    (GeneratedProduct.archive X.val.1 Z.val.1).attributes (GeneratedProduct.generatedMap _ _ a)
  rw [GeneratedProduct.attributes_generated, GeneratedProduct.attributes_generated]
  by_cases ha : a.1 = h.exceptional
  · have hx := (ht.trans_le (current_lower_bound Z a.2)).le
    have hy := (ht'.trans_le (current_lower_bound Z a.2)).le
    apply Attributes.ext
    · simpa only [ProductNodes.generatedAttributes, ha, max_eq_right hx, max_eq_right hy]
    · simp only [ProductNodes.generatedAttributes, same_position h a.1]
    · simp only [ProductNodes.generatedAttributes, same_positive h a.1]
    · simp only [ProductNodes.generatedAttributes, same_source h a.1]
  · simp only [ProductNodes.generatedAttributes, h.attributes_other a.1 ha]

private def collapse_right {X Y : B} (h : PreVariant X Y) (Z : B)
    (ht : (X.val.1.archive.attributes h.exceptional.val).time < currentLowerBound Z)
    (ht' : (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < currentLowerBound Z) :
    CurrentIsoData (GeneratedProduct.productBalanced Z X) (GeneratedProduct.productBalanced Z Y) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := product_pair hz h.toCurrentPairData
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro a
  obtain ⟨a, rfl⟩ := (CoarseObservation.generatedCurrentEquiv Z.val.1 X.val.1).surjective a
  dsimp only [GeneratedProduct.productBalanced, GeneratedProduct.product,
    hp, product_pair, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (GeneratedProduct.archive Z.val.1 Y.val.1).attributes
    (GeneratedProduct.generatedMap _ _ (a.1, h.equiv a.2)) =
    (GeneratedProduct.archive Z.val.1 X.val.1).attributes (GeneratedProduct.generatedMap _ _ a)
  rw [GeneratedProduct.attributes_generated, GeneratedProduct.attributes_generated]
  by_cases ha : a.2 = h.exceptional
  · have hx := (ht.trans_le (current_lower_bound Z a.1)).le
    have hy := (ht'.trans_le (current_lower_bound Z a.1)).le
    apply Attributes.ext
    · simpa only [ProductNodes.generatedAttributes, ha, max_eq_left hx, max_eq_left hy]
    · simp only [ProductNodes.generatedAttributes, same_position h a.2]
    · simp only [ProductNodes.generatedAttributes, same_positive h a.2]
    · simp only [ProductNodes.generatedAttributes, same_source h a.2]
  · simp only [ProductNodes.generatedAttributes, h.attributes_other a.2 ha]

theorem saturated_runSteps (w : List Step) {X Y : B} (h : PreVariant X Y)
    (ht : (X.val.1.archive.attributes h.exceptional.val).time < timeThreshold w)
    (ht' : (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < timeThreshold w)
    (hs : Saturated h (requiredPredicates w)) :
    q (runSteps w X).val = q (runSteps w Y).val := by
  induction w generalizing X Y with
  | nil => exact pre_readout_eq h
  | cons f w ih =>
    cases f with
    | productLeft Z => exact temporal_free_readout (collapse_left h Z ht ht') w
    | productRight Z => exact temporal_free_readout (collapse_right h Z ht ht') w
    | unary f =>
      have hm : ∀ Q, f = .causal Q →
          (mask Y (h.equiv h.exceptional) (sourceAttributeEquiv ⁻¹' Q) ↔
            mask X h.exceptional (sourceAttributeEquiv ⁻¹' Q)) := by
        intro Q hf
        subst f
        constructor
        · intro hy
          exact (hs _ (by simp [requiredPredicates]) (mask_nonempty Y _ _ hy)).1
        · intro hx
          exact (hs _ (by simp [requiredPredicates]) (mask_nonempty X _ _ hx)).2
      let h' := unary_variant h f hm
      apply ih h'
      · cases f <;> try exact ht
        rename_i k
        change (X.val.1.archive.attributes h.exceptional.val).time + k < timeThreshold w
        change (X.val.1.archive.attributes h.exceptional.val).time < timeThreshold w - k at ht
        omega
      · cases f <;> try exact ht'
        rename_i k
        change (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time + k < timeThreshold w
        change (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < timeThreshold w - k at ht'
        omega
      · intro Q hQ hn
        cases f with
        | complement => exact hs Q hQ hn
        | spatial S => exact hs Q hQ hn
        | source L => exact hs Q hQ hn
        | causal R => exact hs Q (by simp [requiredPredicates, hQ]) hn
        | shift k =>
          have hn' : (shiftAttributes k ⁻¹' Q).Nonempty := by
            obtain ⟨a, ha⟩ := hn
            refine ⟨shiftAttributes (-k) a, ?_⟩
            have he : shiftAttributes k (shiftAttributes (-k) a) = a := by
              cases a
              simp [shiftAttributes]
            simpa only [Set.mem_preimage, he] using ha
          exact hs (shiftAttributes k ⁻¹' Q)
            (List.mem_map.mpr ⟨Q, hQ, rfl⟩) hn'
    | parallelLeft Z =>
      let h' := parallel_variant_left h Z
      have he := parallel_variant_left_equiv h Z (.inl h.exceptional)
      have htx := congrArg Attributes.time (par_attr X Z (.inl h.exceptional))
      have hty := (congrArg
        (fun u : ↥(ParallelComposition.context Y.val.1 Z.val.1).current =>
          ((ParallelComposition.archive Y.val.1.archive Z.val.1.archive).attributes u.val).time) he).trans
        (congrArg Attributes.time (par_attr Y Z (.inl (h.equiv h.exceptional))))
      apply ih h'
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) htx) ht
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) hty) ht'
      · intro Q hQ hn
        obtain ⟨hx, hy⟩ := hs Q hQ hn
        exact ⟨(mask_parallel_left X Z h.exceptional Q).mpr hx,
          Eq.mpr (congrArg (fun e => mask (ParallelComposition.parallelBalanced Y Z) e Q) he)
            ((mask_parallel_left Y Z (h.equiv h.exceptional) Q).mpr hy)⟩
    | parallelRight Z =>
      let h' := parallel_variant_right h Z
      have he := parallel_variant_right_equiv h Z (.inr h.exceptional)
      have htx := congrArg Attributes.time (par_attr Z X (.inr h.exceptional))
      have hty := (congrArg
        (fun u : ↥(ParallelComposition.context Z.val.1 Y.val.1).current =>
          ((ParallelComposition.archive Z.val.1.archive Y.val.1.archive).attributes u.val).time) he).trans
        (congrArg Attributes.time (par_attr Z Y (.inr (h.equiv h.exceptional))))
      apply ih h'
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) htx) ht
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) hty) ht'
      · intro Q hQ hn
        obtain ⟨hx, hy⟩ := hs Q hQ hn
        exact ⟨(mask_parallel_right Z X h.exceptional Q).mpr hx,
          Eq.mpr (congrArg (fun e => mask (ParallelComposition.parallelBalanced Z Y) e Q) he)
            ((mask_parallel_right Z Y (h.equiv h.exceptional) Q).mpr hy)⟩

#print axioms reify_temporal_free
#print axioms saturated_runSteps

end
end D5.S3.ConceptDynamics.Spacetime.InteriorArchiveTimeInvisibility
