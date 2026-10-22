/- GID: D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Region charge expressibility is characterized by a common constant past tail. -/

import D5.S3.ConceptDynamics.Spacetime.TotalCopyNormalization
import D5.S3.ConceptDynamics.Spacetime.CoarseObservation
/-! Exact charge expressibility of arbitrary spacetime regions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge TotalCopyNormalization ProductNodes
open CoarseObservation (generatedCurrentEquiv parallelCurrentEquiv)
open CoarseObservation renaming parallelCurrentEquiv → parEquiv
open GeneratedProduct (causal_equiv generatedMap generated_mem_current
  generated_mem_selection product productBalanced)
open ParallelComposition (parallelBalanced)
open ParallelComposition renaming
  archive → parArchive, context → parContext, equiv → parEventEquiv, internal → parInternal, parallel → parallel
open GeneratedProduct renaming
  archive → prodArchive, context → prodContext, equiv → prodEventEquiv, selection → prodSelection,
  attributes_generated → prodAttributes
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Only current attributes and the induced causal relation are retained. -/
private structure CurrentIsoData (X Y : B) where
  equiv : ↥X.val.1.current ≃ ↥Y.val.1.current
  attributes_eq : ∀ e, Y.val.1.archive.attributes (equiv e).val = X.val.1.archive.attributes e.val
  causal_iff : ∀ e f, Y.val.1.archive.causal (equiv e).val (equiv f).val ↔ X.val.1.archive.causal e.val f.val
  selected_iff : ∀ e, (equiv e).val ∈ Y.val.2.val ↔ e.val ∈ X.val.2.val
private theorem q_as_current_sum (X : B) : q X.val = ∑ e : ↥X.val.1.current,
      if e.val ∈ X.val.2.val then contribution X.val.1 e.val else 0 := by
  change (∑ e ∈ X.val.2.val, contribution X.val.1 e) = _; rw [← sum_selectedParents X.val.2 (contribution X.val.1)]
  have hs : selectedParents X.val.2 = Finset.univ.filter (fun e : ↥X.val.1.current => e.val ∈ X.val.2.val) := by
    ext e; simp
  rw [hs, Finset.sum_filter]
private theorem current_readout_eq {X Y : B} (h : CurrentIsoData X Y) : q X.val = q Y.val := by
  rw [q_as_current_sum, q_as_current_sum, ← h.equiv.sum_comp]; apply Finset.sum_congr rfl
  intro e _; simp only [h.selected_iff, contribution, h.attributes_eq]
private theorem causal_mask_iff {X Y : B} (h : CurrentIsoData X Y)
    (Q : Set SourceTimedAttribute) (e : ↥X.val.1.current) :
    (∃ d ∈ Y.val.1.current, sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧
      ((h.equiv e).val = d ∨ Y.val.1.archive.causal (h.equiv e).val d)) ↔
    (∃ d ∈ X.val.1.current, sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
      (e.val = d ∨ X.val.1.archive.causal e.val d)) := by
  have hy := Finset.exists_coe Y.val.1.current (fun d =>
    sourceAttributeEquiv (Y.val.1.archive.attributes d.val) ∈ Q ∧
      ((h.equiv e).val = d.val ∨ Y.val.1.archive.causal (h.equiv e).val d.val))
  have hx := Finset.exists_coe X.val.1.current (fun d =>
    sourceAttributeEquiv (X.val.1.archive.attributes d.val) ∈ Q ∧
      (e.val = d.val ∨ X.val.1.archive.causal e.val d.val))
  simp only [exists_prop] at hx hy
  rw [← hy, ← hx]; exact (h.equiv.exists_congr (fun d => by
    simp only [h.attributes_eq, h.causal_iff, Subtype.val_inj, h.equiv.injective.eq_iff])).symm
private def unary_data {X Y : B} (h : CurrentIsoData X Y) (f : Unary) : CurrentIsoData (unary f X) (unary f Y) := by
  classical
  cases f with
  | complement =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e; change (h.equiv e).val ∈ Y.val.1.current \ Y.val.2.val ↔ e.val ∈ X.val.1.current \ X.val.2.val
    have he : e.val ∈ X.val.1.current := e.property
    simp only [Finset.mem_sdiff, (h.equiv e).property, he, true_and, h.selected_iff]
  | spatial S =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e; exact (Finset.mem_filter.trans (and_congr (h.selected_iff e)
      (by first | (dsimp only; rw [h.attributes_eq]) | rw [h.attributes_eq]))).trans Finset.mem_filter.symm
  | source L =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e; exact (Finset.mem_filter.trans (and_congr (h.selected_iff e)
      (by first | (dsimp only; rw [h.attributes_eq]) | rw [h.attributes_eq]))).trans Finset.mem_filter.symm
  | causal Q =>
    refine ⟨h.equiv, h.attributes_eq, h.causal_iff, ?_⟩
    intro e
    let PX : X.val.1.Event → Prop := fun a => ∃ d ∈ X.val.1.current,
      sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧ (a = d ∨ X.val.1.archive.causal a d)
    let PY : Y.val.1.Event → Prop := fun a => ∃ d ∈ Y.val.1.current,
      sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧ (a = d ∨ Y.val.1.archive.causal a d)
    exact (@Finset.mem_filter _ PY (fun z => Classical.propDecidable (PY z)) Y.val.2.val (h.equiv e).val).trans
      ((and_congr (h.selected_iff e) (causal_mask_iff h Q e)).trans
        (@Finset.mem_filter _ PX (fun z => Classical.propDecidable (PX z)) X.val.2.val e.val).symm)
  | shift k =>
    refine ⟨h.equiv, ?_, h.causal_iff, h.selected_iff⟩
    intro e; exact congrArg (fun a : Attributes 3 => {a with time := a.time + k}) (h.attributes_eq e)

/-- A correspondence of current events, order and selection without an attribute claim. -/

private structure CurrentPairData (X Y : B) where
  equiv : ↥X.val.1.current ≃ ↥Y.val.1.current
  causal_iff : ∀ e f, Y.val.1.archive.causal (equiv e).val (equiv f).val ↔ X.val.1.archive.causal e.val f.val
  selected_iff : ∀ e, (equiv e).val ∈ Y.val.2.val ↔ e.val ∈ X.val.2.val
private def parallel_pair {X X' Y Y' : B} (h : CurrentPairData X X') (k : CurrentPairData Y Y') :
    CurrentPairData (parallelBalanced X Y) (parallelBalanced X' Y') := by
  let a := parallelCurrentEquiv X.val.1 Y.val.1
  let b := parallelCurrentEquiv X'.val.1 Y'.val.1
  let e := a.symm.trans ((Equiv.sumCongr h.equiv k.equiv).trans b)
  have he (u) : e (a u) = b ((Equiv.sumCongr h.equiv k.equiv) u) := by
    change b ((Equiv.sumCongr h.equiv k.equiv) (a.symm (a u))) = _; rw [Equiv.symm_apply_apply]
  refine ⟨e, ?_, ?_⟩
  · intro u v
    obtain ⟨u, rfl⟩ := a.surjective u
    obtain ⟨v, rfl⟩ := a.surjective v
    dsimp only [parallelBalanced, parallel, productBalanced, product]; rw [he, he]
    change (parArchive X'.val.1.archive Y'.val.1.archive).causal
      (parEventEquiv _ _ (Sum.map Subtype.val Subtype.val ((Equiv.sumCongr h.equiv k.equiv) u)))
      (parEventEquiv _ _ (Sum.map Subtype.val Subtype.val ((Equiv.sumCongr h.equiv k.equiv) v))) ↔
      (parArchive X.val.1.archive Y.val.1.archive).causal (parEventEquiv _ _ (Sum.map Subtype.val Subtype.val u))
      (parEventEquiv _ _ (Sum.map Subtype.val Subtype.val v))
    rw [ParallelComposition.causal_cases, ParallelComposition.causal_cases]; cases u <;> cases v
    · exact h.causal_iff _ _
    · exact Iff.rfl
    · exact Iff.rfl
    · exact k.causal_iff _ _
  · intro u
    obtain ⟨u, rfl⟩ := a.surjective u
    dsimp only [parallelBalanced, parallel, productBalanced, product]; rw [he]
    cases u with
    | inl u =>
      change parEventEquiv _ _ (.inl (h.equiv u).val) ∈
        (X'.val.2.val.disjSum Y'.val.2.val).map (parEventEquiv _ _).toEmbedding ↔ parEventEquiv _ _ (.inl u.val) ∈
        (X.val.2.val.disjSum Y.val.2.val).map (parEventEquiv _ _).toEmbedding
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inl_mem_disjSum] using h.selected_iff u
    | inr u =>
      change parEventEquiv _ _ (.inr (k.equiv u).val) ∈
        (X'.val.2.val.disjSum Y'.val.2.val).map (parEventEquiv _ _).toEmbedding ↔ parEventEquiv _ _ (.inr u.val) ∈
        (X.val.2.val.disjSum Y.val.2.val).map (parEventEquiv _ _).toEmbedding
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.inr_mem_disjSum] using k.selected_iff u
private def product_pair {X X' Y Y' : B} (h : CurrentPairData X X') (k : CurrentPairData Y Y') :
    CurrentPairData (productBalanced X Y) (productBalanced X' Y') := by
  let a := generatedCurrentEquiv X.val.1 Y.val.1
  let b := generatedCurrentEquiv X'.val.1 Y'.val.1
  let e := a.symm.trans ((Equiv.prodCongr h.equiv k.equiv).trans b)
  have he (u) : e (a u) = b ((Equiv.prodCongr h.equiv k.equiv) u) := by
    change b ((Equiv.prodCongr h.equiv k.equiv) (a.symm (a u))) = _; rw [Equiv.symm_apply_apply]
  refine ⟨e, ?_, ?_⟩
  · intro u v
    obtain ⟨u, rfl⟩ := a.surjective u
    obtain ⟨v, rfl⟩ := a.surjective v
    dsimp only [parallelBalanced, parallel, productBalanced, product]; rw [he, he]
    change (prodArchive _ _).causal (prodEventEquiv _ _ (.inr _)) (prodEventEquiv _ _ (.inr _)) ↔
      (prodArchive _ _).causal (prodEventEquiv _ _ (.inr _)) (prodEventEquiv _ _ (.inr _))
    rw [causal_equiv, causal_equiv]
    exact iff_of_false (ProductPaths.generated_no_path _ _ _ _) (ProductPaths.generated_no_path _ _ _ _)
  · intro u
    obtain ⟨u, rfl⟩ := a.surjective u
    dsimp only [parallelBalanced, parallel, productBalanced, product]; rw [he]
    change generatedMap _ _ (h.equiv u.1, k.equiv u.2) ∈ (prodSelection X'.val.2 Y'.val.2).val ↔
      generatedMap _ _ u ∈ (prodSelection X.val.2 Y.val.2).val
    simp only [generated_mem_selection, h.selected_iff, k.selected_iff]
private def iso_pair {X Y : B} (h : CurrentIsoData X Y) : CurrentPairData X Y :=
  ⟨h.equiv, h.causal_iff, h.selected_iff⟩
private def parallel_data {X X' Y Y' : B} (h : CurrentIsoData X X') (k : CurrentIsoData Y Y') :
    CurrentIsoData (parallelBalanced X Y) (parallelBalanced X' Y') := by
  let hp := parallel_pair (iso_pair h) (iso_pair k)
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro u
  obtain ⟨u, rfl⟩ := (parallelCurrentEquiv X.val.1 Y.val.1).surjective u
  dsimp only [parallelBalanced, parallel, hp, parallel_pair, iso_pair, Equiv.trans_apply]; rw [Equiv.symm_apply_apply]
  cases u with
  | inl u =>
    exact (ParallelComposition.attributes_left _ _ _).trans
      ((h.attributes_eq u).trans (ParallelComposition.attributes_left _ _ _).symm)
  | inr u =>
    exact (ParallelComposition.attributes_right _ _ _).trans
      ((k.attributes_eq u).trans (ParallelComposition.attributes_right _ _ _).symm)
private def product_data {X X' Y Y' : B} (h : CurrentIsoData X X') (k : CurrentIsoData Y Y') :
    CurrentIsoData (productBalanced X Y) (productBalanced X' Y') := by
  let hp := product_pair (iso_pair h) (iso_pair k)
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro u
  obtain ⟨u, rfl⟩ := (generatedCurrentEquiv X.val.1 Y.val.1).surjective u
  dsimp only [productBalanced, product, hp, product_pair, iso_pair, Equiv.trans_apply]; rw [Equiv.symm_apply_apply]
  change (prodArchive X'.val.1 Y'.val.1).attributes (generatedMap _ _ (h.equiv u.1, k.equiv u.2)) =
    (prodArchive _ _).attributes (generatedMap _ _ u)
  simp only [prodAttributes, generatedAttributes, h.attributes_eq, k.attributes_eq]
private def refl_data (X : B) : CurrentIsoData X X :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

private inductive Step where
  | unary (f : Unary)
  | parallelLeft (Z : B)
  | parallelRight (Z : B)
  | productLeft (Z : B)
  | productRight (Z : B)
private def applyStep : Step → B → B
  | .unary f, X => unary f X
  | .parallelLeft Z, X => parallelBalanced X Z
  | .parallelRight Z, X => parallelBalanced Z X
  | .productLeft Z, X => productBalanced X Z
  | .productRight Z, X => productBalanced Z X
private def runSteps : List Step → B → B
  | [], X => X
  | s :: w, X => runSteps w (applyStep s X)
private theorem step_reify (g : Generator nativeSignature) (hg : g.symbol ≠ .inr .temporal) :
    ∃ s : Step, ∀ X, strictStep nativeSignature g (some X) = some (applyStep s X) := by
  rcases g with ⟨f, i, p⟩
  cases f with
  | inl f =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim (i : Fin 1) _
    subst i
    exact ⟨.unary f, fun _ => rfl⟩
  | inr f =>
    change Fin 2 at i; change {j : Fin 2 // j ≠ i} → B at p
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
private theorem reify_temporal_free (w : List (Generator nativeSignature)) (hw : WordTemporalFree w) :
    ∃ v : List Step, ∀ X, contextDenote nativeSignature w X = some (runSteps v X) := by
  induction w with
  | nil => exact ⟨[], fun _ => rfl⟩
  | cons g w ih =>
    obtain ⟨s, hs⟩ := step_reify g (hw g (by simp))
    obtain ⟨v, hv⟩ := ih (fun g hg => hw g (by simp [hg]))
    refine ⟨s :: v, fun X => ?_⟩
    change D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality.runWord
      (strictStep nativeSignature) w (strictStep nativeSignature g (some X)) = _
    rw [hs]; exact hv (applyStep s X)
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

private structure PreVariant (X Y : B) extends CurrentPairData X Y where
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
private def mask (X : B) (e : ↥X.val.1.current) (Q : Set (Attributes 3)) : Prop :=
  ∃ d : ↥X.val.1.current, X.val.1.archive.attributes d.val ∈ Q ∧ (e = d ∨ X.val.1.archive.causal e.val d.val)
private def Saturated {X Y : B} (h : PreVariant X Y) (Qs : List (Set (Attributes 3))) : Prop :=
  ∀ Q ∈ Qs, Q.Nonempty → mask X h.exceptional Q ∧ mask Y (h.equiv h.exceptional) Q
private theorem mask_nonempty (X : B) (e : ↥X.val.1.current) (Q : Set (Attributes 3)) : mask X e Q → Q.Nonempty := by
  rintro ⟨d, hd, _⟩; exact ⟨_, hd⟩
private theorem mask_other {X Y : B} (h : PreVariant X Y)
    (a : ↥X.val.1.current) (ha : a ≠ h.exceptional) (Q : Set (Attributes 3)) : mask Y (h.equiv a) Q ↔ mask X a Q := by
  have exclude (d : ↥X.val.1.current) (hr : a = d ∨ X.val.1.archive.causal a.val d.val) : d ≠ h.exceptional := by
    intro hd
    rcases hr with hr | hr
    · exact ha (hr.trans hd)
    · exact h.no_incoming a (hd ▸ hr)
  constructor
  · rintro ⟨d, hd, hr⟩
    obtain ⟨b, rfl⟩ := h.equiv.surjective d
    have hb : a = b ∨ X.val.1.archive.causal a.val b.val := hr.elim (fun he => Or.inl (h.equiv.injective he))
        (fun he => Or.inr ((h.causal_iff _ _).mp he))
    exact ⟨b, by simpa only [h.attributes_other b (exclude b hb)] using hd, hb⟩
  · rintro ⟨d, hd, hr⟩
    refine ⟨h.equiv d, ?_, ?_⟩
    · simpa only [h.attributes_other d (exclude d hr)] using hd
    · exact hr.elim (fun he => Or.inl (congrArg h.equiv he)) (fun he => Or.inr ((h.causal_iff _ _).mpr he))
private theorem same_position {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).position = (X.val.1.archive.attributes a.val).position := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.position_eq
  · exact congrArg Attributes.position (h.attributes_other a ha)
private theorem same_positive {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).positive = (X.val.1.archive.attributes a.val).positive := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.positive_eq
  · exact congrArg Attributes.positive (h.attributes_other a ha)
private theorem same_source {X Y : B} (h : PreVariant X Y) (a : ↥X.val.1.current) :
    (Y.val.1.archive.attributes (h.equiv a).val).source = (X.val.1.archive.attributes a.val).source := by
  by_cases ha : a = h.exceptional
  · subst a; exact h.source_eq
  · exact congrArg Attributes.source (h.attributes_other a ha)
private theorem pre_readout_eq {X Y : B} (h : PreVariant X Y) : q X.val = q Y.val := by
  rw [q_as_current_sum, q_as_current_sum, ← h.equiv.sum_comp]; apply Finset.sum_congr rfl
  intro a _; simp only [h.selected_iff, contribution, same_positive h a]
private theorem mask_native (X : B) (a : ↥X.val.1.current) (Q : Set SourceTimedAttribute) :
    mask X a (sourceAttributeEquiv ⁻¹' Q) ↔
      ∃ d ∈ X.val.1.current, sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧
        (a.val = d ∨ X.val.1.archive.causal a.val d) := by
  have eq (d : ↥X.val.1.current) : (a = d) ↔ (a.val = d.val) := Subtype.ext_iff
  simp only [mask, eq, Set.mem_preimage]
  simpa only [exists_prop] using (Finset.exists_coe X.val.1.current (fun d =>
    sourceAttributeEquiv (X.val.1.archive.attributes d.val) ∈ Q ∧
      (a.val = d.val ∨ X.val.1.archive.causal a.val d.val)))
private def unary_variant {X Y : B} (h : PreVariant X Y) (f : Unary) (hm : ∀ Q, f = .causal Q →
      (mask Y (h.equiv h.exceptional) (sourceAttributeEquiv ⁻¹' Q) ↔
        mask X h.exceptional (sourceAttributeEquiv ⁻¹' Q))) : PreVariant (unary f X) (unary f Y) := by
  classical
  cases f with
  | complement =>
    refine { h with selected_iff := ?_ }
    intro a
    have ha : a.val ∈ X.val.1.current := a.property
    change (h.equiv a).val ∈ Y.val.1.current \ Y.val.2.val ↔ a.val ∈ X.val.1.current \ X.val.2.val
    simp only [Finset.mem_sdiff, (h.equiv a).property, ha, true_and, h.selected_iff]
  | spatial S =>
    refine { h with selected_iff := ?_ }
    intro a; exact (@Finset.mem_filter _ (fun e => (Y.val.1.archive.attributes e).position ∈ S)
      (fun _ => Classical.propDecidable _) Y.val.2.val (h.equiv a).val).trans ((and_congr (h.selected_iff a)
        (Iff.of_eq (congrArg (fun p => p ∈ S) (same_position h a)))).trans
          (@Finset.mem_filter _ (fun e => (X.val.1.archive.attributes e).position ∈ S)
            (fun _ => Classical.propDecidable _) X.val.2.val a.val).symm)
  | source L =>
    refine { h with selected_iff := ?_ }
    intro a; exact (@Finset.mem_filter _ (fun e => (Y.val.1.archive.attributes e).source ∈ L)
      (fun _ => Classical.propDecidable _) Y.val.2.val (h.equiv a).val).trans ((and_congr (h.selected_iff a)
        (Iff.of_eq (congrArg (fun r => r ∈ L) (same_source h a)))).trans
          (@Finset.mem_filter _ (fun e => (X.val.1.archive.attributes e).source ∈ L)
            (fun _ => Classical.propDecidable _) X.val.2.val a.val).symm)
  | causal Q =>
    refine { h with selected_iff := ?_ }
    intro a
    have hmask : mask Y (h.equiv a) (sourceAttributeEquiv ⁻¹' Q) ↔ mask X a (sourceAttributeEquiv ⁻¹' Q) := by
      by_cases ha : a = h.exceptional
      · subst a; exact hm Q rfl
      · exact mask_other h a ha _
    let PX : X.val.1.Event → Prop := fun a => ∃ d ∈ X.val.1.current,
      sourceAttributeEquiv (X.val.1.archive.attributes d) ∈ Q ∧ (a = d ∨ X.val.1.archive.causal a d)
    let PY : Y.val.1.Event → Prop := fun a => ∃ d ∈ Y.val.1.current,
      sourceAttributeEquiv (Y.val.1.archive.attributes d) ∈ Q ∧ (a = d ∨ Y.val.1.archive.causal a d)
    exact (@Finset.mem_filter _ PY (fun z => Classical.propDecidable (PY z)) Y.val.2.val (h.equiv a).val).trans
      ((and_congr (h.selected_iff a)
        ((mask_native Y (h.equiv a) Q).symm.trans (hmask.trans (mask_native X a Q)))).trans
            (@Finset.mem_filter _ PX (fun z => Classical.propDecidable (PX z)) X.val.2.val a.val).symm)
  | shift k =>
    refine { h with attributes_other := ?_ }
    intro a ha; exact congrArg (fun z : Attributes 3 => {z with time := z.time + k}) (h.attributes_other a ha)

private theorem par_attr (X Z : B) (a : ↥X.val.1.current ⊕ ↥Z.val.1.current) :
    (parArchive X.val.1.archive Z.val.1.archive).attributes (parEquiv X.val.1 Z.val.1 a).val =
      a.elim (fun e => X.val.1.archive.attributes e.val) (fun e => Z.val.1.archive.attributes e.val) := by
  cases a with
  | inl a => exact ParallelComposition.attributes_left _ _ _
  | inr a => exact ParallelComposition.attributes_right _ _ _
private theorem mask_parallel_left (X Z : B) (a : ↥X.val.1.current) (Q : Set (Attributes 3)) :
    mask (parallelBalanced X Z) (parEquiv X.val.1 Z.val.1 (.inl a)) Q ↔ mask X a Q := by
  unfold mask; change (∃ d : ↥(parContext X.val.1 Z.val.1).current,
    (parArchive X.val.1.archive Z.val.1.archive).attributes d.val ∈ Q ∧
      (parEquiv X.val.1 Z.val.1 (.inl a) = d ∨
        (parArchive X.val.1.archive Z.val.1.archive).causal
          (parEquiv X.val.1 Z.val.1 (.inl a)).val d.val)) ↔ _
  refine (Equiv.exists_congr_right (parEquiv X.val.1 Z.val.1)).symm.trans ?_
  simp only [par_attr, (parEquiv X.val.1 Z.val.1).injective.eq_iff, Sum.exists]
  simp only [parEquiv, Equiv.ofBijective_apply,
    ParallelComposition.causal_cases,
    parInternal, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, or_false, false_or,
    and_false, false_and, exists_false, or_false]
private theorem mask_parallel_right (Z X : B) (a : ↥X.val.1.current) (Q : Set (Attributes 3)) :
    mask (parallelBalanced Z X) (parEquiv Z.val.1 X.val.1 (.inr a)) Q ↔ mask X a Q := by
  unfold mask; change (∃ d : ↥(parContext Z.val.1 X.val.1).current,
    (parArchive Z.val.1.archive X.val.1.archive).attributes d.val ∈ Q ∧
      (parEquiv Z.val.1 X.val.1 (.inr a) = d ∨
        (parArchive Z.val.1.archive X.val.1.archive).causal
          (parEquiv Z.val.1 X.val.1 (.inr a)).val d.val)) ↔ _
  refine (Equiv.exists_congr_right (parEquiv Z.val.1 X.val.1)).symm.trans ?_
  simp only [par_attr, (parEquiv Z.val.1 X.val.1).injective.eq_iff, Sum.exists]
  simp only [parEquiv, Equiv.ofBijective_apply,
    ParallelComposition.causal_cases,
    parInternal, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, or_false, false_or,
    and_false, false_and, exists_false, or_false]
private def parallel_variant_left {X Y : B} (h : PreVariant X Y) (Z : B) :
    PreVariant (parallelBalanced X Z) (parallelBalanced Y Z) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := parallel_pair h.toCurrentPairData hz
  have he (a) : hp.equiv (parEquiv X.val.1 Z.val.1 a) = parEquiv Y.val.1 Z.val.1 ((Equiv.sumCongr h.equiv (Equiv.refl _)) a) := by
    change parEquiv Y.val.1 Z.val.1 ((Equiv.sumCongr h.equiv (Equiv.refl _)) ((parEquiv X.val.1 Z.val.1).symm (parEquiv X.val.1 Z.val.1 a))) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨hp, parEquiv X.val.1 Z.val.1 (.inl h.exceptional), ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a, rfl⟩ := (parEquiv X.val.1 Z.val.1).surjective a
    have heattr := congrArg (fun u : ↥(parContext Y.val.1 Z.val.1).current =>
      (parArchive Y.val.1.archive Z.val.1.archive).attributes u.val) (he a)
    refine heattr.trans ((par_attr Y Z ((Equiv.sumCongr h.equiv (Equiv.refl _)) a)).trans
      (Eq.trans ?_ (par_attr X Z a).symm))
    cases a with
    | inl a =>
      have hne : a ≠ h.exceptional := fun eq => ha (congrArg (fun z => parEquiv X.val.1 Z.val.1 (.inl z)) eq)
      exact h.attributes_other a hne
    | inr a => rfl
  · change ((parArchive Y.val.1.archive Z.val.1.archive).attributes _).position =
      ((parArchive X.val.1.archive Z.val.1.archive).attributes _).position
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.elim_inl] using h.position_eq
  · change ((parArchive Y.val.1.archive Z.val.1.archive).attributes _).positive =
      ((parArchive X.val.1.archive Z.val.1.archive).attributes _).positive
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.elim_inl] using h.positive_eq
  · change ((parArchive Y.val.1.archive Z.val.1.archive).attributes _).source =
      ((parArchive X.val.1.archive Z.val.1.archive).attributes _).source
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.elim_inl] using h.source_eq
  · intro a hr
    obtain ⟨a, rfl⟩ := (parEquiv X.val.1 Z.val.1).surjective a
    have hh := (ParallelComposition.causal_cases _ _ _ _).mp hr; cases a with
    | inl a => exact h.no_incoming a hh
    | inr a => exact hh.elim
private def parallel_variant_right {X Y : B} (h : PreVariant X Y) (Z : B) :
    PreVariant (parallelBalanced Z X) (parallelBalanced Z Y) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := parallel_pair hz h.toCurrentPairData
  have he (a) : hp.equiv (parEquiv Z.val.1 X.val.1 a) = parEquiv Z.val.1 Y.val.1 ((Equiv.sumCongr (Equiv.refl _) h.equiv) a) := by
    change parEquiv Z.val.1 Y.val.1 ((Equiv.sumCongr (Equiv.refl _) h.equiv) ((parEquiv Z.val.1 X.val.1).symm (parEquiv Z.val.1 X.val.1 a))) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨hp, parEquiv Z.val.1 X.val.1 (.inr h.exceptional), ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a, rfl⟩ := (parEquiv Z.val.1 X.val.1).surjective a
    have heattr := congrArg (fun u : ↥(parContext Z.val.1 Y.val.1).current =>
      (parArchive Z.val.1.archive Y.val.1.archive).attributes u.val) (he a)
    refine heattr.trans ((par_attr Z Y ((Equiv.sumCongr (Equiv.refl _) h.equiv) a)).trans
      (Eq.trans ?_ (par_attr Z X a).symm))
    cases a with
    | inl a => rfl
    | inr a =>
      have hne : a ≠ h.exceptional := fun eq => ha (congrArg (fun z => parEquiv Z.val.1 X.val.1 (.inr z)) eq)
      exact h.attributes_other a hne
  · change ((parArchive Z.val.1.archive Y.val.1.archive).attributes _).position =
      ((parArchive Z.val.1.archive X.val.1.archive).attributes _).position
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr, Sum.elim_inr] using h.position_eq
  · change ((parArchive Z.val.1.archive Y.val.1.archive).attributes _).positive =
      ((parArchive Z.val.1.archive X.val.1.archive).attributes _).positive
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr, Sum.elim_inr] using h.positive_eq
  · change ((parArchive Z.val.1.archive Y.val.1.archive).attributes _).source =
      ((parArchive Z.val.1.archive X.val.1.archive).attributes _).source
    simpa only [he, par_attr, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr, Sum.elim_inr] using h.source_eq
  · intro a hr
    obtain ⟨a, rfl⟩ := (parEquiv Z.val.1 X.val.1).surjective a
    have hh := (ParallelComposition.causal_cases _ _ _ _).mp hr; cases a with
    | inl a => exact hh.elim
    | inr a => exact h.no_incoming a hh
private theorem parallel_variant_left_equiv {X Y : B} (h : PreVariant X Y) (Z : B)
    (a : ↥X.val.1.current ⊕ ↥Z.val.1.current) : (parallel_variant_left h Z).equiv (parEquiv X.val.1 Z.val.1 a) =
      parEquiv Y.val.1 Z.val.1 ((Equiv.sumCongr h.equiv (Equiv.refl _)) a) := by
  change parEquiv Y.val.1 Z.val.1 ((Equiv.sumCongr h.equiv (Equiv.refl _)) ((parEquiv X.val.1 Z.val.1).symm (parEquiv X.val.1 Z.val.1 a))) = _
  rw [Equiv.symm_apply_apply]
private theorem parallel_variant_right_equiv {X Y : B} (h : PreVariant X Y) (Z : B)
    (a : ↥Z.val.1.current ⊕ ↥X.val.1.current) : (parallel_variant_right h Z).equiv (parEquiv Z.val.1 X.val.1 a) =
      parEquiv Z.val.1 Y.val.1 ((Equiv.sumCongr (Equiv.refl _) h.equiv) a) := by
  change parEquiv Z.val.1 Y.val.1 ((Equiv.sumCongr (Equiv.refl _) h.equiv) ((parEquiv Z.val.1 X.val.1).symm (parEquiv Z.val.1 X.val.1 a))) = _
  rw [Equiv.symm_apply_apply]
private def shiftAttributes (k : Int) (a : Attributes 3) : Attributes 3 := {a with time := a.time + k}

private def requiredPredicates : List Step → List (Set (Attributes 3))
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
  have hl := neg_abs_le (Z.val.1.archive.attributes e.val).time; unfold currentLowerBound
  omega
private def timeThreshold : List Step → Int
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
    CurrentIsoData (productBalanced X Z) (productBalanced Y Z) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := product_pair h.toCurrentPairData hz
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro a
  obtain ⟨a, rfl⟩ := (generatedCurrentEquiv X.val.1 Z.val.1).surjective a
  dsimp only [productBalanced, product, hp, product_pair, Equiv.trans_apply]; rw [Equiv.symm_apply_apply]
  change (prodArchive Y.val.1 Z.val.1).attributes (generatedMap _ _ (h.equiv a.1, a.2)) =
    (prodArchive X.val.1 Z.val.1).attributes (generatedMap _ _ a)
  rw [prodAttributes, prodAttributes]
  by_cases ha : a.1 = h.exceptional
  · have hx := (ht.trans_le (current_lower_bound Z a.2)).le
    have hy := (ht'.trans_le (current_lower_bound Z a.2)).le; apply Attributes.ext
    · simpa only [generatedAttributes, ha, max_eq_right hx, max_eq_right hy]
    · simp only [generatedAttributes, same_position h a.1]
    · simp only [generatedAttributes, same_positive h a.1]
    · simp only [generatedAttributes, same_source h a.1]
  · simp only [generatedAttributes, h.attributes_other a.1 ha]
private def collapse_right {X Y : B} (h : PreVariant X Y) (Z : B)
    (ht : (X.val.1.archive.attributes h.exceptional.val).time < currentLowerBound Z)
    (ht' : (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < currentLowerBound Z) :
    CurrentIsoData (productBalanced Z X) (productBalanced Z Y) := by
  let hz : CurrentPairData Z Z := ⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  let hp := product_pair hz h.toCurrentPairData
  refine ⟨hp.equiv, ?_, hp.causal_iff, hp.selected_iff⟩
  intro a
  obtain ⟨a, rfl⟩ := (generatedCurrentEquiv Z.val.1 X.val.1).surjective a
  dsimp only [productBalanced, product, hp, product_pair, Equiv.trans_apply]; rw [Equiv.symm_apply_apply]
  change (prodArchive Z.val.1 Y.val.1).attributes (generatedMap _ _ (a.1, h.equiv a.2)) =
    (prodArchive Z.val.1 X.val.1).attributes (generatedMap _ _ a)
  rw [prodAttributes, prodAttributes]
  by_cases ha : a.2 = h.exceptional
  · have hx := (ht.trans_le (current_lower_bound Z a.1)).le
    have hy := (ht'.trans_le (current_lower_bound Z a.1)).le; apply Attributes.ext
    · simpa only [generatedAttributes, ha, max_eq_left hx, max_eq_left hy]
    · simp only [generatedAttributes, same_position h a.2]
    · simp only [generatedAttributes, same_positive h a.2]
    · simp only [generatedAttributes, same_source h a.2]
  · simp only [generatedAttributes, h.attributes_other a.2 ha]
private theorem saturated_runSteps (w : List Step) {X Y : B} (h : PreVariant X Y)
    (ht : (X.val.1.archive.attributes h.exceptional.val).time < timeThreshold w)
    (ht' : (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < timeThreshold w)
    (hs : Saturated h (requiredPredicates w)) : q (runSteps w X).val = q (runSteps w Y).val := by
  induction w generalizing X Y with
  | nil => exact pre_readout_eq h
  | cons f w ih =>
    cases f with
    | productLeft Z => exact temporal_free_readout (collapse_left h Z ht ht') w
    | productRight Z => exact temporal_free_readout (collapse_right h Z ht ht') w
    | unary f =>
      have hm : ∀ Q, f = .causal Q → (mask Y (h.equiv h.exceptional) (sourceAttributeEquiv ⁻¹' Q) ↔
            mask X h.exceptional (sourceAttributeEquiv ⁻¹' Q)) := by
        intro Q hf
        subst f
        constructor
        · intro hy; exact (hs _ (by simp [requiredPredicates]) (mask_nonempty Y _ _ hy)).1
        · intro hx; exact (hs _ (by simp [requiredPredicates]) (mask_nonempty X _ _ hx)).2
      let h' := unary_variant h f hm
      apply ih h'
      · cases f <;> try exact ht
        rename_i k
        change (X.val.1.archive.attributes h.exceptional.val).time + k < timeThreshold w
        change (X.val.1.archive.attributes h.exceptional.val).time < timeThreshold w - k at ht; omega
      · cases f <;> try exact ht'
        rename_i k
        change (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time + k < timeThreshold w
        change (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time < timeThreshold w - k at ht'; omega
      · intro Q hQ hn; cases f with
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
          exact hs (shiftAttributes k ⁻¹' Q) (List.mem_map.mpr ⟨Q, hQ, rfl⟩) hn'
    | parallelLeft Z =>
      let h' := parallel_variant_left h Z
      have he := parallel_variant_left_equiv h Z (.inl h.exceptional)
      have htx := congrArg Attributes.time (par_attr X Z (.inl h.exceptional))
      have hty := (congrArg (fun u : ↥(parContext Y.val.1 Z.val.1).current =>
          ((parArchive Y.val.1.archive Z.val.1.archive).attributes u.val).time) he).trans
        (congrArg Attributes.time (par_attr Y Z (.inl (h.equiv h.exceptional))))
      apply ih h'
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) htx) ht
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) hty) ht'
      · intro Q hQ hn
        obtain ⟨hx, hy⟩ := hs Q hQ hn
        exact ⟨(mask_parallel_left X Z h.exceptional Q).mpr hx,
          Eq.mpr (congrArg (fun e => mask (parallelBalanced Y Z) e Q) he)
            ((mask_parallel_left Y Z (h.equiv h.exceptional) Q).mpr hy)⟩
    | parallelRight Z =>
      let h' := parallel_variant_right h Z
      have he := parallel_variant_right_equiv h Z (.inr h.exceptional)
      have htx := congrArg Attributes.time (par_attr Z X (.inr h.exceptional))
      have hty := (congrArg (fun u : ↥(parContext Z.val.1 Y.val.1).current =>
          ((parArchive Z.val.1.archive Y.val.1.archive).attributes u.val).time) he).trans
        (congrArg Attributes.time (par_attr Z Y (.inr (h.equiv h.exceptional))))
      apply ih h'
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) htx) ht
      · exact Eq.mpr (congrArg (fun n => n < timeThreshold w) hty) ht'
      · intro Q hQ hn
        obtain ⟨hx, hy⟩ := hs Q hQ hn
        exact ⟨(mask_parallel_right Z X h.exceptional Q).mpr hx,
          Eq.mpr (congrArg (fun e => mask (parallelBalanced Z Y) e Q) he)
            ((mask_parallel_right Z Y (h.equiv h.exceptional) Q).mpr hy)⟩

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.SourceTreeEncoding
open TaggedPresentation

abbrev Word := List (Generator nativeSignature)
abbrev Region := Set (Int × (Fin 3 → Int))

def TailAt (R : Region) (c : Int) : Prop := ∀ p t t', t < c → t' < c → ((t, p) ∈ R ↔ (t', p) ∈ R)

def Tail (R : Region) : Prop := ∃ c, TailAt R c

def regionReadout (R : Region) (X : B) : Int := ∑ e ∈ X.val.2.val.filter (fun e =>
    ((X.val.1.archive.attributes e).time, (X.val.1.archive.attributes e).position) ∈ R), contribution X.val.1 e

def QExpressible (R : Region) : Prop := ∃ w : Word, ∀ X : B, ∃ Y : B,
    contextDenote nativeSignature w X = some Y ∧ q Y.val = regionReadout R X

structure TimeVariantData (X Y : B) where
  eventEquiv : X.val.1.Event ≃ Y.val.1.Event
  name_eq : ∀ e, (eventEquiv e).val = e.val
  exceptional : X.val.1.Event
  attributes_other : ∀ e, e ≠ exceptional → Y.val.1.archive.attributes (eventEquiv e) = X.val.1.archive.attributes e
  position_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).position =
    (X.val.1.archive.attributes exceptional).position
  positive_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).positive =
    (X.val.1.archive.attributes exceptional).positive
  source_eq : (Y.val.1.archive.attributes (eventEquiv exceptional)).source =
    (X.val.1.archive.attributes exceptional).source
  causal_iff : ∀ e f, Y.val.1.archive.causal (eventEquiv e) (eventEquiv f) ↔ X.val.1.archive.causal e f
  current_image : X.val.1.current.map eventEquiv.toEmbedding = Y.val.1.current
  selection_image : X.val.2.val.map eventEquiv.toEmbedding = Y.val.2.val
  earlier : ∃ e, e ≠ exceptional ∧
    (X.val.1.archive.attributes e).time < (X.val.1.archive.attributes exceptional).time ∧
    (X.val.1.archive.attributes e).time < (Y.val.1.archive.attributes (eventEquiv exceptional)).time
  later : ∃ e, e ≠ exceptional ∧ (X.val.1.archive.attributes exceptional).time < (X.val.1.archive.attributes e).time ∧
    (Y.val.1.archive.attributes (eventEquiv exceptional)).time < (X.val.1.archive.attributes e).time

def SelectedVariant (X Y : B) (p : Fin 3 → Int) (t t' : Int) : Prop := ∃ h : TimeVariantData X Y,
    X.val.2.val = {h.exceptional} ∧ (X.val.1.archive.attributes h.exceptional).position = p ∧
    (X.val.1.archive.attributes h.exceptional).positive = true ∧ (X.val.1.archive.attributes h.exceptional).time = t ∧
    (Y.val.1.archive.attributes (h.eventEquiv h.exceptional)).time = t'
private abbrev StarNode (m : Nat) := ((Option (Fin m)) × Bool) ⊕ Bool
private def starCode (m : Nat) : StarNode m ↪ HF where
  toFun x := natCode ((Fintype.equivFin (StarNode m)) x).val
  inj' _ _ h := (Fintype.equivFin (StarNode m)).injective (Fin.ext (natCode_inj.mp h))
private def starExceptional (m : Nat) : StarNode m := .inl (none, true)
private def starCurrent (m : Nat) : Finset (StarNode m) := Finset.univ.disjSum ∅
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
  rintro ⟨rfl, i, h⟩; simp [starExceptional] at h
private theorem star_trans {m : Nat} (a b d : StarNode m) :
    starRelation a b → starRelation b d → starRelation a d := by
  rintro ⟨rfl, i, rfl⟩ ⟨h, _⟩; simp [starExceptional] at h
private theorem star_time {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (a b : StarNode m) :
    starRelation a b → (starAttributes v p lo hi t a).time < (starAttributes v p lo hi t b).time := by
  rintro ⟨rfl, i, rfl⟩; exact ht i
private def starContext {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) : Context 3 :=
  contextOf (starCode m) (starAttributes v p lo hi t) starRelation
    star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m)
private theorem star_balanced {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) : ComplementCharge.Balanced (starContext v p lo hi t ht) := by
  refine (charge_map (starCode m) (starAttributes v p lo hi t) starRelation
    star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m) (starCurrent m)).trans ?_
  simp only [starCurrent, Finset.sum_disjSum, Finset.sum_empty, add_zero]
  rw [Fintype.sum_prod_type]; apply Finset.sum_eq_zero
  intro i _; cases i with
  | none => simp [starAttributes]
  | some i => cases h : (v i).positive <;> simp [starAttributes, h]
private def starInput {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) : B :=
  ⟨⟨starContext v p lo hi t ht, selectionOf (starCode m) (starAttributes v p lo hi t) starRelation
      star_irrefl star_trans (star_time v p lo hi t ht) (starCurrent m)
      {starExceptional m} (by simp [starExceptional, starCurrent])⟩, star_balanced v p lo hi t ht⟩
private theorem star_attributes_eq {m : Nat} (v : Fin m → Attributes 3)
    (p : Fin 3 → Int) (lo hi t : Int) (ht : ∀ i, t < (v i).time) (a : StarNode m) :
    (starInput v p lo hi t ht).val.1.archive.attributes (eventEquiv (starCode m) a) = starAttributes v p lo hi t a :=
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
    position_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
    positive_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
    source_eq := by simp [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
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
    dsimp only [eqv]; rw [Equiv.symm_apply_apply]
    cases a with
    | inr b => rfl
    | inl a =>
      rcases a with ⟨i, b⟩
      cases i <;> cases b <;> first | rfl | exact (ha rfl).elim
  · refine ⟨eqv (.inr false), ?_, ?_, ?_⟩
    · intro h
      have he := eqv.injective h; cases he
    · simpa [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes] using hlo.1
    · simpa [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes] using hlo.2
  · refine ⟨eqv (.inr true), ?_, ?_, ?_⟩
    · intro h
      have he := eqv.injective h; cases he
    · simpa [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes] using hhi.1
    · simpa [eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes] using hhi.2
  · exact Finset.map_singleton _ _
private def star_current_variant {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t t' : Int) (ht : ∀ i, t < (v i).time) (ht' : ∀ i, t' < (v i).time) :
    PreVariant (starInput v p lo hi t ht) (starInput v p lo hi t' ht') := by
  let eqv := eventEquiv (starCode m)
  let e : ↥(starInput v p lo hi t ht).val.1.current :=
    ⟨eqv (starExceptional m), by simp [starInput, starContext, contextOf, starCurrent, starExceptional, eqv]⟩
  refine {
    equiv := Equiv.refl _
    causal_iff := fun _ _ => Iff.rfl
    selected_iff := fun _ => Iff.rfl
    exceptional := e
    attributes_other := ?_
    position_eq := by simp [e, eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
    positive_eq := by simp [e, eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
    source_eq := by
      simp [e, eqv, starInput, starContext, contextOf, archiveOf, starExceptional, starAttributes]
    no_incoming := ?_ }
  · intro a ha
    obtain ⟨b, hb⟩ := eqv.surjective a.val
    have hb' : b ≠ starExceptional m := by
      intro h; apply ha
      apply Subtype.ext; exact hb.symm.trans (congrArg eqv h)
    change starAttributes v p lo hi t' (eqv.symm a.val) = starAttributes v p lo hi t (eqv.symm a.val)
    rw [← hb, Equiv.symm_apply_apply]; cases b with
    | inr b => rfl
    | inl b =>
      rcases b with ⟨i, b⟩
      cases i <;> cases b <;> first | rfl | exact (hb' rfl).elim
  · intro a; change ¬ starRelation (eqv.symm a.val) (eqv.symm (eqv (starExceptional m)))
    rw [Equiv.symm_apply_apply]; rintro ⟨_, i, h⟩
    simp [starExceptional] at h
private def starPoint {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (i : Option (Fin m)) (b : Bool) :
    ↥(starInput v p lo hi t ht).val.1.current := ⟨eventEquiv (starCode m) (.inl (i, b)), by
    simp [starInput, starContext, contextOf, starCurrent]⟩
private theorem star_hit {m : Nat} (v : Fin m → Attributes 3) (p : Fin 3 → Int)
    (lo hi t : Int) (ht : ∀ i, t < (v i).time) (i : Fin m) (Q : Set (Attributes 3)) (hv : v i ∈ Q) :
    mask (starInput v p lo hi t ht) (starPoint v p lo hi t ht none true) Q := by
  refine ⟨starPoint v p lo hi t ht (some i) true, ?_, Or.inr ?_⟩
  · simpa only [starPoint, starInput, starContext, contextOf, archiveOf,
      Equiv.symm_apply_apply, starAttributes] using hv
  · simpa only [starInput, starContext, contextOf, archiveOf, starPoint,
      Equiv.symm_apply_apply, starExceptional] using
        (show starRelation (starExceptional m) (.inl (some i, true)) from ⟨rfl, i, rfl⟩)

private theorem finite_joint_input (Qs : List (Set (Attributes 3))) (K : Int) :
    ∃ c : Int, c ≤ K ∧ ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c → ∃ X Y : B, SelectedVariant X Y p t t' ∧
        ∃ h : PreVariant X Y, (X.val.1.archive.attributes h.exceptional.val).time = t ∧
          (Y.val.1.archive.attributes (h.equiv h.exceptional).val).time = t' ∧ Saturated h Qs := by
  let v (i : Fin Qs.length) : Attributes 3 := if h : (Qs.get i).Nonempty then Classical.choose h
    else ⟨0, fun _ => 0, true, FreeMagma.of 0⟩
  have hv (i : Fin Qs.length) (h : (Qs.get i).Nonempty) : v i ∈ Qs.get i := by
    simp only [v, dif_pos h]
    exact Classical.choose_spec h
  obtain ⟨l, lower⟩ := Finite.exists_ge (fun i : Fin Qs.length => (v i).time)
  let c := min K l
  refine ⟨c, min_le_left _ _, fun p t t' ht ht' => ?_⟩
  have htv (i) : t < (v i).time := ht.trans_le ((min_le_right K l).trans (lower i))
  have ht'v (i) : t' < (v i).time := ht'.trans_le ((min_le_right K l).trans (lower i))
  let lo := min t t' - 1
  let hi := max t t' + 1
  have hlo : lo < t ∧ lo < t' := by dsimp only [lo]; omega
  have hhi : t < hi ∧ t' < hi := by dsimp only [hi]; omega
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

private theorem normalize_word (w : Word) (ht : ∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) :
    ∃ w' : Word, WordTemporalFree w' ∧
      ∀ X, contextDenote nativeSignature w X = contextDenote nativeSignature w' X := by
  have hc : DiagonalTotal (wordToCopy w) := by
    intro X; simpa only [word_to_copy_denote] using ht X
  obtain ⟨_, _, _, N, _, _, he, _, ws, hw, hd, _, _⟩ := total_copy_normalization (wordToCopy w) (by decide) hc
  refine ⟨ws 0, (hw 0).1, fun X => ?_⟩
  have hv : sliceAssignment (0 : Fin 1) X = fun _ => X := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [hd, hv]; exact (word_to_copy_denote w X).symm.trans (he X)

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
    regionReadout R X = (if (t, p) ∈ R then 1 else 0) ∧ regionReadout R Y = (if (t', p) ∈ R then 1 else 0) := by
  obtain ⟨v, selected, pos, positive, time, time'⟩ := pair
  have selected' : Y.val.2.val = {v.eventEquiv v.exceptional} := by
    rw [← v.selection_image, selected, Finset.map_singleton]
    rfl
  have pos' := v.position_eq.trans pos
  have positive' := v.positive_eq.trans positive
  constructor
  · unfold regionReadout; rw [selected, Finset.sum_filter, Finset.sum_singleton]
    simp only [time, pos, contribution, positive, ite_true]
  · unfold regionReadout; rw [selected', Finset.sum_filter, Finset.sum_singleton]
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
  have values : regionReadout R X = regionReadout R Y := hU.symm.trans ((Option.some.inj same).trans hV)
  obtain ⟨hX, hY⟩ := selected_region_values R X Y p t t' pair
  rw [hX, hY] at values
  split_ifs at values <;> simp_all

abbrev unitBalanced : B := ComplementFibers.balancedSection 3 1

def tailCausalPredicate (R : Region) (k : Int) : Set SourceTimedAttribute :=
  {a | k + 1 ≤ a.2.2.2 ∧ (a.2.2.2 - 1, a.1) ∈ R}

def tailConstruction (R : Region) (k : Int) (X : B) : B := unary (.causal (tailCausalPredicate R k))
    (productBalanced X (unary (.shift k) unitBalanced))

private theorem generated_mask (X Z : B) (Q : Set SourceTimedAttribute) (p : Parents X.val.1 Z.val.1) :
    (∃ d ∈ (prodContext X.val.1 Z.val.1).current,
      sourceAttributeEquiv ((prodArchive X.val.1 Z.val.1).attributes d) ∈ Q ∧
        (generatedMap X.val.1 Z.val.1 p = d ∨ (prodArchive X.val.1 Z.val.1).causal
            (generatedMap X.val.1 Z.val.1 p) d)) ↔
      sourceAttributeEquiv (generatedAttributes X.val.1 Z.val.1 p) ∈ Q := by
  constructor
  · rintro ⟨d, _, hQ, he | hc⟩
    · subst d
      simpa only [prodAttributes] using hQ
    · obtain ⟨d, rfl⟩ := (prodEventEquiv X.val.1 Z.val.1).surjective d
      exact (ProductPaths.generated_no_path X.val.1 Z.val.1 p d ((causal_equiv _ _ _ _).mp hc)).elim
  · intro hQ
    exact ⟨generatedMap _ _ p, generated_mem_current _ _ p, by simpa only [prodAttributes] using hQ, Or.inl rfl⟩
private theorem filtered_product_readout (X Z : B) (Q : Set SourceTimedAttribute) :
    q (unary (.causal Q) (productBalanced X Z)).val = ∑ p ∈ selectedParents X.val.2 ×ˢ selectedParents Z.val.2,
        if sourceAttributeEquiv (generatedAttributes X.val.1 Z.val.1 p) ∈ Q
        then contribution X.val.1 p.1.val * contribution Z.val.1 p.2.val else 0 := by
  let P : (prodArchive X.val.1 Z.val.1).Event → Prop := fun e =>
    ∃ d ∈ (prodContext X.val.1 Z.val.1).current,
      sourceAttributeEquiv ((prodArchive X.val.1 Z.val.1).attributes d) ∈ Q ∧
        (e = d ∨ (prodArchive X.val.1 Z.val.1).causal e d)
  change (∑ e ∈ @Finset.filter _ P (fun e => Classical.propDecidable (P e))
    (prodSelection X.val.2 Z.val.2).val, contribution (prodContext X.val.1 Z.val.1) e) = _
  rw [Finset.sum_filter]; change (∑ e ∈ (selectedParents X.val.2 ×ˢ selectedParents Z.val.2).map (generatedMap _ _),
      @ite Int (P e) (Classical.propDecidable (P e)) (contribution (prodContext X.val.1 Z.val.1) e) 0) = _
  rw [Finset.sum_map]; apply Finset.sum_congr rfl
  intro p _
  have hm := generated_mask X Z Q p; change P (generatedMap _ _ p) ↔ _ at hm
  simp only [hm]
  split_ifs
  · have ha := prodAttributes X.val.1 Z.val.1 p
    exact (congrArg (fun a : Attributes 3 => if a.positive then (1 : Int) else -1) ha).trans
      (generated_contribution X.val.1 Z.val.1 p)
  · rfl
private theorem shifted_unit_selected (k : Int) : ∃ u : ↥(unary (.shift k) unitBalanced).val.1.current,
      selectedParents (unary (.shift k) unitBalanced).val.2 = {u} ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).time = k ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).position = (fun _ => 0) ∧
      ((unary (.shift k) unitBalanced).val.1.archive.attributes u.val).positive = true := by
  have hc : unitBalanced.val.2.val.card = 1 := by exact IntegerRepresentatives.representative_selected_card 3 1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have ham : a ∈ unitBalanced.val.2.val := by simp [ha]
  let u : ↥(unary (.shift k) unitBalanced).val.1.current := ⟨a, unitBalanced.val.2.property ham⟩
  have hs : selectedParents (unary (.shift k) unitBalanced).val.2 = {u} := by
    ext e; simp only [mem_selectedParents, Finset.mem_singleton]
    change e.val ∈ unitBalanced.val.2.val ↔ e = u; rw [ha, Finset.mem_singleton]
    exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  have hq : q unitBalanced.val = 1 := IntegerRepresentatives.representative_readout 3 1
  have hp : (unitBalanced.val.1.archive.attributes a).positive = true := by
    change (∑ e ∈ unitBalanced.val.2.val, contribution unitBalanced.val.1 e) = 1 at hq
    rw [ha, Finset.sum_singleton] at hq; unfold contribution at hq
    cases he : (unitBalanced.val.1.archive.attributes a).positive <;> simp_all
  refine ⟨u, hs, ?_, rfl, hp⟩
  change 0 + k = k; omega

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
  [⟨.inr .product, 0, fun _ => unary (.shift k) unitBalanced⟩, ⟨.inl (.causal (tailCausalPredicate R k)), 0, fun j =>
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
