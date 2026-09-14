/- GID: D5/S3/ConceptDynamics/Spacetime/CoarseObservation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/CoarseObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Spacetime/CoarseObservation.global_balance_forces_local_balance; result=D5/S3/ConceptDynamics/Spacetime/CoarseObservation.not_global_balance_forces_local_balance; claim=D5/S3/ConceptDynamics/Spacetime/CoarseObservation.global_balance_forces_local_balance
   digest: Native finite observations retain background and selected charges through complement, parallel composition and generated products. -/

import D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
import D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
import D5.S3.Entropy.Forgetting.PushforwardComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.CoarseObservation

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.SourceTreeEncoding
open D5.S0.History.Spacetime.HFEncoding
open ComplementCharge ProductNodes
noncomputable section
open Classical

variable {B D K : Type*}

/-- A fiber consists of actual selected events, with its bin map defined only on current events. -/
def binFiber {c : Context 3} (a : Selection c) (f : ↥c.current → B) (b : B) :
    Finset c.Event :=
  ((selectedParents a).filter (fun e => f e = b)).map (Function.Embedding.subtype _)

def binCharge {c : Context 3} (a : Selection c) (f : ↥c.current → B) : B → Int :=
  fun b => charge c (binFiber a f b)

def backgroundBins (c : Context 3) (f : ↥c.current → B) : B → Int :=
  binCharge (fullSelection c) f

def selectedBins (x : Rich 3) (f : ↥x.1.current → B) : B → Int := binCharge x.2 f

/-- The output is two integer arrays on the entire B, with no induced causal-history structure. -/
def observe (x : Rich 3) (f : ↥x.1.current → B) : (B → Int) × (B → Int) :=
  (backgroundBins x.1 f, selectedBins x f)

def pushforward [Fintype B] (g : B → D) (z : B → Int) : D → Int :=
  fun d => ∑ b, if g b = d then z b else 0

private theorem binCharge_sum {c : Context 3} (a : Selection c)
    (f : ↥c.current → B) (b : B) :
    binCharge a f b = ∑ e ∈ (selectedParents a).filter (fun e => f e = b),
      contribution c e.val := by
  simp [binCharge, binFiber, charge]

private theorem full_parents (c : Context 3) : selectedParents (fullSelection c) = Finset.univ := by
  ext e
  simp [fullSelection, e.property]

private theorem binCharge_total [Fintype B] {c : Context 3} (a : Selection c)
    (f : ↥c.current → B) : (∑ b, binCharge a f b) = readout a := by
  simp_rw [binCharge_sum]
  calc
    _ = ∑ e ∈ selectedParents a, contribution c e.val :=
      Finset.sum_fiberwise (selectedParents a) f (fun e => contribution c e.val)
    _ = readout a := sum_selectedParents a (contribution c)

/-- Finite fiber summation includes unhit and zero-charge bins. -/
theorem sum_backgroundBins [Fintype B] (c : Context 3) (f : ↥c.current → B) :
    (∑ b, backgroundBins c f b) = background c := binCharge_total (fullSelection c) f

theorem sum_selectedBins [Fintype B] (x : Rich 3) (f : ↥x.1.current → B) :
    (∑ b, selectedBins x f b) = q x := binCharge_total x.2 f

/-- The literal selection complement has affine, rather than unconditional negative, charge. -/
theorem observe_complement (x : Rich 3) (f : ↥x.1.current → B) :
    observe (complementRich x) f =
      (backgroundBins x.1 f, backgroundBins x.1 f - selectedBins x f) := by
  refine Prod.ext rfl ?_
  funext b
  change binCharge (complement x.2) f b = binCharge (fullSelection x.1) f b - binCharge x.2 f b
  simp_rw [binCharge_sum]
  have hf : (selectedParents (complement x.2)).filter (fun e => f e = b) =
      ((selectedParents (fullSelection x.1)).filter (fun e => f e = b)) \
        ((selectedParents x.2).filter (fun e => f e = b)) := by
    ext e
    simp [complement, fullSelection, e.property]
    tauto
  rw [hf]
  apply Finset.sum_sdiff_eq_sub
  exact Finset.filter_subset_filter (fun e => f e = b) (by rw [full_parents]; exact Finset.subset_univ _)

/-- The frozen integer-compatible indicator owner supplies composition directly. -/
theorem pushforward_comp [Fintype B] [Fintype D] (g : B → D) (h : D → K) (z : B → Int) :
    pushforward (h ∘ g) z = pushforward h (pushforward g z) := by
  funext k
  exact (D5.S3.Entropy.Forgetting.PushforwardComposition.sum_indicator_comp z g h k).symm

private theorem binCharge_as_pushforward {c : Context 3} (a : Selection c)
    (f : ↥c.current → B) :
    binCharge a f = pushforward f
      (fun e => if e ∈ selectedParents a then contribution c e.val else 0) := by
  funext b
  rw [binCharge_sum]
  simp only [Finset.sum_filter, pushforward]
  calc
    _ = ∑ e ∈ selectedParents a,
        if f e = b then (if e ∈ selectedParents a then contribution c e.val else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [he, ite_true]
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (by
      intro e _ he
      simp only [he, ite_false, ite_self])

private theorem binCharge_pushforward [Fintype B] {c : Context 3} (a : Selection c)
    (f : ↥c.current → B) (g : B → D) :
    binCharge a (g ∘ f) = pushforward g (binCharge a f) := by
  rw [binCharge_as_pushforward, pushforward_comp, binCharge_as_pushforward]

theorem observe_coarsen [Fintype B] (x : Rich 3) (f : ↥x.1.current → B) (g : B → D) :
    observe x (g ∘ f) = (pushforward g (backgroundBins x.1 f),
      pushforward g (selectedBins x f)) := by
  exact Prod.ext (binCharge_pushforward (fullSelection x.1) f g)
    (binCharge_pushforward x.2 f g)

private def generatedCurrentEquiv (c e : Context 3) :
    Parents c e ≃ ↥(GeneratedProduct.context c e).current :=
  (Equiv.subtypeUnivEquiv (fun p : Parents c e => Finset.mem_univ p)).symm.trans
    (Finset.equivMap (GeneratedProduct.generatedMap c e) Finset.univ)

/-- Invert only the new-current image; no bin is assigned to either old archive. -/
def productBin {c e : Context 3} (f : ↥c.current → B) (g : ↥e.current → D) :
    ↥(GeneratedProduct.context c e).current → B × D :=
  fun x => (f ((generatedCurrentEquiv c e).symm x).1,
    g ((generatedCurrentEquiv c e).symm x).2)

private theorem generated_selected_parents {c e : Context 3} (a : Selection c) (s : Selection e) :
    selectedParents (GeneratedProduct.selection a s) =
      (selectedParents a ×ˢ selectedParents s).map (generatedCurrentEquiv c e).toEmbedding := by
  apply Finset.ext
  intro x
  obtain ⟨p, rfl⟩ := (generatedCurrentEquiv c e).surjective x
  simp only [mem_selectedParents, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    Finset.mem_product]
  change GeneratedProduct.generatedMap c e p ∈ (GeneratedProduct.selection a s).val ↔ _
  simp

/-- The native selected bin fiber is exactly the ordered Cartesian product of the two input fibers. -/
theorem generated_selected_bin_fiber {c e : Context 3} (a : Selection c) (s : Selection e)
    (f : ↥c.current → B) (g : ↥e.current → D) (b : B) (d : D) :
    binFiber (GeneratedProduct.selection a s) (productBin f g) (b, d) =
      (((selectedParents a).filter (fun p => f p = b)) ×ˢ
        ((selectedParents s).filter (fun p => g p = d))).map (GeneratedProduct.generatedMap c e) := by
  unfold binFiber
  simp only [generated_selected_parents, Finset.filter_map, Finset.map_map]
  simp only [Function.comp_def, Equiv.toEmbedding_apply, productBin,
    Equiv.symm_apply_apply, Prod.mk.injEq]
  change Finset.map (GeneratedProduct.generatedMap c e) _ = _
  exact congrArg (Finset.map (GeneratedProduct.generatedMap c e))
    (Finset.filter_product (fun p => f p = b) (fun p => g p = d))

private theorem product_selected_charge {c e : Context 3} (a : Selection c) (s : Selection e)
    (f : ↥c.current → B) (g : ↥e.current → D) (b : B) (d : D) :
    binCharge (GeneratedProduct.selection a s) (productBin f g) (b, d) =
      binCharge a f b * binCharge s g d := by
  unfold binCharge
  rw [generated_selected_bin_fiber, GeneratedProduct.charge_generated, Finset.sum_product]
  simp only [charge, binFiber, Finset.sum_map, Function.Embedding.subtype_apply]
  exact (Finset.sum_mul_sum _ _ _ _).symm

/-- Both arrays are computed on the actual product current and selection. -/
theorem product_bin_charges (x y : Rich 3) (f : ↥x.1.current → B) (g : ↥y.1.current → D) :
    observe (GeneratedProduct.product x y) (productBin f g) =
      ((fun p => backgroundBins x.1 f p.1 * backgroundBins y.1 g p.2),
        (fun p => selectedBins x f p.1 * selectedBins y g p.2)) := by
  have hfull : fullSelection (GeneratedProduct.context x.1 y.1) =
      GeneratedProduct.selection (fullSelection x.1) (fullSelection y.1) := by
    apply Subtype.ext
    change Finset.univ.map _ = (selectedParents (fullSelection x.1) ×ˢ
      selectedParents (fullSelection y.1)).map _
    rw [full_parents, full_parents, Finset.univ_product_univ]
  apply Prod.ext
  · funext p
    change binCharge (fullSelection (GeneratedProduct.context x.1 y.1)) (productBin f g) p = _
    rw [hfull]
    exact product_selected_charge _ _ _ _ _ _
  · funext p
    exact product_selected_charge _ _ _ _ _ _

/-- Arbitrary merging consumes the native product fiber equation before pushing either array. -/
theorem product_coarsened_charges [Fintype B] [Fintype D] (x y : Rich 3)
    (f : ↥x.1.current → B) (g : ↥y.1.current → D) (h : B × D → K) :
    observe (GeneratedProduct.product x y) (h ∘ productBin f g) =
      (pushforward h (fun p => backgroundBins x.1 f p.1 * backgroundBins y.1 g p.2),
        pushforward h (fun p => selectedBins x f p.1 * selectedBins y g p.2)) := by
  rw [observe_coarsen]
  have hp := product_bin_charges x y f g
  exact Prod.ext (congrArg (pushforward h) (congrArg Prod.fst hp))
    (congrArg (pushforward h) (congrArg Prod.snd hp))

private def parallelCurrentEquiv (c e : Context 3) :
    (↥c.current ⊕ ↥e.current) ≃ ↥(ParallelComposition.context c e).current :=
  Equiv.ofBijective
    (fun p => ⟨ParallelComposition.equiv c.archive e.archive
      (Sum.map Subtype.val Subtype.val p), by
        change _ ∈ (c.current.disjSum e.current).map
          (ParallelComposition.equiv c.archive e.archive).toEmbedding
        apply Finset.mem_map.mpr
        refine ⟨Sum.map Subtype.val Subtype.val p, ?_, rfl⟩
        cases p <;> simp [Subtype.property]⟩)
    ⟨by
      intro p q hp
      have h := (ParallelComposition.equiv c.archive e.archive).injective
        (congrArg Subtype.val hp)
      cases p <;> cases q <;> simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq,
        Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
      all_goals exact Subtype.ext h,
    by
      rintro ⟨v, hv⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hv
      cases p with
      | inl a => exact ⟨.inl ⟨a, Finset.inl_mem_disjSum.mp hp⟩, rfl⟩
      | inr b => exact ⟨.inr ⟨b, Finset.inr_mem_disjSum.mp hp⟩, rfl⟩⟩

/-- Tagged bins on the actual tagged current; archived events are never extended by a default. -/
def parallelBin {c e : Context 3} (f : ↥c.current → B) (g : ↥e.current → D) :
    ↥(ParallelComposition.context c e).current → B ⊕ D :=
  fun p => Sum.map f g ((parallelCurrentEquiv c e).symm p)

private theorem parallel_selected_parents {c e : Context 3} (a : Selection c) (s : Selection e) :
    selectedParents (ParallelComposition.selection a s) =
      ((selectedParents a).disjSum (selectedParents s)).map
        (parallelCurrentEquiv c e).toEmbedding := by
  ext x
  obtain ⟨p, rfl⟩ := (parallelCurrentEquiv c e).surjective x
  simp only [mem_selectedParents, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  cases p with
  | inl p =>
    change ParallelComposition.equiv c.archive e.archive (Sum.inl p.val) ∈
      (a.val.disjSum s.val).map (ParallelComposition.equiv c.archive e.archive).toEmbedding ↔ _
    simp [mem_selectedParents]
  | inr p =>
    change ParallelComposition.equiv c.archive e.archive (Sum.inr p.val) ∈
      (a.val.disjSum s.val).map (ParallelComposition.equiv c.archive e.archive).toEmbedding ↔ _
    simp [mem_selectedParents]

private theorem parallel_fiber_left {c e : Context 3} (a : Selection c) (s : Selection e)
    (f : ↥c.current → B) (g : ↥e.current → D) (b : B) :
    binFiber (ParallelComposition.selection a s) (parallelBin f g) (.inl b) =
      ((binFiber a f b).disjSum ∅).map (ParallelComposition.equiv c.archive e.archive).toEmbedding := by
  unfold binFiber
  simp only [parallel_selected_parents, Finset.filter_map, Finset.map_map]
  have hf : @Finset.filter _
      ((fun p => parallelBin f g p = Sum.inl b) ∘ (parallelCurrentEquiv c e).toEmbedding)
      (fun p => Classical.propDecidable _) ((selectedParents a).disjSum (selectedParents s)) =
      (((selectedParents a).filter (fun p => f p = b)).disjSum ∅) := by
    ext p
    cases p <;> simp [parallelBin]
  exact (congrArg (Finset.map ((parallelCurrentEquiv c e).toEmbedding.trans
    (Function.Embedding.subtype _))) hf).trans (by
      simp only [Finset.disjSum_empty, Finset.map_map]
      rfl)

private theorem parallel_fiber_right {c e : Context 3} (a : Selection c) (s : Selection e)
    (f : ↥c.current → B) (g : ↥e.current → D) (d : D) :
    binFiber (ParallelComposition.selection a s) (parallelBin f g) (.inr d) =
      ((∅ : Finset c.Event).disjSum (binFiber s g d)).map (ParallelComposition.equiv c.archive e.archive).toEmbedding := by
  unfold binFiber
  simp only [parallel_selected_parents, Finset.filter_map, Finset.map_map]
  have hf : @Finset.filter _
      ((fun p => parallelBin f g p = Sum.inr d) ∘ (parallelCurrentEquiv c e).toEmbedding)
      (fun p => Classical.propDecidable _) ((selectedParents a).disjSum (selectedParents s)) =
      ((∅ : Finset ↥c.current).disjSum ((selectedParents s).filter (fun p => g p = d))) := by
    ext p
    cases p <;> simp [parallelBin]
  exact (congrArg (Finset.map ((parallelCurrentEquiv c e).toEmbedding.trans
    (Function.Embedding.subtype _))) hf).trans (by
      simp only [Finset.empty_disjSum, Finset.map_map]
      rfl)

private theorem parallel_selected_charge {c e : Context 3} (a : Selection c) (s : Selection e)
    (f : ↥c.current → B) (g : ↥e.current → D) :
    binCharge (ParallelComposition.selection a s) (parallelBin f g) =
      Sum.elim (binCharge a f) (binCharge s g) := by
  funext p
  cases p with
  | inl b =>
    change charge _ (binFiber _ _ _) = _
    rw [parallel_fiber_left, ParallelComposition.charge_disjSum]
    simp [charge, binCharge]
  | inr d =>
    change charge _ (binFiber _ _ _) = _
    rw [parallel_fiber_right, ParallelComposition.charge_disjSum]
    simp [charge, binCharge]

theorem parallel_tagged_charges (x y : Rich 3) (f : ↥x.1.current → B) (g : ↥y.1.current → D) :
    observe (ParallelComposition.parallel x y) (parallelBin f g) =
      (Sum.elim (backgroundBins x.1 f) (backgroundBins y.1 g),
        Sum.elim (selectedBins x f) (selectedBins y g)) := by
  have hf : fullSelection (ParallelComposition.context x.1 y.1) =
      ParallelComposition.selection (fullSelection x.1) (fullSelection y.1) := rfl
  apply Prod.ext
  · change binCharge (fullSelection (ParallelComposition.context x.1 y.1)) (parallelBin f g) = _
    rw [hf]
    exact parallel_selected_charge _ _ _ _
  · exact parallel_selected_charge _ _ _ _

theorem parallel_common_charges [Fintype B] (x y : Rich 3)
    (f : ↥x.1.current → B) (g : ↥y.1.current → B) :
    observe (ParallelComposition.parallel x y) (Sum.elim id id ∘ parallelBin f g) =
      (backgroundBins x.1 f + backgroundBins y.1 g, selectedBins x f + selectedBins y g) := by
  rw [observe_coarsen]
  have hp := parallel_tagged_charges x y f g
  have hw := congrArg (pushforward (Sum.elim id id)) (congrArg Prod.fst hp)
  have hz := congrArg (pushforward (Sum.elim id id)) (congrArg Prod.snd hp)
  apply Prod.ext
  · exact hw.trans (by ext b; simp [pushforward, Fintype.sum_sum_type])
  · exact hz.trans (by ext b; simp [pushforward, Fintype.sum_sum_type])

private def splitCode : Bool ↪ HF where
  toFun b := IntegerRepresentatives.eventName 0 b
  inj' := by
    intro a b h
    have hp : (0, a) = (0, b) :=
      @IntegerRepresentatives.eventName_injective (0, a) (0, b) h
    exact (Prod.mk.inj hp).2

private def splitAttributes (b : Bool) : Attributes 3 where
  time := 0
  position i := if i = 0 then (if b then 0 else 1) else 0
  positive := b
  source := FreeMagma.of (if b then 0 else 1)

private def splitContext : Context 3 :=
  TaggedPresentation.contextOf splitCode splitAttributes (fun _ _ => False)
    (by simp) (by simp) (by simp) Finset.univ

private def splitSelection (s : Finset Bool) : Selection splitContext :=
  TaggedPresentation.selectionOf splitCode splitAttributes (fun _ _ => False)
    (by simp) (by simp) (by simp) Finset.univ s (Finset.subset_univ _)

private def splitRich : Rich 3 := ⟨splitContext, splitSelection {true}⟩

private def splitBin (p : ↥splitContext.current) : Bool :=
  (TaggedPresentation.eventEquiv splitCode).symm p.val

private theorem split_current : splitContext.current = Finset.univ := by
  change Finset.univ.map (TaggedPresentation.eventEquiv splitCode).toEmbedding = Finset.univ
  exact Finset.map_univ_equiv _

private theorem split_fiber (s : Finset Bool) (b : Bool) :
    binFiber (splitSelection s) splitBin b =
      (s.filter (fun i => i = b)).map (TaggedPresentation.eventEquiv splitCode).toEmbedding := by
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp, hpv⟩ := Finset.mem_map.mp hv
    have hp' : p ∈ selectedParents (splitSelection s) ∧ splitBin p = b := by
      simpa only [Finset.mem_filter] using hp
    have hs := (mem_selectedParents (splitSelection s) p).mp hp'.1
    change p.val ∈ s.map (TaggedPresentation.eventEquiv splitCode).toEmbedding at hs
    obtain ⟨i, hi, hei⟩ := Finset.mem_map.mp hs
    have hpi : (TaggedPresentation.eventEquiv splitCode).symm p.val = i :=
      (congrArg (TaggedPresentation.eventEquiv splitCode).symm hei).symm.trans
        ((TaggedPresentation.eventEquiv splitCode).symm_apply_apply i)
    have hib : i = b := hpi.symm.trans hp'.2
    exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hib⟩, hei.trans hpv⟩
  · intro hv
    obtain ⟨i, hi, hiv⟩ := Finset.mem_map.mp hv
    have hi' : i ∈ s ∧ i = b := by simpa only [Finset.mem_filter] using hi
    let p : ↥splitContext.current := ⟨TaggedPresentation.eventEquiv splitCode i, by
      rw [split_current]; exact Finset.mem_univ _⟩
    apply Finset.mem_map.mpr
    refine ⟨p, ?_, hiv⟩
    suffices p ∈ selectedParents (splitSelection s) ∧ splitBin p = b by
      simpa only [Finset.mem_filter] using this
    refine ⟨?_, ((TaggedPresentation.eventEquiv splitCode).symm_apply_apply i).trans hi'.2⟩
    apply (mem_selectedParents (splitSelection s) p).mpr
    exact Finset.mem_map.mpr ⟨i, hi'.1, rfl⟩

private theorem split_charge (s : Finset Bool) (b : Bool) :
    binCharge (splitSelection s) splitBin b =
      ∑ i ∈ s.filter (fun i => i = b), if i then (1 : Int) else -1 := by
  unfold binCharge
  rw [split_fiber]
  exact TaggedPresentation.charge_map splitCode splitAttributes (fun _ _ => False)
    (by simp) (by simp) (by simp) Finset.univ _

/-- The two current events are separated by both leaf source and first spatial coordinate.
The positive bin is true and the negative bin false. -/
theorem two_bin_counterexample :
    ∃ (x : Rich 3) (e : Bool ≃ x.1.Event) (f : ↥x.1.current → Bool),
      x.1.current = Finset.univ ∧ x.2.val = {e true} ∧
      (∀ b, x.1.archive.attributes (e b) =
        { time := 0, position := fun i => if i = 0 then (if b then 0 else 1) else 0,
          positive := b, source := FreeMagma.of (if b then 0 else 1) }) ∧
      (∀ p q, ¬ x.1.archive.causal p q) ∧
      (∀ p, f p = e.symm p.val) ∧ Balanced x.1 ∧
      backgroundBins x.1 f = (fun b => if b then 1 else -1) ∧
      selectedBins x f = (fun b => if b then 1 else 0) ∧
      selectedBins (complementRich x) f = (fun b => if b then 0 else -1) ∧
      selectedBins (complementRich x) f ≠ -selectedBins x f := by
  have hfull : fullSelection splitContext = splitSelection Finset.univ := rfl
  have hw : backgroundBins splitContext splitBin = (fun b => if b then 1 else -1) := by
    funext b
    unfold backgroundBins
    rw [hfull, split_charge]
    cases b <;> simp [Finset.sum_filter]
  have hz : selectedBins splitRich splitBin = (fun b => if b then 1 else 0) := by
    funext b
    change binCharge (splitSelection {true}) splitBin b = _
    rw [split_charge]
    cases b <;> simp [Finset.sum_filter]
  have hc : selectedBins (complementRich splitRich) splitBin = (fun b => if b then 0 else -1) := by
    have h := congrArg Prod.snd (observe_complement splitRich splitBin)
    change selectedBins (complementRich splitRich) splitBin =
      backgroundBins splitContext splitBin - selectedBins splitRich splitBin at h
    rw [h, hw, hz]
    funext b
    cases b <;> norm_num
  refine ⟨splitRich, TaggedPresentation.eventEquiv splitCode, splitBin,
    split_current, ?_, ?_, ?_, ?_, ?_, hw, hz, hc, ?_⟩
  · simp only [splitRich, splitSelection, TaggedPresentation.selectionOf,
      Finset.map_singleton]
    rfl
  · intro b
    exact TaggedPresentation.attributes_eventEquiv splitCode splitAttributes (fun _ _ => False)
      (by simp) (by simp) (by simp) b
  · intro p q h
    exact h
  · intro p
    rfl
  · change background splitContext = 0
    rw [← sum_backgroundBins splitContext splitBin, hw]
    simp
  · rw [hc, hz]
    intro h
    have ht := congrFun h true
    norm_num at ht

/-- Global balance alone need not survive a full-current finite-bin observation. -/
def global_balance_forces_local_balance : Prop :=
  ∀ (B : Type) [Fintype B] (x : Rich 3) (f : ↥x.1.current → B),
    Balanced x.1 → ∀ b, backgroundBins x.1 f b = 0

theorem not_global_balance_forces_local_balance : Not global_balance_forces_local_balance := by
  intro h
  obtain ⟨x, e, f, _, _, _, _, _, hb, hw, _⟩ := two_bin_counterexample
  have ht := h Bool x f hb true
  rw [hw] at ht
  norm_num at ht

end
end D5.S3.ConceptDynamics.Spacetime.CoarseObservation
