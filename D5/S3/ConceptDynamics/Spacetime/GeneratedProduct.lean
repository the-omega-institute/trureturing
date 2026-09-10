/- GID: D5/S3/ConceptDynamics/Spacetime/GeneratedProduct
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/GeneratedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The HF generated product retains archives and multiplies signed readouts. -/

import D5.S3.ConceptDynamics.Spacetime.ProductPaths
import D5.S3.ConceptDynamics.Spacetime.FiniteCausalPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.GeneratedProduct

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.SourceTreeEncoding
open ComplementCharge TaggedPresentation ProductNodes ProductPaths
noncomputable section

local instance : DecidableEq HF := Classical.decEq _
variable {d : Nat}

def archive (c e : Context d) : Archive d :=
  archiveOf (code c e) (attributes c e) (Relation.TransGen (Edge c e))
    (path_irrefl c e) (fun _ _ _ => Relation.TransGen.trans) (fun _ _ => path_time c e)

/-- The typed sum/product is equivalent to the exact finite HF archive. -/
def equiv (c e : Context d) : Node c e ≃ (archive c e).Event := eventEquiv (code c e)

def left (c e : Context d) : c.Event ↪ (archive c e).Event where
  toFun a := equiv c e (oldLeft c e a)
  inj' _ _ h := Sum.inl.inj (Sum.inl.inj ((equiv c e).injective h))

def right (c e : Context d) : e.Event ↪ (archive c e).Event where
  toFun b := equiv c e (oldRight c e b)
  inj' _ _ h := Sum.inr.inj (Sum.inl.inj ((equiv c e).injective h))

def generatedMap (c e : Context d) : Parents c e ↪ (archive c e).Event :=
  Function.Embedding.inr.trans (equiv c e).toEmbedding

@[simp] theorem left_val (c e : Context d) (a : c.Event) :
    (left c e a).val = eventTag 0 a.val := rfl

@[simp] theorem right_val (c e : Context d) (b : e.Event) :
    (right c e b).val = eventTag 1 b.val := rfl

@[simp] theorem generated_val (c e : Context d) (p : Parents c e) :
    (generatedMap c e p).val = eventTag 2 (pair p.1.val.val p.2.val.val) := rfl

@[simp] theorem attributes_left (c e : Context d) (a : c.Event) :
    (archive c e).attributes (left c e a) = c.archive.attributes a := by
  simp [archive, archiveOf, left, equiv]

@[simp] theorem attributes_right (c e : Context d) (b : e.Event) :
    (archive c e).attributes (right c e b) = e.archive.attributes b := by
  simp [archive, archiveOf, right, equiv]

@[simp] theorem attributes_generated (c e : Context d) (p : Parents c e) :
    (archive c e).attributes (generatedMap c e p) = generatedAttributes c e p := by
  simp [archive, archiveOf, generatedMap, equiv, Function.Embedding.trans_apply,
    ProductNodes.attributes]

theorem causal_equiv (c e : Context d) (x y : Node c e) :
    (archive c e).causal (equiv c e x) (equiv c e y) ↔ Relation.TransGen (Edge c e) x y := by
  simp [archive, archiveOf, equiv]

theorem causal_left (c e : Context d) (a b : c.Event) :
    (archive c e).causal (left c e a) (left c e b) ↔ c.archive.causal a b := by
  rw [show left c e a = equiv c e (oldLeft c e a) from rfl,
    show left c e b = equiv c e (oldLeft c e b) from rfl, causal_equiv]
  constructor
  · exact (path_left_iff c e a b).mp
  · intro h
    exact map_old_left_path c e (.single h)

theorem causal_right (c e : Context d) (a b : e.Event) :
    (archive c e).causal (right c e a) (right c e b) ↔ e.archive.causal a b := by
  exact (causal_equiv c e _ _).trans (path_right_iff c e a b)

/-- These embeddings impose no condition on either input's current or selected region. -/
def embeddingLeft (c e : Context d) : ArchiveEmbedding c.archive (archive c e) :=
  ⟨left c e, attributes_left c e, causal_left c e⟩

def embeddingRight (c e : Context d) : ArchiveEmbedding e.archive (archive c e) :=
  ⟨right c e, attributes_right c e, causal_right c e⟩

theorem mem_events (c e : Context d) (v : HF) :
    v ∈ (archive c e).events ↔
      (∃ a ∈ c.archive.events, eventTag 0 a = v) ∨
      (∃ b ∈ e.archive.events, eventTag 1 b = v) ∨
      ∃ p : Parents c e, eventTag 2 (pair p.1.val.val p.2.val.val) = v := by
  simp only [archive, archiveOf, events, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨(a | b) | p, rfl⟩
    · exact Or.inl ⟨a.val, a.property, rfl⟩
    · exact Or.inr (Or.inl ⟨b.val, b.property, rfl⟩)
    · exact Or.inr (Or.inr ⟨p, rfl⟩)
  · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨oldLeft c e ⟨a, ha⟩, rfl⟩
    · exact ⟨oldRight c e ⟨b, hb⟩, rfl⟩
    · exact ⟨generated c e p, rfl⟩

theorem events_eq (c e : Context d) :
    (archive c e).events = c.archive.events.image (eventTag 0) ∪
      e.archive.events.image (eventTag 1) ∪
      Finset.univ.image (fun p : Parents c e => eventTag 2 (pair p.1.val.val p.2.val.val)) := by
  ext v
  simp only [mem_events, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, or_assoc]

@[simp] theorem recover_left (c e : Context d) (v : HF) :
    eventTag 0 v ∈ (archive c e).events ↔ v ∈ c.archive.events := by
  simp [mem_events, eventTag_inj]

@[simp] theorem recover_right (c e : Context d) (v : HF) :
    eventTag 1 v ∈ (archive c e).events ↔ v ∈ e.archive.events := by
  simp [mem_events, eventTag_inj]

theorem archive_card (c e : Context d) :
    (archive c e).events.card = c.archive.events.card + e.archive.events.card +
      c.current.card * e.current.card := by
  simp [archive, archiveOf, events, Node, Parents]

/-- Only generated candidate pairs belong to the new current region. -/
def context (c e : Context d) : Context d where
  archive := archive c e
  current := Finset.univ.map (generatedMap c e)

def selection {c e : Context d} (a : Selection c) (b : Selection e) : Selection (context c e) :=
  ⟨(selectedParents a ×ˢ selectedParents b).map (generatedMap c e),
    Finset.map_subset_map.mpr (Finset.subset_univ _)⟩

def product (x y : Rich d) : Rich d := ⟨context x.1 y.1, selection x.2 y.2⟩

@[simp] theorem generated_mem_current (c e : Context d) (p : Parents c e) :
    generatedMap c e p ∈ (context c e).current := by simp [context]

theorem left_not_current (c e : Context d) (a : c.Event) :
    left c e a ∉ (context c e).current := by
  intro h
  obtain ⟨p, _, hp⟩ := Finset.mem_map.mp h
  have hh : Sum.inr p = Sum.inl (Sum.inl a) := (equiv c e).injective hp
  cases hh

theorem right_not_current (c e : Context d) (b : e.Event) :
    right c e b ∉ (context c e).current := by
  intro h
  obtain ⟨p, _, hp⟩ := Finset.mem_map.mp h
  have hh : Sum.inr p = Sum.inl (Sum.inr b) := (equiv c e).injective hp
  cases hh

@[simp] theorem generated_mem_selection {c e : Context d} (a : Selection c) (b : Selection e)
    (p : Parents c e) : generatedMap c e p ∈ (selection a b).val ↔
      p.1.val ∈ a.val ∧ p.2.val ∈ b.val := by
  simp [selection]

theorem current_card (c e : Context d) :
    (context c e).current.card = c.current.card * e.current.card := by
  simp [context, Parents]

theorem charge_generated (c e : Context d) (s : Finset (Parents c e)) :
    charge (context c e) (s.map (generatedMap c e)) =
      ∑ p ∈ s, contribution c p.1.val * contribution e p.2.val := by
  rw [charge, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  unfold contribution
  change (if ((archive c e).attributes (generatedMap c e p)).positive then (1 : Int) else -1) = _
  rw [attributes_generated]
  exact generated_contribution c e p

/-- The selected readout is the actual signed double sum over selected parents. -/
theorem selected_double_sum {c e : Context d} (a : Selection c) (b : Selection e) :
    readout (selection a b) =
      ∑ x ∈ a.val, ∑ y ∈ b.val, contribution c x * contribution e y := by
  change charge (context c e)
    ((selectedParents a ×ˢ selectedParents b).map (generatedMap c e)) = _
  rw [charge_generated, Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum, sum_selectedParents, sum_selectedParents,
    ← Finset.sum_mul_sum]

theorem q_product (x y : Rich d) : q (product x y) = q x * q y := by
  change readout (selection x.2 y.2) = _
  rw [selected_double_sum, ← Finset.sum_mul_sum]
  rfl

theorem sum_current (c : Context d) :
    (∑ a : ↥c.current, contribution c a.val) = background c := by
  exact (Finset.sum_subtype c.current (by simp) (contribution c)).symm

theorem background_double_sum (c e : Context d) :
    background (context c e) =
      ∑ x ∈ c.current, ∑ y ∈ e.current, contribution c x * contribution e y := by
  change charge (context c e) (Finset.univ.map (generatedMap c e)) = _
  rw [charge_generated, Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum, sum_current, sum_current, ← Finset.sum_mul_sum]
  rfl

theorem background_product (c e : Context d) :
    background (context c e) = background c * background e := by
  rw [background_double_sum, ← Finset.sum_mul_sum]
  rfl

theorem balanced_product {c e : Context d} (hc : Balanced c) (he : Balanced e) :
    Balanced (context c e) := by
  change background (context c e) = 0
  rw [background_product, hc, he, mul_zero]

def productBalanced (x y : BalancedRich d) : BalancedRich d :=
  ⟨product x.val y.val, balanced_product x.property y.property⟩

theorem source_code_commutes (c e : Context d) (p : Parents c e) :
    sourceCode ((archive c e).attributes (generatedMap c e p)).source =
      pair (natCode 1) (pair (sourceCode (c.archive.attributes p.1.val).source)
        (sourceCode (e.archive.attributes p.2.val).source)) := by
  rw [attributes_generated]
  exact source_code_generated c e p

theorem hf_tag_commutes (c e : Context d) (p : Parents c e) :
    toZF (generatedMap c e p).val = ZFSet.pair (Ordinal.toZFSet (2 : Ordinal))
      (ZFSet.pair (toZF p.1.val.val) (toZF p.2.val.val)) := hf_code_generated c e p

/-- The generating edges on actual HF archive members. -/
def generator (c e : Context d) (x y : (archive c e).Event) : Prop :=
  Edge c e ((equiv c e).symm x) ((equiv c e).symm y)

@[simp] theorem generator_equiv (c e : Context d) (x y : Node c e) :
    generator c e (equiv c e x) (equiv c e y) ↔ Edge c e x y := by
  simp [generator]

theorem causal_transGen_iff (c e : Context d) (x y : (archive c e).Event) :
    (archive c e).causal x y ↔ Relation.TransGen (generator c e) x y := by
  constructor
  · intro h
    have hh : Relation.TransGen (generator c e)
        (equiv c e ((equiv c e).symm x)) (equiv c e ((equiv c e).symm y)) :=
      Relation.TransGen.lift (equiv c e) (p := generator c e)
        (fun a b hab => by simpa [generator] using hab) _ _ h
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
    exact hh
  · intro h
    exact Relation.TransGen.lift (equiv c e).symm (fun _ _ hh => hh) _ _ h

theorem causal_eq_transGen (c e : Context d) :
    (archive c e).causal = Relation.TransGen (generator c e) :=
  funext fun x => funext fun y => propext (causal_transGen_iff c e x y)

theorem causal_generated_iff (c e : Context d) (x : Node c e) (p : Parents c e) :
    (archive c e).causal (equiv c e x) (generatedMap c e p) ↔
      (∃ a, x = oldLeft c e a ∧ (a = p.1.val ∨ c.archive.causal a p.1.val)) ∨
      (∃ b, x = oldRight c e b ∧ (b = p.2.val ∨ e.archive.causal b p.2.val)) :=
  (causal_equiv c e x (generated c e p)).trans (path_generated_iff c e x p)

theorem causal_iff_bounded_path (c e : Context d) (x y : (archive c e).Event) :
    (archive c e).causal x y ↔ ∃ p : FiniteCausalPaths.PathSeries (generator c e),
      0 < p.length ∧ p.length ≤ (archive c e).events.card - 1 ∧ p.head = x ∧ p.last = y := by
  rw [causal_eq_transGen]
  exact FiniteCausalPaths.transGen_iff_bounded_series (archive c e)
    (fun a b h => (causal_transGen_iff c e a b).mpr (.single h)) x y

theorem causal_graph_finite (c e : Context d) :
    Set.Finite {p : (archive c e).Event × (archive c e).Event | (archive c e).causal p.1 p.2} :=
  Set.toFinite _

/-- Empty opposite current regions erase old selections from the product result. -/
theorem product_eq_of_empty_right {c e : Context d} (h : e.current = ∅)
    (a a' : Selection c) (b b' : Selection e) :
    product ⟨c, a⟩ ⟨e, b⟩ = product ⟨c, a'⟩ ⟨e, b'⟩ := by
  have hb := selectedParents_eq_empty_of_current b h
  have hb' := selectedParents_eq_empty_of_current b' h
  have hs : selection a b = selection a' b' := by
    apply Subtype.ext
    simp [selection, hb, hb']
  exact congrArg (fun s => (⟨context c e, s⟩ : Rich d)) hs

theorem product_eq_of_empty_left {c e : Context d} (h : c.current = ∅)
    (a a' : Selection c) (b b' : Selection e) :
    product ⟨c, a⟩ ⟨e, b⟩ = product ⟨c, a'⟩ ⟨e, b'⟩ := by
  have ha := selectedParents_eq_empty_of_current a h
  have ha' := selectedParents_eq_empty_of_current a' h
  have hs : selection a b = selection a' b' := by
    apply Subtype.ext
    simp [selection, ha, ha']
  exact congrArg (fun s => (⟨context c e, s⟩ : Rich d)) hs

end
end D5.S3.ConceptDynamics.Spacetime.GeneratedProduct
