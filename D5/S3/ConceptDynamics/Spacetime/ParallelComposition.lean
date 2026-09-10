/- GID: D5/S3/ConceptDynamics/Spacetime/ParallelComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ParallelComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parallel composition tags complete archives and adds signed readouts. -/

import D5.S3.ConceptDynamics.Spacetime.TaggedPresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.ParallelComposition

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge TaggedPresentation
noncomputable section

local instance : DecidableEq HF := Classical.decEq _

variable {d : Nat}

abbrev Node (a b : Archive d) := a.Event ⊕ b.Event

def eventCode (a b : Archive d) : Node a b → HF
  | .inl e => eventTag 0 e.val
  | .inr f => eventTag 1 f.val

theorem eventCode_injective (a b : Archive d) : Function.Injective (eventCode a b) := by
  intro x y h
  cases x with
  | inl e =>
    cases y with
    | inl f => exact congrArg Sum.inl (Subtype.ext (eventTag_inj.mp h).2)
    | inr f => have hh := (eventTag_inj.mp h).1; simp at hh
  | inr e =>
    cases y with
    | inl f => have hh := (eventTag_inj.mp h).1; simp at hh
    | inr f => exact congrArg Sum.inr (Subtype.ext (eventTag_inj.mp h).2)

def code (a b : Archive d) : Node a b ↪ HF := ⟨eventCode a b, eventCode_injective a b⟩

def attributes (a b : Archive d) : Node a b → Attributes d
  | .inl e => a.attributes e
  | .inr f => b.attributes f

def internal (a b : Archive d) : Node a b → Node a b → Prop
  | .inl e, .inl f => a.causal e f
  | .inr e, .inr f => b.causal e f
  | _, _ => False

theorem internal_irrefl (a b : Archive d) (x : Node a b) : ¬ internal a b x x := by
  cases x with
  | inl e => exact a.irrefl e
  | inr e => exact b.irrefl e

theorem internal_trans (a b : Archive d) (x y z : Node a b) :
    internal a b x y → internal a b y z → internal a b x z := by
  cases x <;> cases y <;> cases z <;> simp only [internal]
  all_goals first | exact a.trans _ _ _ | exact b.trans _ _ _ | tauto

theorem internal_time (a b : Archive d) (x y : Node a b) :
    internal a b x y → (attributes a b x).time < (attributes a b y).time := by
  cases x <;> cases y <;> simp only [internal, attributes]
  all_goals first | exact a.time_lt _ _ | exact b.time_lt _ _ | tauto

def archive (a b : Archive d) : Archive d :=
  archiveOf (code a b) (attributes a b) (internal a b)
    (internal_irrefl a b) (internal_trans a b) (internal_time a b)

def equiv (a b : Archive d) : Node a b ≃ (archive a b).Event := eventEquiv (code a b)

def left (a b : Archive d) : a.Event ↪ (archive a b).Event :=
  Function.Embedding.inl.trans (equiv a b).toEmbedding

def right (a b : Archive d) : b.Event ↪ (archive a b).Event :=
  Function.Embedding.inr.trans (equiv a b).toEmbedding

@[simp] theorem left_val (a b : Archive d) (e : a.Event) :
    (left a b e).val = eventTag 0 e.val := rfl

@[simp] theorem right_val (a b : Archive d) (e : b.Event) :
    (right a b e).val = eventTag 1 e.val := rfl

@[simp] theorem attributes_left (a b : Archive d) (e : a.Event) :
    (archive a b).attributes (left a b e) = a.attributes e := by
  simp [archive, archiveOf, left, equiv, Function.Embedding.trans_apply, attributes]

@[simp] theorem attributes_right (a b : Archive d) (e : b.Event) :
    (archive a b).attributes (right a b e) = b.attributes e := by
  simp [archive, archiveOf, right, equiv, Function.Embedding.trans_apply, attributes]

@[simp] theorem causal_left (a b : Archive d) (e f : a.Event) :
    (archive a b).causal (left a b e) (left a b f) ↔ a.causal e f := by
  simp [archive, archiveOf, left, equiv, Function.Embedding.trans_apply, internal]

@[simp] theorem causal_right (a b : Archive d) (e f : b.Event) :
    (archive a b).causal (right a b e) (right a b f) ↔ b.causal e f := by
  simp [archive, archiveOf, right, equiv, Function.Embedding.trans_apply, internal]

theorem causal_cases (a b : Archive d) (x y : Node a b) :
    (archive a b).causal (equiv a b x) (equiv a b y) ↔ internal a b x y := by
  simp [archive, archiveOf, equiv]

def embeddingLeft (a b : Archive d) : ArchiveEmbedding a (archive a b) :=
  ⟨left a b, attributes_left a b, causal_left a b⟩

def embeddingRight (a b : Archive d) : ArchiveEmbedding b (archive a b) :=
  ⟨right a b, attributes_right a b, causal_right a b⟩

/-- Membership recovers the original component, including overlapping or empty inputs. -/
theorem mem_events (a b : Archive d) (v : HF) :
    v ∈ (archive a b).events ↔
      (∃ e ∈ a.events, eventTag 0 e = v) ∨ (∃ f ∈ b.events, eventTag 1 f = v) := by
  simp only [archive, archiveOf, events, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e | f, rfl⟩
    · exact Or.inl ⟨e.val, e.property, rfl⟩
    · exact Or.inr ⟨f.val, f.property, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact ⟨.inl ⟨e, he⟩, rfl⟩
    · exact ⟨.inr ⟨f, hf⟩, rfl⟩

theorem events_eq (a b : Archive d) :
    (archive a b).events = a.events.image (eventTag 0) ∪ b.events.image (eventTag 1) := by
  ext v; simp only [mem_events, Finset.mem_union, Finset.mem_image]

@[simp] theorem recover_left (a b : Archive d) (v : HF) :
    eventTag 0 v ∈ (archive a b).events ↔ v ∈ a.events := by
  simp [mem_events, eventTag_inj]

@[simp] theorem recover_right (a b : Archive d) (v : HF) :
    eventTag 1 v ∈ (archive a b).events ↔ v ∈ b.events := by
  simp [mem_events, eventTag_inj]

theorem archive_card (a b : Archive d) :
    (archive a b).events.card = a.events.card + b.events.card := by
  simp [archive, archiveOf, events, Node]

def context (c e : Context d) : Context d :=
  contextOf (code c.archive e.archive) (attributes c.archive e.archive)
    (internal c.archive e.archive) (internal_irrefl c.archive e.archive)
    (internal_trans c.archive e.archive) (internal_time c.archive e.archive)
    (c.current.disjSum e.current)

def selection {c e : Context d} (a : Selection c) (b : Selection e) :
    Selection (context c e) :=
  selectionOf _ _ _ _ _ _ _ (a.val.disjSum b.val) (Finset.disjSum_mono a.property b.property)

def parallel (x y : Rich d) : Rich d := ⟨context x.1 y.1, selection x.2 y.2⟩

theorem current_eq (c e : Context d) :
    (context c e).current = c.current.map (left c.archive e.archive) ∪
      e.current.map (right c.archive e.archive) := by
  simpa only [context, contextOf, left, right, equiv, archive, archiveOf,
    Finset.disjUnion_eq_union] using
    (Finset.map_disjSum (s := c.current) (t := e.current) (equiv _ _).toEmbedding)

theorem selection_eq {c e : Context d} (a : Selection c) (b : Selection e) :
    (selection a b).val = a.val.map (left c.archive e.archive) ∪
      b.val.map (right c.archive e.archive) := by
  simpa only [selection, selectionOf, context, contextOf, left, right, equiv,
    archive, archiveOf, Finset.disjUnion_eq_union] using
    (Finset.map_disjSum (s := a.val) (t := b.val) (equiv _ _).toEmbedding)

theorem current_card (c e : Context d) :
    (context c e).current.card = c.current.card + e.current.card := by
  change ((c.current.disjSum e.current).map _).card = _
  rw [Finset.card_map, Finset.card_disjSum]

theorem selection_card {c e : Context d} (a : Selection c) (b : Selection e) :
    (selection a b).val.card = a.val.card + b.val.card := by
  change ((a.val.disjSum b.val).map _).card = _
  rw [Finset.card_map, Finset.card_disjSum]

theorem charge_disjSum (c e : Context d) (s : Finset c.Event) (t : Finset e.Event) :
    charge (context c e) ((s.disjSum t).map (equiv c.archive e.archive).toEmbedding) =
      charge c s + charge e t := by
  change charge (contextOf _ _ _ _ _ _ _) ((s.disjSum t).map (eventEquiv _).toEmbedding) = _
  rw [TaggedPresentation.charge_map]
  simp [Finset.sum_disjSum, attributes, charge, contribution]

theorem q_parallel (x y : Rich d) : q (parallel x y) = q x + q y :=
  charge_disjSum x.1 y.1 x.2.val y.2.val

theorem background_parallel (c e : Context d) :
    background (context c e) = background c + background e :=
  charge_disjSum c e c.current e.current

theorem balanced_parallel {c e : Context d} (hc : Balanced c) (he : Balanced e) :
    Balanced (context c e) := by
  change background (context c e) = 0
  rw [background_parallel, hc, he, add_zero]

def parallelBalanced (x y : BalancedRich d) : BalancedRich d :=
  ⟨parallel x.val y.val, balanced_parallel x.property y.property⟩

end
end D5.S3.ConceptDynamics.Spacetime.ParallelComposition
