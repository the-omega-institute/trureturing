/- GID: D5/S3/ConceptDynamics/Spacetime/TemporalComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/TemporalComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Temporal composition preserves absolute times with an exact archive guard. -/

import D5.S3.ConceptDynamics.Spacetime.ParallelComposition
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.TemporalComposition

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge TaggedPresentation
noncomputable section

variable {d : Nat}

/-- The guard quantifies over every archived event, including inactive events. -/
def Guard (a b : Archive d) : Prop :=
  ∀ e : a.Event, ∀ f : b.Event, (a.attributes e).time < (b.attributes f).time

def edge (a b : Archive d) : ParallelComposition.Node a b → ParallelComposition.Node a b → Prop
  | .inl e, .inl f => a.causal e f
  | .inr e, .inr f => b.causal e f
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False

theorem edge_irrefl (a b : Archive d) (x : ParallelComposition.Node a b) : ¬ edge a b x x := by
  cases x with
  | inl e => exact a.irrefl e
  | inr e => exact b.irrefl e

theorem edge_trans (a b : Archive d) (x y z : ParallelComposition.Node a b) :
    edge a b x y → edge a b y z → edge a b x z := by
  cases x <;> cases y <;> cases z <;> simp only [edge]
  all_goals first | exact a.trans _ _ _ | exact b.trans _ _ _ | tauto

theorem temporal_guard_iff (a b : Archive d) :
    (∀ x y, edge a b x y → (ParallelComposition.attributes a b x).time <
      (ParallelComposition.attributes a b y).time) ↔
      Guard a b := by
  constructor
  · intro h e f; exact h (.inl e) (.inr f) True.intro
  · intro h x y
    cases x <;> cases y <;> simp only [edge, ParallelComposition.attributes]
    all_goals first | exact a.time_lt _ _ | exact b.time_lt _ _ | exact fun _ => h _ _ | tauto

/-- The same necessary and sufficient condition on the literal HF event domain. -/
theorem hf_time_condition_iff (a b : Archive d) :
    (∀ x y : ↥(events (ParallelComposition.code a b)),
      edge a b ((eventEquiv (ParallelComposition.code a b)).symm x)
        ((eventEquiv (ParallelComposition.code a b)).symm y) →
      (ParallelComposition.attributes a b
        ((eventEquiv (ParallelComposition.code a b)).symm x)).time <
      (ParallelComposition.attributes a b
        ((eventEquiv (ParallelComposition.code a b)).symm y)).time) ↔ Guard a b := by
  rw [← temporal_guard_iff]
  constructor
  · intro h x y
    simpa only [Equiv.symm_apply_apply] using h (eventEquiv _ x) (eventEquiv _ y)
  · intro h x y; exact h _ _

def archive (a b : Archive d) (h : Guard a b) : Archive d :=
  archiveOf (ParallelComposition.code a b) (ParallelComposition.attributes a b)
    (edge a b) (edge_irrefl a b) (edge_trans a b) ((temporal_guard_iff a b).mpr h)

def equiv (a b : Archive d) (h : Guard a b) :
    ParallelComposition.Node a b ≃ (archive a b h).Event :=
  eventEquiv (ParallelComposition.code a b)

@[simp] theorem equiv_val (a b : Archive d) (h : Guard a b) (x : ParallelComposition.Node a b) :
    (equiv a b h x).val = ParallelComposition.eventCode a b x := rfl

@[simp] theorem attributes_equiv (a b : Archive d) (h : Guard a b)
    (x : ParallelComposition.Node a b) :
    (archive a b h).attributes (equiv a b h x) = ParallelComposition.attributes a b x := by
  simp [archive, equiv, archiveOf]

@[simp] theorem causal_equiv (a b : Archive d) (h : Guard a b)
    (x y : ParallelComposition.Node a b) :
    (archive a b h).causal (equiv a b h x) (equiv a b h y) ↔ edge a b x y := by
  simp [archive, equiv, archiveOf]

theorem events_eq (a b : Archive d) (h : Guard a b) :
    (archive a b h).events = (ParallelComposition.archive a b).events := rfl

theorem archive_card (a b : Archive d) (h : Guard a b) :
    (archive a b h).events.card = a.events.card + b.events.card :=
  ParallelComposition.archive_card a b

def context (c e : Context d) (h : Guard c.archive e.archive) : Context d :=
  contextOf (ParallelComposition.code c.archive e.archive)
    (ParallelComposition.attributes c.archive e.archive)
    (edge c.archive e.archive) (edge_irrefl c.archive e.archive)
    (edge_trans c.archive e.archive) ((temporal_guard_iff _ _).mpr h)
    (c.current.disjSum e.current)

def selection {c e : Context d} (h : Guard c.archive e.archive)
    (a : Selection c) (b : Selection e) : Selection (context c e h) :=
  selectionOf _ _ _ _ _ _ _ (a.val.disjSum b.val) (Finset.disjSum_mono a.property b.property)

def temporal (x y : Rich d) (h : Guard x.1.archive y.1.archive) : Rich d :=
  ⟨context x.1 y.1 h, selection h x.2 y.2⟩

theorem charge_disjSum (c e : Context d) (h : Guard c.archive e.archive)
    (s : Finset c.Event) (t : Finset e.Event) :
    charge (context c e h) ((s.disjSum t).map (equiv _ _ h).toEmbedding) =
      charge c s + charge e t := by
  change charge (contextOf _ _ _ _ _ _ _) ((s.disjSum t).map (eventEquiv _).toEmbedding) = _
  rw [TaggedPresentation.charge_map]
  simp [Finset.sum_disjSum, ParallelComposition.attributes, charge, contribution]

theorem q_temporal (x y : Rich d) (h : Guard x.1.archive y.1.archive) :
    q (temporal x y h) = q x + q y := charge_disjSum _ _ h _ _

theorem background_temporal (c e : Context d) (h : Guard c.archive e.archive) :
    background (context c e h) = background c + background e := charge_disjSum _ _ h _ _

theorem balanced_temporal {c e : Context d} (h : Guard c.archive e.archive)
    (hc : Balanced c) (he : Balanced e) : Balanced (context c e h) := by
  change background (context c e h) = 0
  rw [background_temporal, hc, he, add_zero]

def temporalBalanced (x y : BalancedRich d) (h : Guard x.val.1.archive y.val.1.archive) :
    BalancedRich d := ⟨temporal x.val y.val h, balanced_temporal h x.property y.property⟩

/-- Translation changes the input time coordinate explicitly; all other data are copied. -/
def shiftArchive (a : Archive d) (k : Int) : Archive d where
  events := a.events
  attributes e := {a.attributes e with time := (a.attributes e).time + k}
  causal := a.causal
  irrefl := a.irrefl
  trans := a.trans
  time_lt e f h := by simpa only [add_comm] using add_lt_add_right (a.time_lt e f h) k

def shiftContext (c : Context d) (k : Int) : Context d := ⟨shiftArchive c.archive k, c.current⟩

def shiftRich (x : Rich d) (k : Int) : Rich d := ⟨shiftContext x.1 k, x.2⟩

theorem shift_attributes (a : Archive d) (k : Int) (e : a.Event) :
    (shiftArchive a k).attributes e = {a.attributes e with time := (a.attributes e).time + k} := rfl

theorem shift_causal (a : Archive d) (k : Int) (e f : a.Event) :
    (shiftArchive a k).causal e f ↔ a.causal e f := Iff.rfl

theorem q_shift (x : Rich d) (k : Int) : q (shiftRich x k) = q x := rfl

theorem background_shift (c : Context d) (k : Int) :
    background (shiftContext c k) = background c := rfl

/-- A finite, nonnegative bound also handles either empty archive without an extremum choice. -/
def shiftBound (a b : Archive d) : Nat :=
  Finset.univ.sup fun p : a.Event × b.Event =>
    ((a.attributes p.1).time - (b.attributes p.2).time).natAbs

theorem guard_of_large_shift (a b : Archive d) (k : Int) (hk : (shiftBound a b : Int) < k) :
    Guard a (shiftArchive b k) := by
  intro e f
  have hn : ((a.attributes e).time - (b.attributes f).time).natAbs ≤ shiftBound a b := by
    unfold shiftBound
    exact Finset.le_sup (f := fun p : a.Event × b.Event =>
      ((a.attributes p.1).time - (b.attributes p.2).time).natAbs) (Finset.mem_univ (e, f))
  have hz : (a.attributes e).time - (b.attributes f).time ≤
      (((a.attributes e).time - (b.attributes f).time).natAbs : Int) := Int.le_natAbs
  have hn' : (((a.attributes e).time - (b.attributes f).time).natAbs : Int) ≤ shiftBound a b :=
    Int.ofNat_le.mpr hn
  change (a.attributes e).time < (b.attributes f).time + k
  omega

theorem exists_shift (a b : Archive d) : ∃ k : Int, Guard a (shiftArchive b k) :=
  ⟨(shiftBound a b : Int) + 1, guard_of_large_shift a b _ (by omega)⟩

theorem guard_empty_left (a b : Archive d) (h : a.events = ∅) : Guard a b := by
  intro e
  have := e.property
  simp [h] at this

theorem guard_empty_right (a b : Archive d) (h : b.events = ∅) : Guard a b := by
  intro _ f
  have := f.property
  simp [h] at this

end
end D5.S3.ConceptDynamics.Spacetime.TemporalComposition
