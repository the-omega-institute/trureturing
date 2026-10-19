/- GID: D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive decoder traces retain actual states and acquisition cuts. -/
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import Mathlib.Logic.Relation
import Mathlib.Data.List.OfFn
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.ENat.Lattice

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

inductive Op (C I O : Type*) where
  | internal (next : C) (batch : List O)
  | acquire (next : I → Option (C × List O))
  | stopped

structure Frame (C O : Type*) where
  state : C
  acquired : ℕ
  output : List O

variable {C I O : Type*}

/-- The input and output are external proof bookkeeping, never arguments of action. -/
inductive Step (action : C → Op C I O) (input : ℕ → Option I) :
    Frame C O → Frame C O → Prop where
  | internal (c d : C) (q : ℕ) (o w : List O)
      (instruction : action c = .internal d w) :
      Step action input ⟨c,q,o⟩ ⟨d,q,o ++ w⟩
  | acquire (c d : C) (q : ℕ) (o w : List O) (f : I → Option (C × List O))
      (a : I) (instruction : action c = .acquire f)
      (available : input q = some a) (result : f a = some (d,w)) :
      Step action input ⟨c,q,o⟩ ⟨d,q+1,o ++ w⟩

/-- Every endpoint and intermediate readable state is retained in the vertex list. -/
inductive Trace (action : C → Op C I O) (input : ℕ → Option I)
    (start : Frame C O) : Frame C O → List C → Prop where
  | refl : Trace action input start start [start.state]
  | tail {middle finish : Frame C O} {vertices : List C} :
      Trace action input start middle vertices → Step action input middle finish →
      Trace action input start finish (vertices ++ [finish.state])

def Run (action : C → Op C I O) (input : ℕ → Option I)
    (s t : Frame C O) : Prop := ∃ vertices, Trace action input s t vertices

def full (r : ℕ → I) : ℕ → Option I := fun q => some (r q)
def availablePrefix (h : List I) : ℕ → Option I := fun q => h[q]?
def front (r : ℕ → I) (n : ℕ) : List I := List.ofFn (fun p : Fin n => r p.val)
def Ready (action : C → Op C I O) (c : C) : Prop :=
  action c = .stopped ∨ ∃ f, action c = .acquire f

def Cut (action : C → Op C I O) (initial : C) (h : List I) (t : Frame C O) : Prop :=
  Run action (availablePrefix h) ⟨initial,0,[]⟩ t ∧ t.acquired = h.length ∧ Ready action t.state

def Drain (action : C → Op C I O) (s t : Frame C O) : Prop :=
  Run action (fun _ => none) s t ∧ Ready action t.state

theorem step_unique (action : C → Op C I O) (input : ℕ → Option I) :
    Relator.RightUnique (Step action input) := by
  intro s t u ht hu
  cases ht with
  | internal c d q o w h =>
    cases hu with
    | internal _ d' _ _ w' h' => cases h.symm.trans h'; rfl
    | acquire _ _ _ _ _ _ _ h' _ _ => cases h.symm.trans h'
  | acquire c d q o w f a h ha hf =>
    cases hu with
    | internal _ _ _ _ _ h' => cases h.symm.trans h'
    | acquire _ d' _ _ w' f' a' h' ha' hf' =>
      cases h.symm.trans h'
      cases ha.symm.trans ha'
      cases hf.symm.trans hf'
      rfl

theorem trace_closure {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {v : List C} (h : Trace action input s t v) :
    Relation.ReflTransGen (Step action input) s t := by
  induction h with
  | refl => exact .refl
  | tail _ edge ih => exact ih.tail edge

theorem run_closure {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} : Run action input s t ↔
      Relation.ReflTransGen (Step action input) s t := by
  constructor
  · rintro ⟨v,h⟩; exact trace_closure h
  · intro h
    induction h with
    | refl => exact ⟨_,.refl⟩
    | tail _ edge ih => obtain ⟨v,hv⟩ := ih; exact ⟨_,hv.tail edge⟩

theorem run_trans {action : C → Op C I O} {input : ℕ → Option I}
    {s t u : Frame C O} (h : Run action input s t) (g : Run action input t u) :
    Run action input s u :=
  run_closure.mpr (h |> run_closure.mp |>.trans (run_closure.mp g))

theorem run_comparable {action : C → Op C I O} {input : ℕ → Option I}
    {s t u : Frame C O} (h : Run action input s t) (g : Run action input s u) :
    Run action input t u ∨ Run action input u t := by
  exact (Relation.ReflTransGen.total_of_right_unique (step_unique action input)
    (run_closure.mp h) (run_closure.mp g)).imp run_closure.mpr run_closure.mpr

theorem run_mono {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} (h : Run action input s t) :
    s.acquired ≤ t.acquired ∧ s.output.length ≤ t.output.length := by
  have hh := run_closure.mp h
  clear h
  induction hh with
  | refl => exact ⟨le_refl _,le_refl _⟩
  | tail _ edge ih =>
    rcases ih with ⟨ha,ho⟩
    cases edge <;> dsimp only at * <;> simp only [List.length_append] <;> constructor <;> omega

theorem trace_input_transfer {action : C → Op C I O} {input input' : ℕ → Option I}
    {s t : Frame C O} {v : List C} (h : Trace action input s t v)
    (same : ∀ q, s.acquired ≤ q → q < t.acquired → input q = input' q) :
    Trace action input' s t v := by
  induction h with
  | refl => exact .refl
  | @tail m t v h edge ih =>
    have hm := run_mono (show Run action input s m from ⟨v,h⟩)
    cases edge with
    | internal c d q o w inst =>
      exact (ih (by intro k hk hl; exact same k hk hl)).tail
        (.internal c d q o w inst)
    | acquire c d q o w f a inst ha hf =>
      dsimp only at hm same
      refine (ih (by intro k hk hl; dsimp only at hl; exact same k hk (by omega))).tail
        (.acquire c d q o w f a inst ?_ hf)
      rw [← same q hm.1 (by simp)]
      exact ha

theorem prefix_trace_iff {action : C → Op C I O} (r : ℕ → I) (n : ℕ)
    {s t : Frame C O} {v : List C} (bound : t.acquired ≤ n) :
    Trace action (full r) s t v ↔ Trace action (availablePrefix (front r n)) s t v := by
  constructor <;> intro h <;> apply trace_input_transfer h <;> intro q hq hqn
  all_goals
    have hn : q < (front r n).length := by simp only [front,List.length_ofFn]; omega
    simp only [availablePrefix,List.getElem?_eq_getElem hn]
    simp [front,full]

theorem cut_unique (action : C → Op C I O) (initial : C) (h : List I)
    {s t : Frame C O} (hs : Cut action initial h s) (ht : Cut action initial h t) : s = t := by
  have terminal (v : Frame C O) (hv : Cut action initial h v) :
      ∀ u, ¬ Step action (availablePrefix h) v u := by
    intro u edge
    cases edge with
    | internal c d q o w inst =>
      rcases hv.2.2 with stop | ⟨f,acq⟩ <;> cases inst.symm.trans (by assumption)
    | acquire c d q o w f a inst ha hf =>
      have hq : q = h.length := hv.2.1
      have hn : availablePrefix h q = none := by simp [availablePrefix,hq]
      rw [hn] at ha; cases ha
  rcases run_comparable hs.1 ht.1 with after | before
  · exact ((Relation.reflTransGen_iff_eq (terminal s hs)).mp (run_closure.mp after)).symm
  · exact (Relation.reflTransGen_iff_eq (terminal t ht)).mp (run_closure.mp before)

/-- Finite processing is required only at startup and actual acquisition results. -/
def Processing (action : C → Op C I O) (initial : C) (Record : (ℕ → O) → (ℕ → I) → Prop) : Prop :=
  (∃ t, Drain action ⟨initial,0,[]⟩ t) ∧
  ∀ a r, Record a r → ∀ (c d : C) (q : ℕ) (o w : List O) (f : I → Option (C × List O)),
    Run action (full r) ⟨initial,0,[]⟩ ⟨c,q,o⟩ →
    action c = .acquire f → f (r q) = some (d,w) →
    ∃ t, Drain action ⟨d,q+1,o++w⟩ t

theorem drain_acquired {action : C → Op C I O} {s t : Frame C O}
    (h : Drain action s t) : t.acquired = s.acquired := by
  have hh := run_closure.mp h.1
  clear h
  induction hh with
  | refl => rfl
  | tail _ edge ih =>
    cases edge with
    | internal => exact ih
    | acquire _ _ _ _ _ _ _ _ impossible _ => cases impossible

theorem drain_run {action : C → Op C I O} {s t : Frame C O}
    (h : Drain action s t) (input : ℕ → Option I) : Run action input s t := by
  obtain ⟨v,hv⟩ := h.1
  refine ⟨v,trace_input_transfer hv ?_⟩
  intro q hq hqt
  have heq := drain_acquired h
  omega

/-- D liveness forces each acquisition, while only its actual processing is drained. -/
theorem actual_cut_exists (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
    (processing : Processing action initial Record)
    (live : ∀ a r, Record a r → InD a → ∀ p,
      ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
    (a : ℕ → O) (r : ℕ → I) (record : Record a r) (finite : InD a) (n : ℕ) :
    ∃ t, Cut action initial (front r n) t ∧
      Run action (full r) ⟨initial,0,[]⟩ t := by
  have makeCut (n : ℕ) (t : Frame C O)
      (hr : Run action (full r) ⟨initial,0,[]⟩ t)
      (hq : t.acquired = n) (ready : Ready action t.state) :
      Cut action initial (front r n) t := by
    obtain ⟨v,hv⟩ := hr
    refine ⟨⟨v,(prefix_trace_iff r n (by omega)).mp hv⟩,by simp [front,hq],ready⟩
  induction n with
  | zero =>
    obtain ⟨t,ht⟩ := processing.1
    have hq := drain_acquired ht
    have hr := drain_run ht (full r)
    exact ⟨t,makeCut 0 t hr hq ht.2,hr⟩
  | succ n ih =>
    obtain ⟨t,cut,ht⟩ := ih
    have hq : t.acquired = n := by simpa [front] using cut.2.1
    obtain ⟨u,hu,hpos⟩ := live a r record finite t.output.length
    have after : Run action (full r) t u := by
      rcases run_comparable ht hu with after | before
      · exact after
      · have hg := (run_mono before).2
        omega
    rcases Relation.ReflTransGen.cases_head (run_closure.mp after) with heq | ⟨v,edge,rest⟩
    · subst u; omega
    · cases edge with
      | internal c d q o w inst =>
        rcases cut.2.2 with stop | ⟨f,acq⟩ <;> cases inst.symm.trans (by assumption)
      | acquire c d q o w f color inst ha hf =>
        have hc : color = r q := by simpa [full] using ha.symm
        subst color
        obtain ⟨z,hz⟩ := processing.2 a r record c d q o w f ht inst hf
        have hrun : Run action (full r) ⟨initial,0,[]⟩ z :=
          run_trans (run_closure.mpr ((run_closure.mp ht).tail
            (.acquire c d q o w f (r q) inst rfl hf))) (drain_run hz (full r))
        have hzq : z.acquired = n+1 := by
          have hh := drain_acquired hz
          dsimp only at hq hh
          omega
        exact ⟨z,makeCut (n+1) z hrun hzq hz.2,hrun⟩

end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
