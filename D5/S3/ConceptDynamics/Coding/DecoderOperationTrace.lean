/- GID: D5/S3/ConceptDynamics/Coding/DecoderOperationTrace
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/DecoderOperationTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite primitive traces retain readable states and replay unread suffixes. -/
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

/-- Replay uses the same vertex list and primitive batches, with independent old output. -/
theorem trace_replay {action : C → Op C I O} {r : ℕ → I}
    {s t : Frame C O} {v : List C} (h : Trace action (full r) s t v) :
    ∃ m w, t.acquired = s.acquired + m ∧ t.output = s.output ++ w ∧
      ∀ (r' : ℕ → I) (q' : ℕ) (o' : List O),
        (∀ j, r (s.acquired+j) = r' (q'+j)) →
        Trace action (full r') ⟨s.state,q',o'⟩ ⟨t.state,q'+m,o'++w⟩ v := by
  induction h with
  | refl => refine ⟨0,[],by simp,by simp,?_⟩; intro r' q' o' same; simpa using
      (Trace.refl : Trace action (full r') ⟨s.state,q',o'⟩ ⟨s.state,q',o'⟩ [s.state])
  | @tail middle finish vertices h edge ih =>
    obtain ⟨m,w,hq,ho,replay⟩ := ih
    cases edge with
    | internal c d q o batch inst =>
      dsimp only at hq ho replay
      refine ⟨m,w++batch,hq,by simpa [ho,List.append_assoc],?_⟩
      intro r' q' o' same
      simpa [List.append_assoc] using (replay r' q' o' same).tail
        (Step.internal c d (q'+m) (o'++w) batch inst)
    | acquire c d q o batch f a inst ha hf =>
      dsimp only at hq ho replay
      refine ⟨m+1,w++batch,by simp_all [Nat.add_assoc],by simpa [ho,List.append_assoc],?_⟩
      intro r' q' o' same
      have inputEq : full r' (q'+m) = some a := by
        dsimp only [full]
        rw [← same m,← hq]
        exact ha
      simpa [Nat.add_assoc,List.append_assoc] using (replay r' q' o' same).tail
        (Step.acquire c d (q'+m) (o'++w) batch f a inst inputEq hf)

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

/-- Comparable actual paths and unread-suffix replay distinguish live source addresses. -/
theorem actual_address_eq (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
    (safe : ∀ a r, Record a r → ∀ t,
      Run action (full r) ⟨initial,0,[]⟩ t → ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (live : ∀ a r, Record a r → InD a → ∀ p,
      ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
    (a b : ℕ → O) (r r' : ℕ → I) (ha : Record a r) (hb : Record b r') (hd : InD a)
    (s s' : Frame C O)
    (hs : Run action (full r) ⟨initial,0,[]⟩ s)
    (hs' : Run action (full r') ⟨initial,0,[]⟩ s')
    (state : s.state = s'.state) (output : s.output = s'.output)
    (same : ∀ j, r (s.acquired+j) = r' (s'.acquired+j)) : a = b := by
  funext p
  obtain ⟨t,ht,hp⟩ := live a r ha hd (max p s.output.length)
  have hp' : p < t.output.length := (le_max_left _ _).trans_lt hp
  have after : Run action (full r) s t := by
    rcases run_comparable hs ht with h | h
    · exact h
    · have hg := (run_mono h).2
      have hh := le_max_right p s.output.length
      omega
  obtain ⟨v,hv⟩ := after
  obtain ⟨m,w,hq,ho,replay⟩ := trace_replay hv
  have newTrace := replay r' s'.acquired s'.output same
  rw [state] at newTrace
  have all := run_trans hs' (show Run action (full r') s'
      ⟨t.state,s'.acquired+m,s'.output++w⟩ from ⟨v,newTrace⟩)
  have hnew : p < (s'.output++w).length := by rw [← output,← ho]; exact hp'
  calc a p = t.output[p] := (safe a r ha t ht p hp').symm
       _ = (s'.output++w)[p] := by simp only [ho,output]
       _ = b p := safe b r' hb _ all p hnew

/-- This supremum includes every actual record and every operation vertex. -/
def ReachThrough (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (H : ℕ) (c : C) : Prop :=
  ∃ a r t, Record a r ∧ Run action (full r) ⟨initial,0,[]⟩ t ∧
    t.acquired ≤ H ∧ t.state = c

noncomputable def Peak (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ) : WithTop ℕ :=
  ⨆ c, ⨆ (_ : ReachThrough action initial Record H c), ((enc c).length : WithTop ℕ)

theorem peak_bound (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ) (c : C)
    (hc : ReachThrough action initial Record H c) :
    ((enc c).length : WithTop ℕ) ≤ Peak action initial Record enc H :=
  le_iSup_of_le c (le_iSup_of_le hc (le_refl _))

private theorem trace_vertex_split {action : C → Op C I O} {input : ℕ → Option I}
    {s t : Frame C O} {v : List C} (h : Trace action input s t v) (c : C) (hc : c ∈ v) :
    ∃ u, Run action input s u ∧ Run action input u t ∧ u.state = c := by
  induction h with
  | refl =>
    have he : c = s.state := by simpa using hc
    exact ⟨s,⟨_,.refl⟩,⟨_,.refl⟩,he.symm⟩
  | @tail middle finish vertices h edge ih =>
    rcases List.mem_append.mp hc with old | last
    · obtain ⟨u,hu,ht,he⟩ := ih old
      exact ⟨u,hu,run_closure.mpr ((run_closure.mp ht).tail edge),he⟩
    · have he : c = finish.state := by simpa using last
      exact ⟨finish,⟨_,h.tail edge⟩,⟨_,.refl⟩,he.symm⟩

/-- No readable intermediate state disappears when costs are bounded at a horizon. -/
theorem peak_trace_bound (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ)
    (a : ℕ → O) (r : ℕ → I) (t : Frame C O) (v : List C)
    (ha : Record a r) (hr : Trace action (full r) ⟨initial,0,[]⟩ t v)
    (hq : t.acquired ≤ H) (c : C) (hc : c ∈ v) :
    ((enc c).length : WithTop ℕ) ≤ Peak action initial Record enc H := by
  obtain ⟨u,hu,ht,he⟩ := trace_vertex_split hr c hc
  exact peak_bound action initial Record enc H c
    ⟨a,r,u,ha,hu,(run_mono ht).1.trans hq,he⟩

theorem peak_monotone (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) :
    Monotone (Peak action initial Record enc) := by
  intro H K hHK
  apply iSup_le
  intro c
  apply iSup_le
  rintro ⟨a,r,t,ha,hr,hq,hc⟩
  exact peak_bound action initial Record enc K c ⟨a,r,t,ha,hr,hq.trans hHK,hc⟩



end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def phi : ℝ := 1 + t
noncomputable def c0 : ℝ := 2 * t / 5
inductive Label | L3 | L0 | L5 | L2 | L25
  deriving DecidableEq, Repr
inductive Guard | G0 | G1
  deriving DecidableEq, Repr
abbrev Ownership := Fin 5 → Bool

def nextGuard : Guard → Label → Option Guard
  | .G0, .L3 | .G0, .L0 | .G0, .L2 => some .G0
  | .G0, .L5 | .G0, .L25 => some .G1
  | .G1, .L3 | .G1, .L0 => some .G0
  | .G1, .L5 => some .G1
  | .G1, .L2 | .G1, .L25 => none

def walk : Guard → List Label → Option Guard
  | s, [] => some s
  | s, l :: w => (nextGuard s l).bind (fun s' => walk s' w)

def LegalWord (s e : Guard) (w : List Label) : Prop := walk s w = some e

noncomputable def supportUpper : Guard → ℝ
  | .G0 => phi
  | .G1 => t

def InSupport (s : Guard) (x : ℝ) : Prop := -1 ≤ x ∧ x ≤ supportUpper s

noncomputable def shift : Label → ℝ
  | .L3 => -t
  | .L0 => 0
  | .L5 => T2
  | .L2 => 1
  | .L25 => 2 - t

noncomputable def branch (l : Label) (x : ℝ) : ℝ := shift l - g * x

noncomputable def compose : List Label → ℝ → ℝ
  | [], x => x
  | l :: w, x => branch l (compose w x)

/-- A finite literal prefix followed by the empty-window label forever. -/
def address (w : List Label) (p : ℕ) : Label := w[p]?.getD .L0

/-- The complete remaining literal suffix, with the zero tail interpreted at zero. -/
noncomputable def coordinate (w : List Label) (p : ℕ) : ℝ := compose (w.drop p) 0

def repeatWord (w : List Label) : ℕ → List Label
  | 0 => []
  | n + 1 => w ++ repeatWord w n

def U : List Label := [.L5, .L0, .L3, .L0, .L3, .L3]
def V : List Label := [.L0, .L3, .L3, .L5, .L0, .L3]
def C : List Label :=
  [.L5, .L5, .L3, .L2, .L2, .L0, .L3, .L3, .L3, .L25,
   .L5, .L0, .L0, .L2, .L2, .L25, .L3, .L3, .L0, .L5]
def block : Side → List Label | .high => U | .low => V
def stem (j : Side) : List Label := block j ++ C

/-- All positive returns are source words; no budget cap is built into the carrier. -/
def returnWord (j : Side) (a : Return) : List Label :=
  repeatWord (block j) a.m ++ repeatWord C a.r
def externalWord (j : Side) (execution : List Return) : List Label :=
  (execution.reverse.map (returnWord j)).flatten
def anchor (j : Side) : Model → List Label
  | .original => []
  | .anchored => stem j
def observedPrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  stem j ++ externalWord j execution ++ anchor j model
/-- The final zero is part of a finite representation of the same eventually-zero tail. -/
def exitPrefix : Side → List Label | .high => [.L5, .L0] | .low => [.L0]
def tailPrefix (j : Side) : List Label :=
  block j ++ repeatWord C 3 ++ exitPrefix j
def sourcePrefix (j : Side) (model : Model) (execution : List Return) : List Label :=
  observedPrefix j model execution ++ tailPrefix j
def source (j : Side) (model : Model) (execution : List Return) : ℕ → Label :=
  address (sourcePrefix j model execution)

noncomputable def eSide : Side → ℝ | .high => T2 - c0 | .low => c0
noncomputable def xSide (j : Side) : ℝ := aSide j + rho * chi ^ 3 * eSide j
noncomputable def ySide (j : Side) : ℝ := aSide j + rho * chi * xSide j
noncomputable def sign : Side → ℝ | .high => 1 | .low => -1
noncomputable def initial (j : Side) : Model → ℝ
  | .original => xSide j
  | .anchored => ySide j

def observationOffset : Model → ℕ | .original => 26 | .anchored => 52

noncomputable def cut : ℕ → ℝ
  | 0 => -1
  | 1 => -T2 - lam
  | 2 => g - 3 * lam
  | 3 => t - 5 * lam
  | 4 => 2 * t - 7 * lam
  | 5 => 2 * t + lam
  | _ => phi

noncomputable def readout (o : Ownership) (x : ℝ) : Color :=
  if x < cut 1 then 0 else if x = cut 1 then (if o 0 then 1 else 0) else
  if x < cut 2 then 1 else if x = cut 2 then (if o 1 then 2 else 1) else
  if x < cut 3 then 2 else if x = cut 3 then (if o 2 then 3 else 2) else
  if x < cut 4 then 3 else if x = cut 4 then (if o 3 then 4 else 3) else
  if x < cut 5 then 4 else if x = cut 5 then (if o 4 then 5 else 4) else 5

def Cell (o : Ownership) (i : Color) (x : ℝ) : Prop :=
  InSupport .G0 x ∧ readout o x = i
def ClosedCell (i : Color) (x : ℝ) : Prop := cut i.val ≤ x ∧ x ≤ cut (i.val + 1)
noncomputable def clip (x : ℝ) : ℝ := max (-1) (min phi x)
noncomputable def observe (o : Ownership) (x error : ℝ) : Color := readout o (clip (x + error))

inductive Contract | closed | strict | recordMargin
  deriving DecidableEq, Repr
def ErrorBound (b : ℝ) : Contract → (ℕ → ℝ) → Prop
  | .closed, err => ∀ p, |err p| ≤ b
  | .strict, err => ∀ p, |err p| < b
  | .recordMargin, err => ∃ eps > 0, ∀ p, |err p| ≤ b - eps

/-- A readout/error relation on the two fixed sources, including their zero-error futures. -/
def ActualPairSupply (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (execution : List Return) : Prop :=
  ∀ j : Side, ∃ err : ℕ → ℝ, ErrorBound b contract err ∧
    (∀ p (hp : p < (history model execution).length),
      observe o (coordinate (sourcePrefix j model execution) p) (err p) =
        (history model execution)[p]) ∧
    (∀ p, (history model execution).length ≤ p → err p = 0) ∧
    (∀ p, observe o (coordinate (sourcePrefix j model execution)
        ((observedPrefix j model execution).length + p))
        (err ((observedPrefix j model execution).length + p)) =
      observe o (coordinate (tailPrefix j) p) 0)

/-- Legal branch supports and the affine law are derived from the literal source.
The occurrence formula uses the complete right suffix at that very occurrence. -/
theorem literal_source_geometry :
    (∀ (s e : Guard) (w : List Label) (z : ℝ), LegalWord s e w → InSupport e z →
      InSupport s (compose w z)) ∧
    (∀ (left B right : List Label) (p : ℕ), p ≤ B.length →
      coordinate (left ++ B ++ right) (left.length + p) =
        compose (B.drop p) c0 + (-g) ^ (B.length - p) * (coordinate right 0 - c0)) ∧
    (∀ (w : List Label) (n p : ℕ), coordinate (w ++ List.replicate n Label.L0) p =
      coordinate w p) ∧
    (∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y) ∧
    (∀ (w v : List Label) (z : ℝ), compose (w ++ v) z = compose w (compose v z)) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsqrt0 := Real.sqrt_nonneg (5 : ℝ)
  have ht : t ^ 2 = 1 - t := by dsimp [t]; nlinarith
  have htlo : 0 < t := by dsimp [t]; nlinarith
  have hthi : t < 1 := by dsimp [t]; nlinarith
  have hg : 0 < g := by dsimp [g, t]; nlinarith
  have edge_support : ∀ (s e : Guard) (l : Label) (z : ℝ),
      nextGuard s l = some e → InSupport e z → InSupport s (branch l z) := by
    intro s e l z hedge hz
    have hlo := mul_nonneg hg.le (sub_nonneg.mpr hz.1)
    have hhi := mul_nonneg hg.le (sub_nonneg.mpr hz.2)
    cases s <;> cases e <;> cases l <;>
      simp_all [nextGuard, InSupport, supportUpper, branch, shift, phi, T2, g] <;>
      constructor <;> nlinarith
  have affine : ∀ (w : List Label) (x y : ℝ),
      compose w (x + y) = compose w x + (-g) ^ w.length * y := by
    intro w
    induction w with
    | nil => intro x y; simp [compose]
    | cons l w ih =>
      intro x y
      simp only [compose, List.length_cons, ih, branch, pow_succ]
      ring
  have append_compose : ∀ (w v : List Label) (z : ℝ),
      compose (w ++ v) z = compose w (compose v z) := by
    intro w
    induction w with
    | nil => intro v z; rfl
    | cons l w ih => intro v z; simp [compose, ih]
  have zero_tail : ∀ n, compose (List.replicate n Label.L0) 0 = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, compose, branch, shift, ih]
  refine ⟨?_, ?_, ?_, affine, append_compose⟩
  · intro s e w
    induction w generalizing s with
    | nil =>
      intro z hw hz
      have he : s = e := by simpa [LegalWord, walk] using hw
      simpa [compose, he] using hz
    | cons l w ih =>
      intro z hw hz
      cases hnext : nextGuard s l with
      | none => simp [LegalWord, walk, hnext] at hw
      | some s' =>
        have hrest : LegalWord s' e w := by simpa [LegalWord, walk, hnext] using hw
        exact edge_support s s' l (compose w z) hnext (ih s' z hrest hz)
  · intro left B right p hp
    unfold coordinate
    rw [show (left ++ B ++ right).drop (left.length + p) = B.drop p ++ right by
      rw [List.append_assoc, List.drop_append]
      simp only [List.drop_eq_nil_of_le (Nat.le_add_right left.length p),
        Nat.add_sub_cancel_left, List.nil_append]
      exact List.drop_append_of_le_length hp]
    rw [append_compose]
    have h := affine (B.drop p) c0 (compose right 0 - c0)
    rw [show c0 + (compose right 0 - c0) = compose right 0 by ring] at h
    simpa only [add_sub_cancel_left, List.length_drop, List.drop_zero] using h
  · intro w n p
    unfold coordinate
    by_cases hp : p ≤ w.length
    · rw [List.drop_append_of_le_length hp, append_compose, zero_tail]
    · have hp' : w.length ≤ p := le_of_not_ge hp
      simp [List.drop_append, List.drop_eq_nil_of_le hp', List.drop_replicate, zero_tail, compose]

set_option maxHeartbeats 6000000 in
-- The twenty-label affine calculation requires exact polynomial normalization.
/-- Reversed execution reconstructs the prescribed literal sources. Every positive
return is legal, and the boundary displacement is calculated from that source. -/
theorem paired_source_reconstruction (j : Side) (model : Model) (execution : List Return) :
    LegalWord .G0 .G0 (sourcePrefix j model execution) ∧
    (∀ p, source j model execution ((observedPrefix j model execution).length + p) =
      address (tailPrefix j) p) ∧
    (∀ p, coordinate (sourcePrefix j model execution)
        ((observedPrefix j model execution).length + p) = coordinate (tailPrefix j) p) ∧
    coordinate (externalWord j execution ++ anchor j model ++ tailPrefix j) 0 =
      c0 + sign j * execute j execution (initial j model) ∧
    (observedPrefix j model execution).length = observationOffset model + listWeight execution ∧
    (history model execution).length = observationOffset model + listWeight execution ∧
    (∀ D, compose C (c0 + sign j * D) = c0 + sign j * (chi * D)) ∧
    (∀ D, compose (block j) (c0 + sign j * D) =
      c0 + sign j * (aSide j + rho * D)) ∧
    (∀ (a : Return) D, compose (returnWord j a) (c0 + sign j * D) =
      c0 + sign j * returnMap j a D) ∧
    (∀ (xs : List Return) D, compose (externalWord j xs) (c0 + sign j * D) =
      c0 + sign j * execute j xs D) ∧
    compose (tailPrefix j) 0 = c0 + sign j * xSide j := by
  have affine := literal_source_geometry.2.2.2.1
  have app := literal_source_geometry.2.2.2.2
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ht : t ^ 2 = 1 - t := by dsimp [t]; nlinarith only [hsqrt, Real.sqrt_nonneg (5 : ℝ)]
  have htg : t = (1 + g) / 2 := by dsimp [g]; ring
  have hg2 : g ^ 2 = 1 - 4 * g := by dsimp [g]; nlinarith only [ht]
  have hg3 : g ^ 3 = 17 * g - 4 := by rw [pow_succ, hg2]; nlinarith only [hg2]
  have hg4 : g ^ 4 = 17 - 72 * g := by rw [pow_succ, hg3]; nlinarith only [hg2]
  have hg5 : g ^ 5 = 305 * g - 72 := by rw [pow_succ, hg4]; nlinarith only [hg2]
  have hg6 : g ^ 6 = 305 - 1292 * g := by rw [pow_succ, hg5]; nlinarith only [hg2]
  have hg7 : g ^ 7 = 5473 * g - 1292 := by rw [pow_succ, hg6]; nlinarith only [hg2]
  have centerC : compose C c0 = c0 := by
    have s19 : branch .L5 c0 = (3 + g) / 10 := by
      dsimp [branch, shift, T2, c0]; rw [htg]; nlinarith only [hg2]
    have s18 : branch .L0 ((3 + g) / 10) = (-1 + g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s17 : branch .L3 ((-1 + g) / 10) = -6 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s16 : branch .L3 (-6 / 10) = (-5 + g) / 10 := by
      dsimp [branch, shift]; rw [htg]; ring
    have s15 : branch .L25 ((-5 + g) / 10) = (14 + 4 * g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s14 : branch .L2 ((14 + 4 * g) / 10) = (6 + 2 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s13 : branch .L2 ((6 + 2 * g) / 10) = (8 + 2 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s12 : branch .L0 ((8 + 2 * g) / 10) = -2 / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s11 : branch .L0 (-2 / 10) = (2 * g) / 10 := by
      dsimp [branch, shift]; ring
    have s10 : branch .L5 ((2 * g) / 10) = (3 + 3 * g) / 10 := by
      dsimp [branch, shift, T2]; rw [htg]; nlinarith only [hg2]
    have s9 : branch .L25 ((3 + 3 * g) / 10) = (12 + 4 * g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s8 : branch .L3 ((12 + 4 * g) / 10) = (-9 - g) / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s7 : branch .L3 ((-9 - g) / 10) = -4 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s6 : branch .L3 (-4 / 10) = (-5 - g) / 10 := by
      dsimp [branch, shift]; rw [htg]; ring
    have s5 : branch .L0 ((-5 - g) / 10) = (1 + g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s4 : branch .L2 ((1 + g) / 10) = (9 + 3 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s3 : branch .L2 ((9 + 3 * g) / 10) = (7 + 3 * g) / 10 := by
      dsimp [branch, shift]; nlinarith only [hg2]
    have s2 : branch .L3 ((7 + 3 * g) / 10) = -8 / 10 := by
      dsimp [branch, shift]; rw [htg]; nlinarith only [hg2]
    have s1 : branch .L5 (-8 / 10) = (5 + 3 * g) / 10 := by
      dsimp [branch, shift, T2]; rw [htg]; ring
    have s0 : branch .L5 ((5 + 3 * g) / 10) = c0 := by
      dsimp [branch, shift, T2, c0]; rw [htg]; nlinarith only [hg2]
    simp only [C, compose, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10,
      s9, s8, s7, s6, s5, s4, s3, s2, s1, s0]
  have centerBlock : compose (block j) c0 = c0 + sign j * aSide j := by
    cases j <;> dsimp [block, U, V, compose, branch, shift, T2, c0, sign, aSide,
      rho, hSide] <;> rw [htg] <;> ring_nf <;> linarith only [hg2, hg3, hg4, hg5, hg6, hg7]
  have actC (D : ℝ) : compose C (c0 + sign j * D) = c0 + sign j * (chi * D) := by
    rw [affine, centerC]
    norm_num [C, chi, neg_pow]
    ring
  have actBlock (D : ℝ) : compose (block j) (c0 + sign j * D) =
      c0 + sign j * (aSide j + rho * D) := by
    rw [affine, centerBlock]
    have hlen : (block j).length = 6 := by cases j <;> rfl
    rw [hlen]
    norm_num [rho, neg_pow]
    ring
  have copiesC : ∀ n (D : ℝ), compose (repeatWord C n) (c0 + sign j * D) =
      c0 + sign j * (chi ^ n * D) := by
    intro n
    induction n with
    | zero => intro D; simp [repeatWord, compose]
    | succ n ih =>
      intro D
      rw [repeatWord, app, ih, actC, pow_succ]
      ring
  have copiesBlock : ∀ n (D : ℝ), compose (repeatWord (block j) n) (c0 + sign j * D) =
      c0 + sign j * (hSide j - rho ^ n * (hSide j - D)) := by
    intro n
    induction n with
    | zero => intro D; simp [repeatWord, compose]
    | succ n ih =>
      intro D
      rw [repeatWord, app, ih, actBlock, pow_succ]
      dsimp [aSide]
      ring
  have actReturn (a : Return) (D : ℝ) :
      compose (returnWord j a) (c0 + sign j * D) = c0 + sign j * returnMap j a D := by
    rw [returnWord, app, copiesC, copiesBlock]
    rfl
  have external_cons (a : Return) (rest : List Return) :
      externalWord j (a :: rest) = externalWord j rest ++ returnWord j a := by
    simp [externalWord, List.reverse_cons, List.map_append, List.flatten_append]
  have actExternal : ∀ (xs : List Return) (D : ℝ),
      compose (externalWord j xs) (c0 + sign j * D) = c0 + sign j * execute j xs D := by
    intro xs
    induction xs with
    | nil => intro D; rfl
    | cons a rest ih => intro D; rw [external_cons, app, actReturn, ih]; rfl
  have actTail : compose (tailPrefix j) 0 = c0 + sign j * xSide j := by
    have hexit (j' : Side) : compose (exitPrefix j') 0 = c0 + sign j' * eSide j' := by
      cases j' <;> simp only [exitPrefix, compose, branch, shift, sign, eSide,
        mul_zero, sub_zero] <;> ring
    rw [tailPrefix, app, app, hexit j, copiesC, actBlock]
    dsimp [xSide]
    ring
  have actAnchorTail : compose (anchor j model ++ tailPrefix j) 0 =
      c0 + sign j * initial j model := by
    cases model with
    | original => simpa [anchor, initial, compose] using actTail
    | anchored =>
      rw [anchor, app, actTail, stem, app, actC, actBlock]
      dsimp [initial, ySide]
      ring
  have walk_app : ∀ (w v : List Label) (s : Guard), walk s (w ++ v) =
      (walk s w).bind (fun e => walk e v) := by
    intro w
    induction w with
    | nil => intro v s; rfl
    | cons l w ih =>
      intro v s
      cases hn : nextGuard s l <;> simp [walk, hn, ih]
  have walkBlock (s : Guard) : walk s (block j) = some .G0 := by
    cases s <;> cases j <;> rfl
  have walkC (s : Guard) : walk s C = some .G1 := by cases s <;> rfl
  have walkCopiesBlock : ∀ n (s : Guard), walk s (repeatWord (block j) (n + 1)) = some .G0 := by
    intro n
    induction n with
    | zero => intro s; simpa only [repeatWord, List.append_nil] using walkBlock s
    | succ n ih =>
      intro s
      rw [repeatWord, walk_app, walkBlock]
      exact ih .G0
  have walkCopiesC : ∀ n (s : Guard), walk s (repeatWord C (n + 1)) = some .G1 := by
    intro n
    induction n with
    | zero => intro s; simpa only [repeatWord, List.append_nil] using walkC s
    | succ n ih =>
      intro s
      rw [repeatWord, walk_app, walkC]
      exact ih .G1
  have walkReturn (a : Return) (s : Guard) : walk s (returnWord j a) = some .G1 := by
    obtain ⟨m, r, hm, hr⟩ := a
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simp [returnWord, walk_app, walkCopiesBlock, walkCopiesC]
  have walkExternal : ∀ xs, walk .G1 (externalWord j xs) = some .G1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih => simp [external_cons, walk_app, ih, walkReturn]
  have walkStem (s : Guard) : walk s (stem j) = some .G1 := by
    simp [stem, walk_app, walkBlock, walkC]
  have walkAnchor : walk .G1 (anchor j model) = some .G1 := by
    cases model <;> simp [anchor, walkStem, walk]
  have walkTail : walk .G1 (tailPrefix j) = some .G0 := by cases j <;> rfl
  have repeatLength : ∀ (w : List Label) n, (repeatWord w n).length = w.length * n := by
    intro w n
    induction n with
    | zero => rfl
    | succ n ih => simp [repeatWord, ih, Nat.mul_succ, Nat.add_comm]
  have returnLength (a : Return) : (returnWord j a).length = 6 * a.m + 20 * a.r := by
    cases j <;> simp [returnWord, repeatLength, block, U, V, C]
  have externalLength : ∀ xs, (externalWord j xs).length = listWeight xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih => simp [external_cons, returnLength, ih, listWeight, Nat.add_comm]
  have colorsLength (a : Return) : (returnColors a).length = 6 * a.m + 20 * a.r := by
    simp [returnColors, List.length_flatten, colorsD, colorsE, Nat.mul_comm]
  have historyVariableLength : ∀ xs : List Return,
      (xs.reverse.map returnColors).flatten.length = listWeight xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.reverse_cons, List.map_append, List.flatten_append, List.length_append,
        List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [ih, colorsLength]
      simp only [listWeight, Nat.add_comm]
  have stemLength : (stem j).length = 26 := by cases j <;> rfl
  have lenCalc (md : Model) (n : ℕ) :
      26 + n + (anchor j md).length = observationOffset md + n := by
    cases md <;> simp only [anchor, List.length_nil, stemLength, observationOffset] <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, actC, actBlock, actReturn, actExternal, actTail⟩
  · simp [LegalWord, sourcePrefix, observedPrefix, walk_app, walkStem, walkExternal,
      walkAnchor, walkTail]
  · intro p
    simp [source, sourcePrefix, address, List.getElem?_append_right]
  · intro p
    simp only [coordinate, sourcePrefix, List.drop_append, Nat.add_sub_cancel_left,
      List.drop_eq_nil_of_le (Nat.le_add_right (observedPrefix j model execution).length p),
      List.nil_append]
  · simp only [coordinate, List.drop_zero, List.append_assoc]
    rw [app, actAnchorTail, actExternal]
  · simp only [observedPrefix, List.length_append, stemLength, externalLength]
    exact lenCalc model (listWeight execution)
  · have hd : colorsD.length = 6 := rfl
    have he : colorsE.length = 20 := rfl
    cases model <;>
      simp only [history, List.length_append, hd, he, historyVariableLength,
        observationOffset, List.length_nil] <;> omega

/-- The legal finite prefix constructs the guard itinerary and coordinate path
of its eventually-empty address, including all zero-tail departure positions. -/
theorem literal_address_path (s e : Guard) (w : List Label) (hw : LegalWord s e w) :
    ∃ path : ℕ → Guard, path 0 = s ∧
      (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (coordinate w p)) ∧
      (∀ p, coordinate w p = branch (address w p) (coordinate w (p + 1))) := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ht : 0 ≤ t := by dsimp [t]; nlinarith only [hsqrt, Real.sqrt_nonneg (5 : ℝ)]
  have zeroSupport (q : Guard) : InSupport q 0 := by
    cases q <;> simp only [InSupport, supportUpper, phi] <;> constructor <;> linarith
  induction w generalizing s with
  | nil =>
    refine ⟨fun p => if p = 0 then s else .G0, by simp, ?_, ?_, ?_⟩
    · intro p
      cases p with
      | zero => cases s <;> rfl
      | succ p => simp [address, nextGuard]
    · intro p
      simpa only [coordinate, List.drop_nil, compose] using
        zeroSupport (if p = 0 then s else .G0)
    · intro p
      simp [coordinate, address, compose, branch, shift]
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hw
    | some q =>
      have hr : LegalWord q e w := by simpa [LegalWord, walk, hn] using hw
      obtain ⟨path, hzero, hleg, hsupp, hrec⟩ := ih q hr
      refine ⟨fun p => match p with | 0 => s | p + 1 => path p, rfl, ?_, ?_, ?_⟩
      · intro p
        cases p with
        | zero => simpa [address, hzero] using hn
        | succ p => simpa [address, Nat.add_assoc] using hleg p
      · intro p
        cases p with
        | zero => exact literal_source_geometry.1 s e (l :: w) 0 hw (zeroSupport e)
        | succ p => simpa [coordinate] using hsupp p
      · intro p
        cases p with
        | zero => simp [coordinate, address, compose]
        | succ p => simpa [coordinate, address, Nat.add_assoc] using hrec p


/-- Acquisition at every original six- and twenty-slot departure coordinate.
The active slot uses the actual endpoint flag; all other flags remain arbitrary. -/
def BlockSupply (o : Ownership) (b : ℝ) (strict : Bool)
    (w : List Label) (cs : List Color) (z : ℝ) : Prop :=
  ∀ p (hp : p < cs.length), ∃ error : ℝ,
    (if strict then |error| < b else |error| ≤ b) ∧
    observe o (compose (w.drop p) z) error = cs[p]


end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
