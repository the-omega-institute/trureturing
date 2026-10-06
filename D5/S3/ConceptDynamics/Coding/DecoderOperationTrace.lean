/- GID: D5/S3/ConceptDynamics/Coding/DecoderOperationTrace
   generality: G
   anchors: []
   utility: none
   digest: Finite primitive traces retain readable states and replay unread suffixes. -/
import Mathlib.Logic.Relation
import Mathlib.Data.List.OfFn
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.ENat.Lattice

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


/-- A finite actual path that acquires input contains a finite startup path
ending immediately before its first acquisition. -/
theorem initial_drain_of_acquired_run (action : C → Op C I O) (initial : C)
    (r : ℕ → I) (t : Frame C O)
    (hr : Run action (full r) ⟨initial,0,[]⟩ t) (hp : 0 < t.acquired) :
    ∃ u, Drain action ⟨initial,0,[]⟩ u := by
  obtain ⟨vertices,hv⟩ := hr
  induction hv with
  | refl => simp at hp
  | @tail middle finish vertices hv edge ih =>
    by_cases hm : 0 < middle.acquired
    · exact ih hm
    · have zero : middle.acquired = 0 := by omega
      cases edge with
      | internal c d q o batch inst => dsimp only at hp zero; omega
      | acquire c d q o batch f color inst available result =>
        refine ⟨⟨c,q,o⟩,⟨vertices,trace_input_transfer hv ?_⟩,Or.inr ⟨f,inst⟩⟩
        intro k hk hq
        dsimp only at zero hk hq
        omega

/-- Safety on two actual first-label competitors and D liveness force finite
startup. Finite processing is then required only after executed acquisitions. -/
theorem processing_of_safe_live_pair (action : C → Op C I O) (initial : C)
    (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
    (safety : ∀ a r, Record a r → ∀ t,
      Run action (full r) ⟨initial,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, Record a r → InD a → ∀ p,
      ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
    (a beta : ℕ → O) (r r' : ℕ → I)
    (ha : Record a r) (hb : Record beta r') (hd : InD a) (different : a 0 ≠ beta 0)
    (postprocessing : ∀ a r, Record a r → ∀ (c d : C) (q : ℕ) (o w : List O)
      (f : I → Option (C × List O)),
      Run action (full r) ⟨initial,0,[]⟩ ⟨c,q,o⟩ →
      action c = .acquire f → f (r q) = some (d,w) →
      ∃ t, Drain action ⟨d,q+1,o++w⟩ t) : Processing action initial Record := by
  refine ⟨?_,postprocessing⟩
  obtain ⟨t,ht,hp⟩ := liveness a r ha hd 0
  have acquired : 0 < t.acquired := by
    by_contra hn
    have zero : t.acquired = 0 := by omega
    obtain ⟨vertices,hv⟩ := ht
    have ht' : Run action (full r') ⟨initial,0,[]⟩ t := by
      refine ⟨vertices,trace_input_transfer hv ?_⟩
      intro k hk hq; dsimp only at hk; omega
    exact different ((safety a r ha t ⟨vertices,hv⟩ 0 hp).symm.trans
      (safety beta r' hb t ht' 0 hp))
  exact initial_drain_of_acquired_run action initial r t ht acquired

end D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
