/- GID: D5/S3/Combinatorics/Probability/AdaptiveNamingCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/AdaptiveNamingCompletion
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Adaptive naming completion preserves the joint stopped record and state. -/

/- Information escape registration remains open. https://github.com/the-omega-institute/trureturing/issues/32103 -/

import D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Uniformly completing a partial naming commutes with a stopped adaptive protocol. -/

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
open D5.S3.Combinatorics.Probability.NamingUpdate (unused)
open D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)
open scoped ENNReal

namespace D5.S3.Combinatorics.Probability.AdaptiveNamingCompletion

section StatefulProtocol

variable {Q S T : Type*} {R : Q → Type*}

/-- Execute the protocol, keeping the ordered transcript and final state. -/
noncomputable def runQueries (step : ∀ q, S → PMF (R q × S)) :
    PassiveProtocol Q R → S → PMF (List (Sigma R) × S)
  | .stop, s => PMF.pure ([], s)
  | .query q next, s => (step q s).bind fun x =>
      (runQueries step (next x.1) x.2).map (fun out => (⟨q, x.1⟩ :: out.1, out.2))

/-- Complete the final state while retaining the observed output. -/
noncomputable def completeAfter {A : Type*} (complete : S → PMF T)
    (ν : PMF (A × S)) : PMF (A × T) :=
  ν.bind fun x => (complete x.2).map (Prod.mk x.1)

private theorem completeAfter_prepend (complete : S → PMF T)
    (ν : PMF (List (Sigma R) × S)) (r : Sigma R) :
    completeAfter complete (ν.map (fun x => (r :: x.1, x.2))) =
      (completeAfter complete ν).map (fun x => (r :: x.1, x.2)) := by
  simp only [completeAfter, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

private theorem run_then_complete (lazyStep : ∀ q, S → PMF (R q × S))
    (eagerStep : ∀ q, T → PMF (R q × T)) (complete : S → PMF T)
    (hStep : ∀ q s, completeAfter complete (lazyStep q s) =
      (complete s).bind (eagerStep q))
    (p : PassiveProtocol Q R) (s : S) :
    completeAfter complete (runQueries lazyStep p s) =
      (complete s).bind (runQueries eagerStep p) := by
  induction p generalizing s with
  | stop =>
    simp only [runQueries, completeAfter, PMF.pure_bind]
    rfl
  | query q next ih =>
    let rest (r : R q × T) :=
      (runQueries eagerStep (next r.1) r.2).map (fun out => (⟨q, r.1⟩ :: out.1, out.2))
    calc
      _ = (lazyStep q s).bind (fun x =>
            ((complete x.2).bind (runQueries eagerStep (next x.1))).map
              (fun out => (⟨q, x.1⟩ :: out.1, out.2))) := by
        rw [runQueries, completeAfter, PMF.bind_bind]
        congr 1
        funext x
        change completeAfter complete ((runQueries lazyStep (next x.1) x.2).map _) = _
        rw [completeAfter_prepend, ih]
      _ = (completeAfter complete (lazyStep q s)).bind rest := by
        simp only [completeAfter, PMF.bind_bind, PMF.bind_map, PMF.map_bind,
          Function.comp_def, rest]
      _ = _ := by
        rw [hStep, PMF.bind_bind]
        rfl

end StatefulProtocol

section NamedProtocol

variable {V N : Type*} [Fintype V] [Finite N] [DecidableEq V]

/-- A fixed injective naming, unused names, and a nonempty completion space. -/
structure NameState (V N : Type*) [DecidableEq V] where
  knownVertices : Finset V
  available : Finset N
  names : knownVertices ↪ N
  separated : ∀ v, names v ∉ available
  feasible : Nonempty (Candidates knownVertices available names)

noncomputable def sample (s : NameState V N) : PMF (V ↪ N) :=
  let _ : Fintype (Candidates s.knownVertices s.available s.names) := Fintype.ofFinite _
  let _ : Nonempty (Candidates s.knownVertices s.available s.names) := s.feasible
  (uniformPmf (Candidates s.knownVertices s.available s.names)).map Subtype.val

noncomputable def answer {I : Type*} (read : I → V) (s : NameState V N) : PMF (I → N) :=
  (sample s).map (fun f i => f (read i))

/-- A supported reply retains all old names, fixes the requested names and
removes the names used by the expanded assignment from availability. -/
def IsUpdate {I : Type*} (read : I → V) (s : NameState V N)
    (reply : I → N) (next : NameState V N) : Prop :=
  next.knownVertices = namedAfter s.knownVertices read ∧
  (∀ v : s.knownVertices, ∃ hv : v.1 ∈ next.knownVertices, next.names ⟨v.1, hv⟩ = s.names v) ∧
  (∀ i, ∃ hi : read i ∈ next.knownVertices, next.names ⟨read i, hi⟩ = reply i) ∧
  next.available = unused s.available next.knownVertices next.names

private theorem exists_next {I : Type*} (read : I → V) (s : NameState V N) :
    ∃ next : ∀ a ∈ (answer read s).support, NameState V N,
      (∀ a ha, IsUpdate read s a (next a ha)) ∧
      ((answer read s).bindOnSupport fun a ha => (sample (next a ha)).map (Prod.mk a)) =
        (sample s).map (fun f => ((fun i => f (read i)), f)) := by
  classical
  have hResult := (joint_ordered_reply_completion s.knownVertices s.available s.names
    s.separated s.feasible read).2
  let _ : Fintype (Candidates s.knownVertices s.available s.names) := Fintype.ofFinite _
  let _ : Nonempty (Candidates s.knownVertices s.available s.names) := s.feasible
  let orig := uniformPmf (Candidates s.knownVertices s.available s.names)
  let readReply (f : Candidates s.knownVertices s.available s.names) := fun i => f.1 (read i)
  let q := orig.map readReply
  have hAns : answer read s = q := by simp only [answer, sample, q, PMF.map_comp]; rfl
  have hPair : (sample s).map (fun f => ((fun i => f (read i)), f)) =
      orig.map (fun f => (readReply f, f.1)) := by
    simp only [sample, PMF.map_comp]
    rfl
  obtain ⟨kernel, hAvailable, hJoint⟩ := hResult
  let L := namedAfter s.knownVertices read
  let readState (a : I → N) (ha : a ∈ q.support) : NameState V N := by
    let assignment : L ↪ N := (hAvailable a ha).choose
    let hFeasible := (hAvailable a ha).choose_spec.2.choose
    refine ⟨L, unused s.available L assignment, assignment, ?_, hFeasible⟩
    intro v
    classical
    simp only [unused, Finset.mem_sdiff, Finset.mem_image]
    exact fun hn => hn.2 ⟨v, Finset.mem_attach _ _, rfl⟩
  have hKernel (a : I → N) (ha : a ∈ q.support) :
      sample (readState a ha) = kernel a ha := (hAvailable a ha).choose_spec.2.choose_spec.symm
  have hExact (a : I → N) (ha : a ∈ q.support) : IsUpdate read s a (readState a ha) := by
    refine ⟨rfl, ?_, ?_, rfl⟩
    · intro v
      have hv : v.1 ∈ L := Finset.mem_union_left _ v.2
      refine ⟨hv, ?_⟩
      obtain ⟨f, hf⟩ := (kernel a ha).support_nonempty
      have hPairSupport : (a, f) ∈ (q.bindOnSupport fun b hb => (kernel b hb).map (Prod.mk b)).support :=
        (PMF.mem_support_bindOnSupport_iff _ _).2
          ⟨a, ha, (PMF.mem_support_map_iff _ _ _).2 ⟨f, hf, rfl⟩⟩
      rw [hJoint] at hPairSupport
      obtain ⟨original, _, hOriginal⟩ := (PMF.mem_support_map_iff _ _ _).1 hPairSupport
      have hF : original.1 = f := congrArg Prod.snd hOriginal
      rw [← hKernel a ha] at hf
      simp only [sample, PMF.mem_support_map_iff] at hf
      obtain ⟨extended, _, hExtended⟩ := hf
      exact (extended.2.1 ⟨v.1, hv⟩).symm.trans
        ((congrArg (fun g : V ↪ N => g v.1) (hExtended.trans hF.symm)).trans (original.2.1 v))
    · intro i
      have hi : read i ∈ L := by
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, rfl⟩⟩
      exact ⟨hi, (hAvailable a ha).choose_spec.1 i hi⟩
  revert hAns
  generalize answer read s = ans
  intro hAns
  subst ans
  refine ⟨readState, hExact, ?_⟩
  exact (congrArg (fun k => q.bindOnSupport k)
    (funext fun a => funext fun ha => congrArg (fun p => p.map (Prod.mk a)) (hKernel a ha))).trans
    (hJoint.trans hPair.symm)

abbrev FullState (V N : Type*) [DecidableEq V] := NameState V N × (V ↪ N)

noncomputable def complete (s : NameState V N) : PMF (FullState V N) :=
  (sample s).map (Prod.mk s)

noncomputable def update {I : Type*} (read : I → V) (s : NameState V N)
    (r : I → N) (h : r ∈ (answer read s).support) : NameState V N :=
  (exists_next read s).choose r h

noncomputable def lazy {I : Type*} (read : I → V) (s : NameState V N) :
    PMF ((I → N) × NameState V N) :=
  (answer read s).bindOnSupport fun r h => PMF.pure (r, update read s r h)

private noncomputable def attach {I : Type*} (read : I → V) (s : NameState V N)
    (pair : (I → N) × (V ↪ N)) : (I → N) × FullState V N := by
  classical
  exact ⟨pair.1, (if h : pair.1 ∈ (answer read s).support then
    update read s pair.1 h else s, pair.2)⟩

noncomputable def eager {I : Type*} (read : NameState V N → I → V)
    (world : FullState V N) : PMF ((I → N) × FullState V N) :=
  PMF.pure (attach (read world.1) world.1 ((fun i => world.2 (read world.1 i)), world.2))

private theorem step_preserves_completion {I : Type*} (read : NameState V N → I → V)
    (s : NameState V N) :
    completeAfter complete (lazy (read s) s) =
      (complete s).bind (eager read) := by
  classical
  let q := answer (read s) s
  let place := attach (read s) s
  let observe (f : V ↪ N) := ((fun i => f (read s i)), f)
  have hLaw := (exists_next (read s) s).choose_spec.2
  change (q.bindOnSupport fun r h => (sample (update (read s) s r h)).map (Prod.mk r)) =
    (sample s).map observe at hLaw
  have hJoin := congrArg (fun p : PMF ((I → N) × (V ↪ N)) => p.map place) hLaw
  rw [postcompose_support_bind, PMF.map_comp] at hJoin
  have hEager : (complete s).bind (eager read) = (sample s).map (place ∘ observe) := by
    simp only [complete, PMF.bind_map]
    rfl
  rw [hEager, ← hJoin]
  unfold completeAfter lazy
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport, complete, PMF.map_comp, Function.comp_def]
  congr 1
  funext r hr
  apply congrArg (fun f => (sample (update (read s) s r hr)).map f)
  funext f
  simp [place, attach, hr]

/-- Completing after adaptive replies preserves the joint transcript and full state. -/
theorem adaptive_name_completion {Q : Type*} {I : Q → Type*}
    (read : (q : Q) → NameState V N → I q → V)
    (p : PassiveProtocol Q (fun q => I q → N)) (s : NameState V N) :
    let initial := complete s
    (∀ q (state : NameState V N) reply (h : reply ∈ (answer (read q state) state).support),
      IsUpdate (read q state) state reply (update (read q state) state reply h)) ∧
      completeAfter complete
        (runQueries (fun q s => lazy (read q s) s) p s) =
      initial.bind (runQueries (fun q => eager (read q)) p) := by
  intro initial
  refine ⟨fun q state reply h => (exists_next (read q state) state).choose_spec.1 reply h, ?_⟩
  exact run_then_complete _ _ _ (fun q => step_preserves_completion (read q)) p s

end NamedProtocol

end D5.S3.Combinatorics.Probability.AdaptiveNamingCompletion
