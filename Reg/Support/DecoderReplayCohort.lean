import D5.S3.ConceptDynamics.Coding.DecoderReplay
import Reg.Support.DecoderOperationTraceCohort
import Batteries.Tactic.OpenPrivate

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.Cohort

open private frame stop stream no_run_back from Reg.Support.DecoderOperationTraceCohort

open _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort

universe u v w
noncomputable section

def fullTrue : Realization fullSignature.{u,v,w} :=
  realize fullSignature (fun _ _ _ _ _ => True) fullAnchor

abbrev traceReplayArena : Arena where
  signature := fullSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {r : ℕ → I} {s t : Frame C O} {v : List C}
    (h : R.readout () ⟨C, I, O, action, r⟩ s t v),
    ∃ m w, t.acquired = s.acquired + m ∧ t.output = s.output ++ w ∧
      ∀ (r' : ℕ → I) (q' : ℕ) (o' : List O),
        (∀ j, r (s.acquired+j) = r' (q'+j)) →
        Trace action (full r') ⟨s.state,q',o'⟩ ⟨t.state,q'+m,o'++w⟩ v

theorem trace_replay_rejected : ¬ traceReplayArena.{u,v,w}.Law fullTrue := by
  intro h
  obtain ⟨m, batch, acquired, rest⟩ := h (action := stop.{u,v,w}) (r := stream)
    (s := frame 1) (t := frame 0) (v := []) True.intro
  change 0 = 1 + m at acquired
  omega

def traceReplayEvidence : Registration traceReplayArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_replay.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    fullSignature.{u,v,w} fullReadout.{u,v,w} fullAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@trace_replay.{u,v,w}, fullTrue, trace_replay_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fullTrue, ?_, rfl, trace_replay_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := full_dependence

abbrev runFullSignature : Signature where
  Params := FullParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def runFullReadout : ∀ (_ : Unit) (p : FullParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → Prop :=
  fun _ p s => Run p.2.2.2.1 (full p.2.2.2.2) s

def runFullActual : Realization runFullSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runFullSignature.{u,v,w} runFullReadout.{u,v,w} fullAnchor.{u,v,w}

def runFullFalse : Realization runFullSignature.{u,v,w} :=
  realize runFullSignature (fun _ _ _ _ => False) fullAnchor

abbrev actualAddressEqArena : Arena where
  signature := runFullSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
      (safe : ∀ a r, Record a r → ∀ t,
        R.readout () ⟨C,I,O,action,r⟩ ⟨initial,0,[]⟩ t → ∀ p (hp : p < t.output.length), t.output[p] = a p)
      (live : ∀ a r, Record a r → InD a → ∀ p,
        ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
      (a b : ℕ → O) (r r' : ℕ → I) (ha : Record a r) (hb : Record b r') (hd : InD a)
      (s s' : Frame C O)
      (hs : Run action (full r) ⟨initial,0,[]⟩ s)
      (hs' : Run action (full r') ⟨initial,0,[]⟩ s')
      (state : s.state = s'.state) (output : s.output = s'.output)
      (same : ∀ j, r (s.acquired+j) = r' (s'.acquired+j)),
    a = b

namespace Models

def emitter.{c,i,o} : PUnit.{c + 1} →
    Op (PUnit.{c + 1}) (PUnit.{i + 1}) (ULift.{o} Bool) :=
  fun _ => .internal PUnit.unit [⟨false⟩]

theorem emitter_run (r : ℕ → PUnit.{v + 1}) (n : ℕ) :
    Run emitter.{u,v,w} (full r) ⟨PUnit.unit,0,[]⟩
      ⟨PUnit.unit,0,List.replicate n (ULift.up false)⟩ := by
  induction n with
  | zero => exact ⟨_, Trace.refl⟩
  | succ n ih =>
    obtain ⟨vertices, hv⟩ := ih
    refine ⟨_, hv.tail ?_⟩
    simpa [List.replicate_add] using
      (Step.internal (action := emitter.{u,v,w}) (input := full r)
        PUnit.unit PUnit.unit 0 (List.replicate n (ULift.up false)) [⟨false⟩] rfl)

theorem emitter_live (a : ℕ → ULift.{w} Bool) (r : ℕ → PUnit.{v + 1})
    (_record : True) (_finite : True) (p : ℕ) :
    ∃ t, Run emitter.{u,v,w} (full r) ⟨PUnit.unit,0,[]⟩ t ∧
      p < t.output.length := by
  refine ⟨_, emitter_run r (p+1), ?_⟩
  simp

end Models

theorem actual_address_eq_rejected : ¬ actualAddressEqArena.{u,v,w}.Law runFullFalse := by
  intro h
  have equal := h Models.emitter.{u,v,w} PUnit.unit (fun _ _ => True) (fun _ => True)
    (by intro a r record t impossible; exact impossible.elim) Models.emitter_live
    (fun _ => ULift.up false) (fun _ => ULift.up true)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) True.intro True.intro True.intro
    ⟨PUnit.unit,0,[]⟩ ⟨PUnit.unit,0,[]⟩ ⟨_, Trace.refl⟩ ⟨_, Trace.refl⟩
    rfl rfl (fun _ => rfl)
  have impossible : false = true := congrArg ULift.down (congrFun equal 0)
  cases impossible

theorem run_full_dependence : ObservationalDependence runFullSignature.{u,v,w} runFullActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, stream⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Run stop.{u,v,w} (full stream) (frame 0) (frame 0) =
      Run stop.{u,v,w} (full stream) (frame 1) (frame 0) := congrFun h (frame 0)
  exact no_run_back _ (equal.mp ⟨_, Trace.refl⟩)

def actualAddressEqEvidence : Registration actualAddressEqArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_address_eq.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runFullSignature.{u,v,w} runFullReadout.{u,v,w} fullAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@actual_address_eq.{u,v,w}, runFullFalse, actual_address_eq_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runFullFalse, ?_, rfl, actual_address_eq_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_full_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.Cohort
