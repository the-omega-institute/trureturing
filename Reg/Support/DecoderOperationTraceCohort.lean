import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort

universe u v w
noncomputable section

abbrev InputParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O, ℕ → Option I

abbrev FullParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O, ℕ → I

abbrev CutParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O, C

abbrev DrainParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, C → Op C I O

abbrev runSignature : Signature where
  Params := InputParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev traceSignature : Signature where
  Params := InputParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → List p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev fullSignature : Signature where
  Params := FullParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → List p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev cutSignature : Signature where
  Params := CutParams.{u,v,w}
  State p := List p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev drainSignature : Signature where
  Params := DrainParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Shared operands keep the evidence and enrolled descriptor on the same expression. -/
def inputAnchor : ∀ (_ : Empty) (p : InputParams.{u,v,w}), Frame p.1 p.2.2.1 :=
  fun e _ => nomatch e

def fullAnchor : ∀ (_ : Empty) (p : FullParams.{u,v,w}), Frame p.1 p.2.2.1 :=
  fun e _ => nomatch e

def cutAnchor : ∀ (_ : Empty) (p : CutParams.{u,v,w}), List p.2.1 :=
  fun e _ => nomatch e

def drainAnchor : ∀ (_ : Empty) (p : DrainParams.{u,v,w}), Frame p.1 p.2.2.1 :=
  fun e _ => nomatch e

def runReadout : ∀ (_ : Unit) (p : InputParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → Prop :=
  fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s

def traceReadout : ∀ (_ : Unit) (p : InputParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → List p.1 → Prop :=
  fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s

def fullReadout : ∀ (_ : Unit) (p : FullParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → List p.1 → Prop :=
  fun _ p s => Trace p.2.2.2.1 (full p.2.2.2.2) s

def cutReadout : ∀ (_ : Unit) (p : CutParams.{u,v,w}),
    List p.2.1 → Frame p.1 p.2.2.1 → Prop :=
  fun _ p h => Cut p.2.2.2.1 p.2.2.2.2 h

def drainReadout : ∀ (_ : Unit) (p : DrainParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → Prop :=
  fun _ p s => Drain p.2.2.2 s

def runActual : Realization runSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runSignature.{u,v,w} runReadout.{u,v,w} inputAnchor.{u,v,w}

def traceActual : Realization traceSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    traceSignature.{u,v,w} traceReadout.{u,v,w} inputAnchor.{u,v,w}

def fullActual : Realization fullSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    fullSignature.{u,v,w} fullReadout.{u,v,w} fullAnchor.{u,v,w}

def cutActual : Realization cutSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), v, 0, max u w, 0}
    cutSignature.{u,v,w} cutReadout.{u,v,w} cutAnchor.{u,v,w}

def drainActual : Realization drainSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    drainSignature.{u,v,w} drainReadout.{u,v,w} drainAnchor.{u,v,w}

def runTrue : Realization runSignature.{u,v,w} :=
  realize runSignature (fun _ _ _ _ => True) inputAnchor

def runFalse : Realization runSignature.{u,v,w} :=
  realize runSignature (fun _ _ _ _ => False) inputAnchor

def traceFalse : Realization traceSignature.{u,v,w} :=
  realize traceSignature (fun _ _ _ _ _ => False) inputAnchor

def fullFalse : Realization fullSignature.{u,v,w} :=
  realize fullSignature (fun _ _ _ _ _ => False) fullAnchor

def fullTrue : Realization fullSignature.{u,v,w} :=
  realize fullSignature (fun _ _ _ _ _ => True) fullAnchor

def cutTrue : Realization cutSignature.{u,v,w} :=
  realize cutSignature (fun _ _ _ _ => True) cutAnchor

def drainTrue : Realization drainSignature.{u,v,w} :=
  realize drainSignature (fun _ _ _ _ => True) drainAnchor

abbrev runMonoArena : Arena where
  signature := runSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input : ℕ → Option I} {s t : Frame C O}
    (h : R.readout () ⟨C, I, O, action, input⟩ s t),
    s.acquired ≤ t.acquired ∧ s.output.length ≤ t.output.length

abbrev traceInputTransferArena : Arena where
  signature := traceSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {input input' : ℕ → Option I}
    {s t : Frame C O} {v : List C} (h : Trace action input s t v)
    (same : ∀ q, s.acquired ≤ q → q < t.acquired → input q = input' q),
    R.readout () ⟨C, I, O, action, input'⟩ s t v

abbrev prefixTraceIffArena : Arena where
  signature := fullSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} (r : ℕ → I) (n : ℕ)
    {s t : Frame C O} {v : List C} (bound : t.acquired ≤ n),
    R.readout () ⟨C, I, O, action, r⟩ s t v ↔
      Trace action (availablePrefix (front r n)) s t v

abbrev cutUniqueArena : Arena where
  signature := cutSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C) (h : List I) {s t : Frame C O}
    (hs : R.readout () ⟨C, I, O, action, initial⟩ h s)
    (ht : Cut action initial h t), s = t

abbrev traceReplayArena : Arena where
  signature := fullSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {r : ℕ → I} {s t : Frame C O} {v : List C}
    (h : R.readout () ⟨C, I, O, action, r⟩ s t v),
    ∃ m w, t.acquired = s.acquired + m ∧ t.output = s.output ++ w ∧
      ∀ (r' : ℕ → I) (q' : ℕ) (o' : List O),
        (∀ j, r (s.acquired+j) = r' (q'+j)) →
        Trace action (full r') ⟨s.state,q',o'⟩ ⟨t.state,q'+m,o'++w⟩ v

abbrev drainAcquiredArena : Arena where
  signature := drainSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {s t : Frame C O}
    (h : R.readout () ⟨C, I, O, action⟩ s t), t.acquired = s.acquired

abbrev drainRunArena : Arena where
  signature := runSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    {action : C → Op C I O} {s t : Frame C O}
    (h : Drain action s t) (input : ℕ → Option I),
    R.readout () ⟨C, I, O, action, input⟩ s t

/-- Inhabited countermodels vary the whole Law without restricting its carriers. -/
private def frame (n : ℕ) : Frame (PUnit.{u + 1}) (PUnit.{w + 1}) :=
  ⟨PUnit.unit, n, []⟩

private def stop : PUnit.{u + 1} →
    Op (PUnit.{u + 1}) (PUnit.{v + 1}) (PUnit.{w + 1}) := fun _ => .stopped

private def noneInput : ℕ → Option (PUnit.{v + 1}) := fun _ => none

private def stream : ℕ → PUnit.{v + 1} := fun _ => PUnit.unit

private theorem no_run_back (input : ℕ → Option (PUnit.{v + 1})) :
    ¬ Run stop.{u,v,w} input (frame 1) (frame 0) := by
  intro h
  have bound := (run_mono h).1
  change 1 ≤ 0 at bound
  omega

private theorem stopped_cut : Cut stop.{u,v,w} PUnit.unit [] (frame 0) :=
  ⟨⟨_, Trace.refl⟩, rfl, Or.inl rfl⟩

private theorem stopped_drain : Drain stop.{u,v,w} (frame 0) (frame 0) :=
  ⟨⟨_, Trace.refl⟩, Or.inl rfl⟩

theorem run_mono_rejected : ¬ runMonoArena.{u,v,w}.Law runTrue := by
  intro h
  have bound := (h (action := stop.{u,v,w}) (input := noneInput)
    (s := frame 1) (t := frame 0) True.intro).1
  change 1 ≤ 0 at bound
  omega

theorem trace_input_transfer_rejected : ¬ traceInputTransferArena.{u,v,w}.Law traceFalse := by
  intro h
  exact h (action := stop.{u,v,w}) (input := noneInput) (input' := noneInput)
    (s := frame 0) (t := frame 0) (v := [PUnit.unit]) Trace.refl (by intros; rfl)

theorem prefix_trace_iff_rejected : ¬ prefixTraceIffArena.{u,v,w}.Law fullFalse := by
  intro h
  exact (h (action := stop.{u,v,w}) stream 0
    (s := frame 0) (t := frame 0) (v := [PUnit.unit]) (Nat.le_refl 0)).mpr Trace.refl

theorem cut_unique_rejected : ¬ cutUniqueArena.{u,v,w}.Law cutTrue := by
  intro h
  have equal := h stop.{u,v,w} PUnit.unit []
    (s := frame 1) (t := frame 0) True.intro stopped_cut
  have impossible : (1 : ℕ) = 0 := congrArg Frame.acquired equal
  omega

theorem trace_replay_rejected : ¬ traceReplayArena.{u,v,w}.Law fullTrue := by
  intro h
  obtain ⟨m, batch, acquired, rest⟩ := h (action := stop.{u,v,w}) (r := stream)
    (s := frame 1) (t := frame 0) (v := []) True.intro
  change 0 = 1 + m at acquired
  omega

theorem drain_acquired_rejected : ¬ drainAcquiredArena.{u,v,w}.Law drainTrue := by
  intro h
  have equal := h (action := stop.{u,v,w}) (s := frame 0) (t := frame 1) True.intro
  change 1 = 0 at equal
  omega

theorem drain_run_rejected : ¬ drainRunArena.{u,v,w}.Law runFalse := by
  intro h
  exact h (action := stop.{u,v,w}) (s := frame 0) (t := frame 0) stopped_drain noneInput

theorem run_dependence : ObservationalDependence runSignature.{u,v,w} runActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, noneInput⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Run stop.{u,v,w} noneInput (frame 0) (frame 0) =
      Run stop.{u,v,w} noneInput (frame 1) (frame 0) := congrFun h (frame 0)
  exact no_run_back _ (equal.mp ⟨_, Trace.refl⟩)

theorem trace_dependence : ObservationalDependence traceSignature.{u,v,w} traceActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, noneInput⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Trace stop.{u,v,w} noneInput (frame 0) (frame 0) [PUnit.unit] =
      Trace stop.{u,v,w} noneInput (frame 1) (frame 0) [PUnit.unit] :=
    congrFun (congrFun h (frame 0)) [PUnit.unit]
  exact no_run_back _ ⟨_, equal.mp Trace.refl⟩

theorem full_dependence : ObservationalDependence fullSignature.{u,v,w} fullActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, stream⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Trace stop.{u,v,w} (full stream) (frame 0) (frame 0) [PUnit.unit] =
      Trace stop.{u,v,w} (full stream) (frame 1) (frame 0) [PUnit.unit] :=
    congrFun (congrFun h (frame 0)) [PUnit.unit]
  exact no_run_back _ ⟨_, equal.mp Trace.refl⟩

theorem cut_dependence : ObservationalDependence cutSignature.{u,v,w} cutActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, PUnit.unit⟩,
    [], [PUnit.unit], ?_⟩
  intro h
  have equal : Cut stop.{u,v,w} PUnit.unit [] (frame 0) =
      Cut stop.{u,v,w} PUnit.unit [PUnit.unit] (frame 0) := congrFun h (frame 0)
  have impossible := (equal.mp stopped_cut).2.1
  change 0 = 1 at impossible
  omega

theorem drain_dependence : ObservationalDependence drainSignature.{u,v,w} drainActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Drain stop.{u,v,w} (frame 0) (frame 0) =
      Drain stop.{u,v,w} (frame 1) (frame 0) := congrFun h (frame 0)
  exact no_run_back _ (equal.mp stopped_drain).1

def runMonoEvidence : Registration runMonoArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_mono.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runSignature.{u,v,w} runReadout.{u,v,w} inputAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@run_mono.{u,v,w}, runTrue, run_mono_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runTrue, ?_, rfl, run_mono_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

def traceInputTransferEvidence : Registration traceInputTransferArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_input_transfer.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    traceSignature.{u,v,w} traceReadout.{u,v,w} inputAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@trace_input_transfer.{u,v,w}, traceFalse, trace_input_transfer_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨traceFalse, ?_, rfl, trace_input_transfer_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := trace_dependence

def prefixTraceIffEvidence : Registration prefixTraceIffArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.prefix_trace_iff.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    fullSignature.{u,v,w} fullReadout.{u,v,w} fullAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@prefix_trace_iff.{u,v,w}, fullFalse, prefix_trace_iff_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fullFalse, ?_, rfl, prefix_trace_iff_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := full_dependence

def cutUniqueEvidence : Registration cutUniqueArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.cut_unique.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), v, 0, max u w, 0}
    cutSignature.{u,v,w} cutReadout.{u,v,w} cutAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@cut_unique.{u,v,w}, cutTrue, cut_unique_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cutTrue, ?_, rfl, cut_unique_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := cut_dependence

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

def drainAcquiredEvidence : Registration drainAcquiredArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_acquired.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    drainSignature.{u,v,w} drainReadout.{u,v,w} drainAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@drain_acquired.{u,v,w}, drainTrue, drain_acquired_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨drainTrue, ?_, rfl, drain_acquired_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := drain_dependence

def drainRunEvidence : Registration drainRunArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_run.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runSignature.{u,v,w} runReadout.{u,v,w} inputAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@drain_run.{u,v,w}, runFalse, drain_run_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨runFalse, ?_, rfl, drain_run_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := run_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort
