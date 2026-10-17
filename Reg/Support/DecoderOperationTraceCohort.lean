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

abbrev PeakParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O,
    Σ _ : C, (ℕ → O) → (ℕ → I) → Prop

abbrev ProcessingParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Type w

abbrev runFullSignature : Signature where
  Params := FullParams.{u,v,w}
  State p := Frame p.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frame p.1 p.2.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev peakSignature : Signature where
  Params := PeakParams.{u,v,w}
  State p := p.1 → List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → WithTop ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev processingSignature : Signature where
  Params := ProcessingParams.{u,v,w}
  State p := p.1 → Op p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ((ℕ → p.2.2) → (ℕ → p.2.1) → Prop) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def peakAnchor : ∀ (_ : Empty) (p : PeakParams.{u,v,w}), p.1 → List Bool :=
  fun e _ => nomatch e

def processingAnchor : ∀ (_ : Empty) (p : ProcessingParams.{u,v,w}),
    p.1 → Op p.1 p.2.1 p.2.2 := fun e _ => nomatch e

def runFullReadout : ∀ (_ : Unit) (p : FullParams.{u,v,w}),
    Frame p.1 p.2.2.1 → Frame p.1 p.2.2.1 → Prop :=
  fun _ p s => Run p.2.2.2.1 (full p.2.2.2.2) s

def peakReadout : ∀ (_ : Unit) (p : PeakParams.{u,v,w}),
    (p.1 → List Bool) → ℕ → WithTop ℕ :=
  fun _ p enc => Peak p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 enc

def processingReadout : ∀ (_ : Unit) (p : ProcessingParams.{u,v,w}),
    (p.1 → Op p.1 p.2.1 p.2.2) →
      p.1 → ((ℕ → p.2.2) → (ℕ → p.2.1) → Prop) → Prop :=
  fun _ p action => Processing action

def runFullActual : Realization runFullSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    runFullSignature.{u,v,w} runFullReadout.{u,v,w} fullAnchor.{u,v,w}

def peakActual : Realization peakSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), u, 0, 0, 0}
    peakSignature.{u,v,w} peakReadout.{u,v,w} peakAnchor.{u,v,w}

def processingActual : Realization processingSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), max u (max v w), 0, max u (max v w), 0}
    processingSignature.{u,v,w} processingReadout.{u,v,w} processingAnchor.{u,v,w}

def cutFalse : Realization cutSignature.{u,v,w} :=
  realize cutSignature (fun _ _ _ _ => False) cutAnchor

def runFullFalse : Realization runFullSignature.{u,v,w} :=
  realize runFullSignature (fun _ _ _ _ => False) fullAnchor

def peakZero : Realization peakSignature.{u,v,w} :=
  realize peakSignature (fun _ _ _ _ => 0) peakAnchor

def peakDescending : Realization peakSignature.{u,v,w} :=
  realize peakSignature (fun _ _ _ H => Nat.casesOn H 1 (fun _ => 0)) peakAnchor

def drainFalse : Realization drainSignature.{u,v,w} :=
  realize drainSignature (fun _ _ _ _ => False) drainAnchor

def processingFalse : Realization processingSignature.{u,v,w} :=
  realize processingSignature (fun _ _ _ _ _ => False) processingAnchor

abbrev actualCutExistsArena : Arena where
  signature := cutSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (InD : (ℕ → O) → Prop)
      (processing : Processing action initial Record)
      (live : ∀ a r, Record a r → InD a → ∀ p,
        ∃ t, Run action (full r) ⟨initial,0,[]⟩ t ∧ p < t.output.length)
      (a : ℕ → O) (r : ℕ → I) (record : Record a r) (finite : InD a) (n : ℕ),
    ∃ t, R.readout () ⟨C,I,O,action,initial⟩ (front r n) t ∧
        Run action (full r) ⟨initial,0,[]⟩ t

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

abbrev peakBoundArena : Arena where
  signature := peakSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ) (c : C)
      (hc : ReachThrough action initial Record H c),
    ((enc c).length : WithTop ℕ) ≤ R.readout () ⟨C,I,O,action,initial,Record⟩ enc H

abbrev peakTraceBoundArena : Arena where
  signature := peakSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool) (H : ℕ)
      (a : ℕ → O) (r : ℕ → I) (t : Frame C O) (v : List C)
      (ha : Record a r) (hr : Trace action (full r) ⟨initial,0,[]⟩ t v)
      (hq : t.acquired ≤ H) (c : C) (hc : c ∈ v),
    ((enc c).length : WithTop ℕ) ≤ R.readout () ⟨C,I,O,action,initial,Record⟩ enc H

abbrev peakMonotoneArena : Arena where
  signature := peakSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool),
    Monotone (R.readout () ⟨C,I,O,action,initial,Record⟩ enc)

abbrev initialDrainArena : Arena where
  signature := drainSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (r : ℕ → I) (t : Frame C O)
      (hr : Run action (full r) ⟨initial,0,[]⟩ t) (hp : 0 < t.acquired),
    ∃ u, R.readout () ⟨C,I,O,action⟩ ⟨initial,0,[]⟩ u

abbrev processingPairArena : Arena where
  signature := processingSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
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
        ∃ t, Drain action ⟨d,q+1,o++w⟩ t),
    R.readout () ⟨C,I,O⟩ action initial Record

namespace Models

/-- Acquisitions emit one symbol and are ready at every result state. -/
def acquirer.{c,i,o} {I : Type i} {O : Type o} (emit : I → O) :
    PUnit.{c + 1} → Op (PUnit.{c + 1}) I O :=
  fun _ => .acquire (fun x => some (PUnit.unit, [emit x]))

theorem acquirer_drain {I : Type v} {O : Type w} (emit : I → O)
    (s : Frame (PUnit.{u + 1}) O) : Drain (acquirer emit) s s :=
  ⟨⟨_, Trace.refl⟩, Or.inr ⟨_, rfl⟩⟩

theorem acquirer_processing {I : Type v} {O : Type w} (emit : I → O)
    (Record : (ℕ → O) → (ℕ → I) → Prop) :
    Processing (acquirer.{u,v,w} emit) PUnit.unit Record := by
  refine ⟨⟨_, acquirer_drain emit _⟩, ?_⟩
  intro a r record c d q o batch f hr instruction result
  exact ⟨_, acquirer_drain emit _⟩

theorem acquirer_run {I : Type v} {O : Type w} (emit : I → O)
    (r : ℕ → I) (o : O) (same : ∀ q, emit (r q) = o) (n : ℕ) :
    Run (acquirer.{u,v,w} emit) (full r) ⟨PUnit.unit,0,[]⟩
      ⟨PUnit.unit,n,List.replicate n o⟩ := by
  induction n with
  | zero => exact ⟨_, Trace.refl⟩
  | succ n ih =>
    obtain ⟨vertices, hv⟩ := ih
    refine ⟨_, hv.tail ?_⟩
    simpa [List.replicate_add] using
      (Step.acquire (action := acquirer emit) (input := full r)
        PUnit.unit PUnit.unit n (List.replicate n o) [o]
        (fun x => some (PUnit.unit, [emit x])) (r n) rfl rfl (by rw [same n]))

def unitEmit : PUnit.{v + 1} → PUnit.{w + 1} := fun _ => PUnit.unit

theorem unit_live (a : ℕ → PUnit.{w + 1}) (r : ℕ → PUnit.{v + 1})
    (_record : True) (_finite : True) (p : ℕ) :
    ∃ t, Run (acquirer.{u,v,w} unitEmit) (full r) ⟨PUnit.unit,0,[]⟩ t ∧
      p < t.output.length := by
  refine ⟨_, acquirer_run unitEmit r PUnit.unit (fun _ => rfl) (p+1), ?_⟩
  simp

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

def echoEmit.{i,o} : ULift.{i} Bool → ULift.{o} Bool := fun x => ⟨x.down⟩
def boolStream (b : Bool) : ℕ → ULift.{v} Bool := fun _ => ⟨b⟩
def echoRecord (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool) : Prop :=
  ∃ b : Bool, a = boolStream b ∧ r = boolStream b

theorem echo_trace (b : Bool) {t : Frame (PUnit.{u + 1}) (ULift.{w} Bool)}
    {vertices : List (PUnit.{u + 1})}
    (h : Trace (acquirer.{u,v,w} echoEmit) (full (boolStream b))
      ⟨PUnit.unit,0,[]⟩ t vertices) : t.output = List.replicate t.acquired ⟨b⟩ := by
  induction h with
  | refl => rfl
  | @tail middle finish vertices h edge ih =>
    cases edge with
    | internal c d q old batch instruction =>
      simp [acquirer] at instruction
    | acquire c d q old batch f x instruction available result =>
      have hf : (fun x : ULift.{v} Bool =>
          some (PUnit.unit, [echoEmit.{v,w} x])) = f := Op.acquire.inj instruction
      subst f
      have hx : (ULift.up b : ULift.{v} Bool) = x := Option.some.inj available
      subst x
      have he : (PUnit.unit, [ULift.up b]) = (d, batch) := Option.some.inj result
      have hb : batch = [ULift.up b] := (congrArg Prod.snd he).symm
      dsimp only at ih ⊢
      rw [ih, hb]
      simp [List.replicate_add]

theorem echo_safe (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool)
    (record : echoRecord a r) (t : Frame (PUnit.{u + 1}) (ULift.{w} Bool))
    (hr : Run (acquirer.{u,v,w} echoEmit) (full r) ⟨PUnit.unit,0,[]⟩ t)
    (p : ℕ) (hp : p < t.output.length) : t.output[p] = a p := by
  rcases record with ⟨b, rfl, rfl⟩
  obtain ⟨vertices, hv⟩ := hr
  have equal := echo_trace b hv
  simp [equal, boolStream]

theorem echo_live (a : ℕ → ULift.{w} Bool) (r : ℕ → ULift.{v} Bool)
    (record : echoRecord a r) (_finite : True) (p : ℕ) :
    ∃ t, Run (acquirer.{u,v,w} echoEmit) (full r) ⟨PUnit.unit,0,[]⟩ t ∧
      p < t.output.length := by
  rcases record with ⟨b, rfl, rfl⟩
  refine ⟨_, acquirer_run echoEmit (boolStream b) ⟨b⟩ (fun _ => rfl) (p+1), ?_⟩
  simp

end Models

theorem actual_cut_exists_rejected : ¬ actualCutExistsArena.{u,v,w}.Law cutFalse := by
  intro h
  obtain ⟨t, impossible, _⟩ := h (Models.acquirer.{u,v,w} Models.unitEmit) PUnit.unit
    (fun _ _ => True) (fun _ => True)
    (Models.acquirer_processing Models.unitEmit _) Models.unit_live
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) True.intro True.intro 0
  exact impossible

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

private theorem initial_reachable :
    ReachThrough stop.{u,v,w} PUnit.unit (fun _ _ => True) 0 PUnit.unit :=
  ⟨(fun _ => PUnit.unit), stream, frame 0, True.intro, ⟨_, Trace.refl⟩, le_rfl, rfl⟩

theorem peak_bound_rejected : ¬ peakBoundArena.{u,v,w}.Law peakZero := by
  intro h
  have impossible := h stop.{u,v,w} PUnit.unit (fun _ _ => True)
    (fun _ => [false]) 0 PUnit.unit initial_reachable
  change (1 : WithTop ℕ) ≤ 0 at impossible
  simpa using impossible

theorem peak_trace_bound_rejected : ¬ peakTraceBoundArena.{u,v,w}.Law peakZero := by
  intro h
  have impossible := h stop.{u,v,w} PUnit.unit (fun _ _ => True)
    (fun _ => [false]) 0 (fun _ => PUnit.unit) stream (frame 0) [PUnit.unit]
    True.intro Trace.refl (le_refl 0) PUnit.unit (by simp)
  change (1 : WithTop ℕ) ≤ 0 at impossible
  simpa using impossible

theorem peak_monotone_rejected : ¬ peakMonotoneArena.{u,v,w}.Law peakDescending := by
  intro h
  have impossible := h stop.{u,v,w} PUnit.unit (fun _ _ => True)
    (fun _ => []) (show 0 ≤ 1 by omega)
  change (1 : WithTop ℕ) ≤ 0 at impossible
  simpa using impossible

theorem initial_drain_rejected : ¬ initialDrainArena.{u,v,w}.Law drainFalse := by
  intro h
  obtain ⟨t, impossible⟩ := h (Models.acquirer.{u,v,w} Models.unitEmit) PUnit.unit stream
    ⟨PUnit.unit,1,[PUnit.unit]⟩
    (Models.acquirer_run Models.unitEmit stream PUnit.unit (fun _ => rfl) 1)
    (by decide)
  exact impossible

theorem processing_pair_rejected : ¬ processingPairArena.{u,v,w}.Law processingFalse := by
  intro h
  exact h (Models.acquirer.{u,v,w} Models.echoEmit) PUnit.unit Models.echoRecord
    (fun _ => True) Models.echo_safe Models.echo_live
    (Models.boolStream false) (Models.boolStream true)
    (Models.boolStream false) (Models.boolStream true)
    ⟨false, rfl, rfl⟩ ⟨true, rfl, rfl⟩ True.intro
    (by intro equal; have impossible := congrArg ULift.down equal; cases impossible)
    (Models.acquirer_processing Models.echoEmit Models.echoRecord).2

theorem run_full_dependence : ObservationalDependence runFullSignature.{u,v,w} runFullActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop, stream⟩,
    frame 0, frame 1, ?_⟩
  intro h
  have equal : Run stop.{u,v,w} (full stream) (frame 0) (frame 0) =
      Run stop.{u,v,w} (full stream) (frame 1) (frame 0) := congrFun h (frame 0)
  exact no_run_back _ (equal.mp ⟨_, Trace.refl⟩)

private theorem constant_peak (bits : List Bool) :
    Peak stop.{u,v,w} PUnit.unit (fun _ _ => True) (fun _ => bits) 0 =
      (bits.length : WithTop ℕ) := by
  apply le_antisymm
  · unfold Peak
    exact iSup_le (fun _ => iSup_le (fun _ => le_rfl))
  · exact peak_bound stop PUnit.unit (fun _ _ => True) (fun _ => bits)
      0 PUnit.unit initial_reachable

theorem peak_dependence : ObservationalDependence peakSignature.{u,v,w} peakActual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}, stop,
    PUnit.unit, (fun _ _ => True)⟩, (fun _ => []), (fun _ => [false]), ?_⟩
  intro h
  have equal : Peak stop.{u,v,w} PUnit.unit (fun _ _ => True) (fun _ => []) 0 =
      Peak stop.{u,v,w} PUnit.unit (fun _ _ => True) (fun _ => [false]) 0 := congrFun h 0
  rw [constant_peak, constant_peak] at equal
  simpa using equal

theorem processing_dependence :
    ObservationalDependence processingSignature.{u,v,w} processingActual := by
  intro i
  let loop : PUnit.{u + 1} → Op (PUnit.{u + 1}) (PUnit.{v + 1}) (PUnit.{w + 1}) :=
    fun c => .internal c []
  refine ⟨⟨PUnit.{u + 1}, PUnit.{v + 1}, PUnit.{w + 1}⟩, stop, loop, ?_⟩
  intro h
  have positive : Processing stop.{u,v,w} PUnit.unit (fun _ _ => False) :=
    ⟨⟨frame 0, stopped_drain⟩, by intro a r impossible; exact impossible.elim⟩
  have equal : Processing stop.{u,v,w} PUnit.unit (fun _ _ => False) =
      Processing loop PUnit.unit (fun _ _ => False) :=
    congrFun (congrFun h PUnit.unit) (fun _ _ => False)
  obtain ⟨t, _, ready⟩ := (equal.mp positive).1
  rcases ready with stopped | ⟨f, acquire⟩
  · cases stopped
  · cases acquire

def actualCutExistsEvidence : Registration actualCutExistsArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_cut_exists.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), v, 0, max u w, 0}
    cutSignature.{u,v,w} cutReadout.{u,v,w} cutAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@actual_cut_exists.{u,v,w}, cutFalse, actual_cut_exists_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cutFalse, ?_, rfl, actual_cut_exists_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := cut_dependence

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

def peakBoundEvidence : Registration peakBoundArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_bound.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), u, 0, 0, 0}
    peakSignature.{u,v,w} peakReadout.{u,v,w} peakAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@peak_bound.{u,v,w}, peakZero, peak_bound_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨peakZero, ?_, rfl, peak_bound_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := peak_dependence

def peakTraceBoundEvidence : Registration peakTraceBoundArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_trace_bound.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), u, 0, 0, 0}
    peakSignature.{u,v,w} peakReadout.{u,v,w} peakAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@peak_trace_bound.{u,v,w}, peakZero, peak_trace_bound_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨peakZero, ?_, rfl, peak_trace_bound_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := peak_dependence

def peakMonotoneEvidence : Registration peakMonotoneArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_monotone.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), u, 0, 0, 0}
    peakSignature.{u,v,w} peakReadout.{u,v,w} peakAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@peak_monotone.{u,v,w}, peakDescending, peak_monotone_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨peakDescending, ?_, rfl, peak_monotone_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := peak_dependence

def initialDrainEvidence : Registration initialDrainArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.initial_drain_of_acquired_run.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u w, 0, max u w, 0}
    drainSignature.{u,v,w} drainReadout.{u,v,w} drainAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@initial_drain_of_acquired_run.{u,v,w}, drainFalse, initial_drain_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨drainFalse, ?_, rfl, initial_drain_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := drain_dependence

def processingPairEvidence : Registration processingPairArena.{u,v,w}
    (type_of% (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.processing_of_safe_live_pair.{u,v,w})) where
  actual := realize.{max (u + 1) (max (v + 1) (w + 1)), max u (max v w), 0, max u (max v w), 0}
    processingSignature.{u,v,w} processingReadout.{u,v,w} processingAnchor.{u,v,w}
  bridge := Iff.rfl
  variation := ⟨@processing_of_safe_live_pair.{u,v,w}, processingFalse, processing_pair_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨processingFalse, ?_, rfl, processing_pair_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := processing_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort
