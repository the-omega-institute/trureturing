import D5.S3.ConceptDynamics.Coding.DecoderPeak
import Reg.Support.DecoderOperationTraceCohort
import Batteries.Tactic.OpenPrivate

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.Cohort

open private frame stop stream from Reg.Support.DecoderOperationTraceCohort

open _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort

universe u v w
noncomputable section

abbrev PeakParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ C : Type u, Σ I : Type v, Σ O : Type w, Σ _ : C → Op C I O,
    Σ _ : C, (ℕ → O) → (ℕ → I) → Prop

abbrev peakSignature : Signature where
  Params := PeakParams.{u,v,w}
  State p := p.1 → List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → WithTop ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def peakAnchor : ∀ (_ : Empty) (p : PeakParams.{u,v,w}), p.1 → List Bool :=
  fun e _ => nomatch e

def peakReadout : ∀ (_ : Unit) (p : PeakParams.{u,v,w}),
    (p.1 → List Bool) → ℕ → WithTop ℕ :=
  fun _ p enc => Peak p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 enc

def peakActual : Realization peakSignature.{u,v,w} :=
  realize.{max (u + 1) (max (v + 1) (w + 1)), u, 0, 0, 0}
    peakSignature.{u,v,w} peakReadout.{u,v,w} peakAnchor.{u,v,w}

def peakZero : Realization peakSignature.{u,v,w} :=
  realize peakSignature (fun _ _ _ _ => 0) peakAnchor

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

def peakDescending : Realization peakSignature.{u,v,w} :=
  realize peakSignature (fun _ _ _ H => Nat.casesOn H 1 (fun _ => 0)) peakAnchor

abbrev peakMonotoneArena : Arena where
  signature := peakSignature.{u,v,w}
  Law R := ∀ {C : Type u} {I : Type v} {O : Type w}
    (action : C → Op C I O) (initial : C)
      (Record : (ℕ → O) → (ℕ → I) → Prop) (enc : C → List Bool),
    Monotone (R.readout () ⟨C,I,O,action,initial,Record⟩ enc)

theorem peak_monotone_rejected : ¬ peakMonotoneArena.{u,v,w}.Law peakDescending := by
  intro h
  have impossible := h stop.{u,v,w} PUnit.unit (fun _ _ => True)
    (fun _ => []) (show 0 ≤ 1 by omega)
  change (1 : WithTop ℕ) ≤ 0 at impossible
  simpa using impossible

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

end

end Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.Cohort
