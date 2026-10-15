import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.PureLossIncompatibility
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation (e)
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (fockPair tensor)
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
  (fockPair_apply)
open scoped BigOperators ComplexOrder ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the effect of a binary measurement at the chosen outcome. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2)
    (fun _ => Fin 2 → Op) (fun _ => Op)

def actual : Realization signature :=
  realize signature (fun _ b M => M b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : Op)) (fun e => nomatch e)

/-- The complete claim, observing only the effect fed to the loss channel. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n),
    ∃ M : Fin (n + 1) → Fin 2 → Op,
      (∀ j, IsBinaryPOVM (fun b => R.readout () b (M j))) ∧
      (∃ N : Fin (n + 1) → Fin 2 → Op,
        ∀ j b, IsLossDual (inverseTransmissivity n hn) (R.readout () b (M j)) (N j b)) ∧
      ∀ N : Fin (n + 1) → Fin 2 → Op,
        (∀ j b, IsLossDual (inverseTransmissivity n hn) (R.readout () b (M j)) (N j b)) →
          ¬ HasParent N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, hM, _⟩ := h 1 (by norm_num)
  have he := (hM 0).2
  change (1 : Op) + 1 = 1 at he
  have hv := congrArg (fun T : Op => (T (lp.single (p := 2) 0 (1 : ℂ))) 0) he
  norm_num at hv

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun b => if b = 0 then 0 else 1),
    (fun b => if b = 0 then 1 else 0), ?_⟩
  change (0 : Op) ≠ 1
  intro h01
  have he := congrArg (fun T : Op => (T (lp.single (p := 2) 0 (1 : ℂ))) 0) h01
  simp at he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Measurement.PureLossIncompatibility.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility "unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ b M => M b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
      name := `D5.S3.Quantum.Measurement.PureLossIncompatibility.claim,
      path := #[] },
    coordinates := #[5],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "arg",
        "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

namespace StinespringVector

/-- Observe the full output vector at fixed transmissivity as the input varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Set.Icc (0 : ℝ) 1)
    (fun _ => H) (fun _ => K)

def actual : Realization signature :=
  realize signature (fun _ τ v => stinespring τ v) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let τ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  refine ⟨τ, 0, e 0, ?_⟩
  change stinespring τ 0 ≠ stinespring τ (e 0)
  rw [map_zero, split_zero]
  intro he
  have hc := congrArg (fun w : K => w 0 0) he
  norm_num [fockPair_apply] at hc

end StinespringVector

namespace SplitZero

/-- The vacuum identity, with only the input fed to the Stinespring map observed. -/
abbrev arena : Arena where
  signature := StinespringVector.signature
  Law R := ∀ τ : Set.Icc (0 : ℝ) 1, R.readout () τ (e 0) = fockPair 0 0

theorem rejected_law : ¬ arena.Law StinespringVector.rejected := by
  intro h
  have he := h ⟨1, by norm_num⟩
  change (0 : K) = fockPair 0 0 at he
  have hc := congrArg (fun w : K => w 0 0) he
  norm_num [fockPair_apply] at hc

def source_registration : Registration arena (type_of% @split_zero) where
  actual := StinespringVector.actual
  bridge := Iff.rfl
  variation := ⟨split_zero, StinespringVector.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    StinespringVector.actual StinespringVector.rejected rejected_law
  dependence := StinespringVector.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_zero) (Realization StinespringVector.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitZero.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitZero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize StinespringVector.signature (fun _ τ v => stinespring τ v)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SplitZero

namespace SplitOne

/-- The one-photon identity, with the same input-vector observation. -/
abbrev arena : Arena where
  signature := StinespringVector.signature
  Law R := ∀ τ : Set.Icc (0 : ℝ) 1, R.readout () τ (e 1) =
    (Real.sqrt τ.1 : ℂ) • fockPair 1 0 +
      (Real.sqrt (1 - τ.1) : ℂ) • fockPair 0 1

theorem rejected_law : ¬ arena.Law StinespringVector.rejected := by
  intro h
  have he := h ⟨1, by norm_num⟩
  change (0 : K) = (Real.sqrt 1 : ℂ) • fockPair 1 0 +
    (Real.sqrt (1 - 1) : ℂ) • fockPair 0 1 at he
  have hc := congrArg (fun w : K => w 0 1) he
  norm_num [lp.coeFn_add, lp.coeFn_smul, fockPair_apply] at hc

def source_registration : Registration arena (type_of% @split_one) where
  actual := StinespringVector.actual
  bridge := Iff.rfl
  variation := ⟨split_one, StinespringVector.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    StinespringVector.actual StinespringVector.rejected rejected_law
  dependence := StinespringVector.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_one) (Realization StinespringVector.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitOne.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitOne.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize StinespringVector.signature (fun _ τ v => stinespring τ v)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SplitOne

namespace SplitZeroCoord

/-- Observe the retained vacuum output at each environment occupation. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Set.Icc (0 : ℝ) 1)
    (fun _ => ℕ) (fun _ => H)

def actual : Realization signature :=
  realize signature (fun _ τ k => (stinespring τ (e 0)) k) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (τ : Set.Icc (0 : ℝ) 1) (k : ℕ),
    R.readout () τ k = if k = 0 then e 0 else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ⟨1, by norm_num⟩ 0
  change (0 : H) = if (0 : ℕ) = 0 then e 0 else 0 at he
  have hc := congrArg (fun v : H => v 0) he
  norm_num [e, lp.single_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let τ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  refine ⟨τ, 0, 1, ?_⟩
  change (stinespring τ (e 0)) 0 ≠ (stinespring τ (e 0)) 1
  rw [split_zero_coord, split_zero_coord]
  intro he
  have hc := congrArg (fun v : H => v 0) he
  norm_num [e, lp.single_apply] at hc

def source_registration : Registration arena (type_of% @split_zero_coord) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨split_zero_coord, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_zero_coord) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitZeroCoord.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitZeroCoord.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ τ k => (stinespring τ (e 0)) k)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SplitZeroCoord

namespace SplitOneCoord

/-- Observe the retained one-photon output at each environment occupation. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Set.Icc (0 : ℝ) 1)
    (fun _ => ℕ) (fun _ => H)

def actual : Realization signature :=
  realize signature (fun _ τ k => (stinespring τ (e 1)) k) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (τ : Set.Icc (0 : ℝ) 1) (k : ℕ),
    R.readout () τ k = if k = 0 then (Real.sqrt τ.1 : ℂ) • e 1
      else if k = 1 then (Real.sqrt (1 - τ.1) : ℂ) • e 0 else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h ⟨1, by norm_num⟩ 0
  change (0 : H) = if (0 : ℕ) = 0 then (Real.sqrt 1 : ℂ) • e 1
    else if (0 : ℕ) = 1 then (Real.sqrt (1 - 1) : ℂ) • e 0 else 0 at he
  have hc := congrArg (fun v : H => v 1) he
  norm_num [e, lp.single_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let τ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  refine ⟨τ, 0, 1, ?_⟩
  change (stinespring τ (e 1)) 0 ≠ (stinespring τ (e 1)) 1
  rw [split_one_coord, split_one_coord]
  intro he
  have hc := congrArg (fun v : H => v 1) he
  norm_num [τ, e, lp.single_apply] at hc

def source_registration : Registration arena (type_of% @split_one_coord) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨split_one_coord, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_one_coord) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitOneCoord.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.SplitOneCoord.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ τ k => (stinespring τ (e 1)) k)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end SplitOneCoord

namespace VacuumTensor

/-- Observe the complete vacuum embedding as its retained input vector varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => H) (fun _ => K)

def actual : Realization signature :=
  realize signature (fun _ _ v => vacuumEmbedding v) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : H, R.readout () () v = tensor v (e 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (e 0)
  change (0 : K) = fockPair 0 0 at he
  have hc := congrArg (fun w : K => w 0 0) he
  norm_num [fockPair_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, e 0, ?_⟩
  change vacuumEmbedding 0 ≠ vacuumEmbedding (e 0)
  rw [map_zero, vacuum_tensor]
  change (0 : K) ≠ fockPair 0 0
  intro he
  have hc := congrArg (fun w : K => w 0 0) he
  norm_num [fockPair_apply] at hc

def source_registration : Registration arena (type_of% @vacuum_tensor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vacuum_tensor, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@vacuum_tensor) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.VacuumTensor.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.VacuumTensor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vacuumEmbedding v)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end VacuumTensor

end
end Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
