import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the CAR matrix identity and the exact witness gain. -/

namespace Reg.D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence

open _root_.D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CAR

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2) (fun _ => Fin 2)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

private def actual : Realization signature :=
  realize signature (fun _ i j => if i = j then 1 else 0) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ i j : Fin 2,
    jump i * jump j + jump j * jump i = 0 ∧
      jump i * (jump j)ᴴ + (jump j)ᴴ * jump i = R.readout () i j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual : jump 0 * (jump 0)ᴴ + (jump 0)ᴴ * jump 0 = 1 := by
    simpa using (car 0 0).2
  have hzero : jump 0 * (jump 0)ᴴ + (jump 0)ᴴ * jump 0 = 0 := (h 0 0).2
  exact one_ne_zero (hactual.symm.trans hzero)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (1 : Matrix (Fin 4) (Fin 4) ℂ) ≠ 0
  exact one_ne_zero

def family : Registration arena (type_of% @car) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨car, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@car) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence.car.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence.CAR.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i j => if i = j then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CAR

namespace WitnessGain

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4 → ℂ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ x => gain x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R :=
    0 < modeBeta 0 ∧ modeBeta 0 < modeBeta 1 ∧ modeBeta 1 = beta ∧
    (c 0 = 8 / 17 ∧ c 1 = 32 / 257 ∧ d 0 = 15 / 34 ∧ d 1 = 480 / 4369) ∧
    normalized witness ∧
    q 0 witness = 82 / 3782 ∧ q 1 witness = 101 / 3782 ∧
    z 0 witness = ((550 / 3782 : ℝ) : ℂ) ∧
    z 1 witness = ((591 / 3782 : ℝ) : ℂ) ∧
    R.readout () () witness = 15416747 / 31246048178 ∧
    (49 / 100000 : ℝ) < gain witness ∧
    IsGreatest {g | ∃ x, normalized x ∧ modeGain 0 x = g} (1 / 2176) ∧
    IsGreatest {g | ∃ x, normalized x ∧ modeGain 1 x = g} (32 / 74273)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, hgain, _, _, _⟩ := h
  change (0 : ℝ) = 15416747 / 31246048178 at hgain
  norm_num at hgain

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, witness, ?_⟩
  change gain 0 ≠ gain witness
  have hzero : gain 0 = 0 := by simp [gain, modeGain, z, q, moment]
  obtain ⟨_, _, _, _, _, _, _, _, _, hgain, _, _, _⟩ := physical_certificate
  rw [hzero, hgain]
  norm_num

def family : Registration arena (type_of% physical_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_certificate, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      physical_certificate (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence.physical_certificate.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence.WitnessGain.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => gain x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end WitnessGain
end
end Reg.D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
