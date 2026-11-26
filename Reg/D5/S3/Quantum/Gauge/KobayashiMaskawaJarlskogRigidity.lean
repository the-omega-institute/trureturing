import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity

/-! The absolute invariant is a real-valued observation on complex mixing matrices. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity

abbrev MixingMatrix := Matrix (Fin 3) (Fin 3) ℂ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => MixingMatrix) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ V => |jarlskog V|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / (6 * Real.sqrt 3) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : MixingMatrix}, V ∈ Matrix.unitaryGroup (Fin 3) ℂ →
    R.readout () () V ≤ 1 / (6 * Real.sqrt 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h (V := 1) (one_mem _)
  change 1 / (6 * Real.sqrt 3) + 1 ≤ 1 / (6 * Real.sqrt 3) at h1
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (1 : MixingMatrix), fourier3, ?_⟩
  change |jarlskog (1 : MixingMatrix)| ≠ |jarlskog fourier3|
  have hzero : jarlskog (1 : MixingMatrix) = 0 := by
    norm_num [jarlskog, quartet, Matrix.one_apply]
  rw [hzero, abs_zero, fourier3_attains_max_jarlskog.2]
  exact ne_of_lt (by positivity)

def source : Registration arena (type_of% @jarlskog_abs_le_sharp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@jarlskog_abs_le_sharp, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@jarlskog_abs_le_sharp) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity.unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ V => |jarlskog V|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Gauge.KobayashiMaskawaJarlskogRigidity
