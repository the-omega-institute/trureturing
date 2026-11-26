import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages
import Reg.Support.SingleDependentReadout

/-! Exact source registration for the identification of the DT mass. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open HypercubeWalsh LeanInformationAudit

abbrev Parameters := Σ d : ℕ, Σ _ : Kernel (Cube d), ℕ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun p => Cube p.1) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p x => discreteMass p.2.1 p.2.2 x) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (K : Kernel (Cube d)) (n : ℕ) (x : Cube d),
    R.readout () ⟨d, K, n⟩ x = ∑ y, ‖discreteComplexState K n y x‖ ^ 2

private def originKernel (d : ℕ) : Kernel (Cube d) where
  p y := if y = origin then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  total := by simp

private theorem mass_zero {d : ℕ} (K : Kernel (Cube d)) (x : Cube d) :
    discreteMass K 0 x = if x = origin then 1 else 0 := by
  rw [discreteMass_eq_complex]
  change (∑ y, ‖(if x = origin then (K.coin y : ℂ) else 0)‖ ^ 2) = _
  by_cases hx : x = origin
  · simp [hx, Kernel.coin, Real.sq_sqrt, K.nonneg, K.total]
  · simp [hx]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := @h 1 (originKernel 1) 0 origin
  change 0 = ∑ y, ‖discreteComplexState (originKernel 1) 0 y origin‖ ^ 2 at hzero
  rw [← discreteMass_eq_complex, mass_zero] at hzero
  norm_num at hzero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let one : Cube 1 := fun _ => true
  have hne : one ≠ origin := by
    intro h
    have hbit := congrFun h (0 : Fin 1)
    simp [one, origin] at hbit
  refine ⟨⟨1, originKernel 1, 0⟩, origin, one, ?_⟩
  change discreteMass (originKernel 1) 0 origin ≠ discreteMass (originKernel 1) 0 one
  simp [mass_zero, hne]

def evidence : Registration arena (type_of% @discreteMass_eq_complex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@discreteMass_eq_complex, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@discreteMass_eq_complex) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.PositionAverages
