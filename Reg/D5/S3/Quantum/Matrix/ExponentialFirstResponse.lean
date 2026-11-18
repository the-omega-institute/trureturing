import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Matrix.ExponentialFirstResponse

/-! Source families for the complex matrix exponential and its derivative operator. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.ExponentialFirstResponse
open LeanInformationAudit Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse

universe u

private abbrev Mat (n : Type*) := Matrix n n ℂ
private abbrev Shape := Σ n : Type u, Σ _ : Fintype n, DecidableEq n

private theorem derivative_zero (n : Type*) [Fintype n] [DecidableEq n] (X : Mat n) :
    derivative 0 X = X := by
  rw [derivative_apply]
  simp

namespace Exponential

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Shape.{u}
    (fun p => Mat p.1) (fun p => Mat p.1)

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => by
    let _ := p.2.1
    let _ := p.2.2
    exact exp X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A : Mat n),
    HasFDerivAt (R.readout () ⟨n, inferInstance, inferInstance⟩) (derivative A) A

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  have hd : HasFDerivAt (fun _ : Mat n => (0 : Mat n))
      (derivative 0) (0 : Mat n) := h (n := n) 0
  have hz : derivative (0 : Mat n) = 0 := hd.unique (hasFDerivAt_const _ _)
  have he := DFunLike.congr_fun hz (1 : Mat n)
  rw [derivative_zero] at he
  exact one_ne_zero he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let n := ULift.{u} Unit
  refine ⟨⟨n, inferInstance, inferInstance⟩, 0, algebraMap ℝ (Mat n) (Real.log 2), ?_⟩
  change exp (0 : Mat n) ≠ exp (algebraMap ℝ (Mat n) (Real.log 2))
  rw [exp_zero, ← algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ, Real.exp_log (by norm_num)]
  intro h
  rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one] at h
  exact zero_ne_one (add_right_cancel (by simpa only [zero_add] using h :
    (0 : Mat n) + 1 = 1 + 1))

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.ExponentialFirstResponse.hasFDerivAt_exp.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.ExponentialFirstResponse.hasFDerivAt_exp.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Matrix.ExponentialFirstResponse.hasFDerivAt_exp.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse.Exponential.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse.Exponential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.ExponentialFirstResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Exponential

namespace Evaluation

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, Mat n)
    (fun p => Mat p.1) (fun p => Mat p.1)

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => by
    let _ := p.2.1
    let _ := p.2.2.1
    exact derivative p.2.2.2 X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (A J : Mat n),
    R.readout () ⟨n, inferInstance, inferInstance, A⟩ J =
      ∫ t : ℝ in 0..1, exp ((1 - t) • A) * J * exp (t • A)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  have he := h (n := n) (0 : Mat n) 1
  have h' : (0 : Mat n) = 1 := by simpa [rejected, realize] using he
  exact zero_ne_one h'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let n := ULift.{u} Unit
  refine ⟨⟨n, inferInstance, inferInstance, 0⟩, 0, 1, ?_⟩
  change derivative (0 : Mat n) 0 ≠ derivative (0 : Mat n) 1
  rw [derivative_zero, derivative_zero]
  exact zero_ne_one

def family : Registration arena.{u} (type_of% (@derivative_apply.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@derivative_apply.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@derivative_apply.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse.Evaluation.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse.Evaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.ExponentialFirstResponse
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Evaluation

end Reg.D5.S3.Quantum.Matrix.ExponentialFirstResponse
