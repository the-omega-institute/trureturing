import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint

noncomputable section
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.Defs
open _root_.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint

private theorem numPosEig_zero :
    numPosEig (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  classical
  have h := Matrix.isHermitian_zero (n := Fin 3) (α := ℝ)
  have he := h.eigenvalues_eq_zero_iff.mpr rfl
  simp only [numPosEig, dite_eq_left h]
  simp [he]

namespace Plane
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℝ)
    (fun _ => Fin 3 → ℝ) (fun _ => Matrix (Fin 3) (Fin 3) ℝ)

def actual : Realization signature :=
  realize signature (fun _ p d => weightedToeplitz d p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Fin 3 → ℝ), (∀ i, d i ≠ 0) → ∀ a b : ℝ,
    0 < 1 + b - 2 * a ^ 2 → 2 ≤ numPosEig (R.readout () (a, b) d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) (by simp) 0 0 (by norm_num)
  change 2 ≤ numPosEig (0 : Matrix (Fin 3) (Fin 3) ℝ) at hh
  rw [numPosEig_zero] at hh
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 0), 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [actual, realize, weightedToeplitz] at he

def family : Registration arena (type_of% @two_le_numPosEig_weightedToeplitz) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_le_numPosEig_weightedToeplitz, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_le_numPosEig_weightedToeplitz) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint.Plane.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint.Plane.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => weightedToeplitz d p.1 p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Plane

namespace Family
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ
    (fun _ => ℝ) (fun _ => Matrix (Fin 3) (Fin 3) ℝ)

def actual : Realization signature :=
  realize signature (fun _ γ z =>
    stolarskyMatrix γ ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ γ : ℝ, 0 ≤ γ → γ < 2 →
    ∃ z : ℝ, 0 < z ∧ 2 ≤ numPosEig (R.readout () γ z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz, hn⟩ := h 0 (by norm_num) (by norm_num)
  change 2 ≤ numPosEig (0 : Matrix (Fin 3) (Fin 3) ℝ) at hn
  rw [numPosEig_zero] at hn
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 0
  change stolarsky 0 (Real.exp (-2 * 0)) (Real.exp (-2 * 0)) =
    stolarsky 0 (Real.exp (-2 * 1)) (Real.exp (-2 * 1)) at he
  simp only [stolarsky, if_pos rfl] at he
  have hx := Real.exp_injective he
  norm_num at hx

def family : Registration arena (type_of% @exists_threePoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_threePoint, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_threePoint) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint.Family.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint.Family.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ z =>
    stolarskyMatrix γ ![Real.exp (-2 * z), 1, Real.exp (2 * z)]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Family

#print axioms Plane.audit
#print axioms Family.audit

end Reg.D5.S3.Quantum.Matrix.StolarskyMean.ThreePoint
