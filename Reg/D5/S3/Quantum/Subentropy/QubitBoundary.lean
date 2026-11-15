import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Subentropy.QubitBoundary
import D5.S3.Quantum.Subentropy.UniformValues
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Source-bound observations of the qubit subentropy boundary estimate. -/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.QubitBoundary

namespace Reg.D5.S3.Quantum.Subentropy.QubitBoundary

abbrev M := Matrix (Fin 2) (Fin 2) ℂ

inductive ReadoutRole
  | zeroValue
  | deficitLower
  | deficitUpper
  deriving DecidableEq

instance : Fintype ReadoutRole where
  elems := {.zeroValue, .deficitLower, .deficitUpper}
  complete i := by cases i <;> simp

@[reducible] def signature : Signature where
  Params := Unit
  State _ := M
  Role := ReadoutRole
  finiteRole := inferInstance
  nonemptyRole := ⟨.zeroValue⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => matrixSubentropy A) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law obs := ∀ (A : M) (_hA : A.PosSemidef) (_htr : A.trace = 1),
    let δ := A.det.re
    0 ≤ δ ∧ δ ≤ 1 / 4 ∧
      (δ = 0 → obs.readout .zeroValue () A = 0) ∧
      (0 < δ → 0 ≤ δ - obs.readout .deficitLower () A ∧
        δ - obs.readout .deficitUpper () A ≤ δ ^ 2 * Real.log (1 / δ) / (1 - δ))

private def pure : M := diagonal ![1, 0]
private def mixed : M := diagonal (fun _ => ((1 / 2 : ℝ) : ℂ))

private theorem pure_psd : pure.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [pure]

private theorem pure_trace : pure.trace = 1 := by
  norm_num [pure, Matrix.trace, Fin.sum_univ_two]

private theorem pure_det : pure.det.re = 0 := by
  norm_num [pure, Matrix.det_fin_two]

private theorem mixed_psd : mixed.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ)
  exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem mixed_trace : mixed.trace = 1 := by
  norm_num [mixed, Matrix.trace, Fin.sum_univ_two]

private theorem mixed_det : mixed.det.re = 1 / 4 := by
  norm_num [mixed, Matrix.det_fin_two]

def changed (i : ReadoutRole) : Realization signature := realize signature
  (fun j p A => if j = i then
    if i = .deficitUpper then
      -1 - A.det.re ^ 2 * Real.log (1 / A.det.re) / (1 - A.det.re) else 1
    else actual.readout j p A) (fun e => nomatch e)

private theorem changed_negative (i : ReadoutRole) : ¬ arena.Law (changed i) := by
  intro h
  cases i
  · have hp := (h pure pure_psd pure_trace).2.2.1 pure_det
    norm_num [changed, realize] at hp
  · have hp := ((h mixed mixed_psd mixed_trace).2.2.2
      (by rw [mixed_det]; norm_num)).1
    norm_num [changed, realize, mixed_det] at hp
  · have hp := ((h mixed mixed_psd mixed_trace).2.2.2
      (by rw [mixed_det]; norm_num)).2
    norm_num [changed, realize] at hp
    rw [mixed_det] at hp
    linarith

def evidence : Registration arena (type_of% @qubit_subentropy_near_pure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨qubit_subentropy_near_pure, changed .zeroValue, changed_negative .zeroValue⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, ?_, changed_negative i⟩
      · intro j hj
        funext p A
        simp only [changed, realize, ite_eq_right hj]
      · rfl
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), pure, mixed, ?_⟩
    change matrixSubentropy pure ≠ matrixSubentropy mixed
    rw [(qubit_subentropy_near_pure pure pure_psd pure_trace).2.2.1 pure_det]
    have hv := _root_.D5.S3.Quantum.Subentropy.UniformValues.subentropy_uniformTwo
      (ι := Fin 2) (by decide)
    change matrixSubentropy mixed = _ at hv
    rw [hv]
    linarith [Real.log_two_gt_d9]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@qubit_subentropy_near_pure) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.QubitBoundary.qubit_subentropy_near_pure.audit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.QubitBoundary.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => matrixSubentropy A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.QubitBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "arg", "arg",
        "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "arg", "arg",
        "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Quantum.Subentropy.QubitBoundary
