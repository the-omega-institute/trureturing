import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
import Reg.Support.DependentFamily

/-! Source-bound audit of the full-ONB Nagaoka–Hayashi to Holevo bound. -/

namespace Reg.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio

open _root_.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Fix the dimension and basis, and observe NHCRB along the parameter family. -/
abbrev signature : Signature where
  Params := Σ d : ℕ, Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ
  State p := Fin (p.1 ^ 2 - 1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p θ => nhcrb p.1 p.2 θ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p θ => ((p.1 : ℝ) + 1) * hcrb p.1 p.2 θ + 1)
    (fun e => nomatch e)

/-- Preserve every dimension, orthonormality, and positivity hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 2 ≤ d →
    ∀ b : Fin (d ^ 2 - 1) → Matrix (Fin d) (Fin d) ℂ, IsTracelessONB d b →
    ∀ θ : Fin (d ^ 2 - 1) → ℝ, (model d b θ).PosSemidef →
      R.readout () ⟨d, b⟩ θ ≤ ((d : ℝ) + 1) * hcrb d b θ

private def q : ℝ := Real.sqrt (1 / 2)

private lemma q_sq : (q : ℂ) ^ 2 = 1 / 2 := by
  have h : q ^ 2 = 1 / 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← Complex.ofReal_pow, h]
  norm_num

/-- Normalized Pauli matrices give an explicit admissible full qubit basis. -/
private def qubitBasis : Fin (2 ^ 2 - 1) → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, (q : ℂ); (q : ℂ), 0],
    !![0, -(q : ℂ) * Complex.I; (q : ℂ) * Complex.I, 0],
    !![(q : ℂ), 0; 0, -(q : ℂ)]]

private lemma qubitBasis_onb : IsTracelessONB 2 qubitBasis := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (qubitBasis j).conjTranspose = qubitBasis j
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k <;>
      simp [qubitBasis, Matrix.conjTranspose_apply]
  · intro j
    fin_cases j <;> simp [qubitBasis, Matrix.trace, Fin.sum_univ_two]
  · intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [qubitBasis, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [q_sq]

private lemma qubit_zero_positive : (model 2 qubitBasis 0).PosSemidef := by
  have h := (Matrix.PosSemidef.one (R := ℂ) (n := Fin 2)).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have heq : model 2 qubitBasis 0 = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    norm_num [model, Matrix.smul_apply, Complex.real_smul]
  rw [heq]
  exact h

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by norm_num) qubitBasis qubitBasis_onb 0 qubit_zero_positive
  change (2 + 1) * hcrb 2 qubitBasis 0 + 1 ≤ (2 + 1) * hcrb 2 qubitBasis 0 at hbad
  linarith

private lemma zero_basis_nhcrb (θ : Fin (2 ^ 2 - 1) → ℝ) :
    nhcrb 2 (fun _ => 0) θ = - ∑ j, θ j ^ 2 := by
  have hempty : {c : ℝ | ∃ x l, IsLUB 2 (fun _ => 0) θ x ∧ IsAdmissible x l ∧
      c = (∑ j, (model 2 (fun _ => 0) θ * l j j).trace).re} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro c ⟨x, l, hx, _, _⟩
    have hh := hx.2.2 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
    norm_num at hh
  rw [nhcrb, hempty]
  simp

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, fun _ => 0⟩, 0, (fun _ => 1), ?_⟩
  change nhcrb 2 (fun _ => 0) 0 ≠ nhcrb 2 (fun _ => 0) (fun _ => 1)
  rw [zero_basis_nhcrb, zero_basis_nhcrb]
  norm_num

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p θ => nhcrb p.1 p.2 θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
    definition := some {
      owner := `D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
      name := `D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.claim
      path := #[] }
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.result
#print _root_.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.OnbTomographyHolevoRatio
