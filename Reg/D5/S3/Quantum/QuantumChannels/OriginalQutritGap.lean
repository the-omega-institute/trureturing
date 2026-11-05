import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.OriginalQutritGap
import Reg.Support.DependentFamily

/-! Both commutator occurrences are observed on the complete original unitary family. -/

open _root_.D5.S3.Quantum.QuantumChannels.OriginalQutritGap
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritGap

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix.unitaryGroup (Fin 3) ℂ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ N => delta N) (fun e => nomatch e)

def badLower : Realization signature := realize signature
  (fun i _ N => if i = 0 then 1 else delta N) (fun e => nomatch e)

def badUpper : Realization signature := realize signature
  (fun i _ N => if i = 1 then -1 else delta N) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ N : Matrix.unitaryGroup (Fin 3) ℂ,
    R.readout 0 () N / 8 ≤ 1 - ‖theta N‖ ^ 2 ∧
      1 - ‖theta N‖ ^ 2 ≤ (3/2 : ℝ) * R.readout 1 () N

theorem delta_one : delta 1 = 0 := by
  change ‖vectorize 3 ((1 : Mat) * Pxi - Pxi * (1 : Mat))‖ ^ 2 = 0
  simp

def phase : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨!![1,0,0; 0,-1,0; 0,0,1], by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]⟩

theorem delta_phase_ne : delta phase ≠ 0 := by
  intro h
  have hn : ‖vectorize 3 ((phase : Mat) * Pxi - Pxi * (phase : Mat))‖ = 0 :=
    sq_eq_zero_iff.mp h
  have hm : (phase : Mat) * Pxi - Pxi * (phase : Mat) = 0 := by
    apply (vectorize 3).injective
    simpa only [map_zero] using norm_eq_zero.mp hn
  have he := congrArg (fun X : Mat => X 0 1) hm
  have hentry : (2 : ℂ) * Pxi 0 1 = 0 := by
    simpa [phase, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, two_mul] using he
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hp : Pxi 0 1 ≠ 0 := by
    simp [Pxi, xi, Matrix.vecMulVec_apply, hs]
  exact mul_ne_zero (by norm_num) hp hentry

theorem gap_one : 1 - ‖theta 1‖ ^ 2 = 0 := by
  have h := original_two_sided 1
  rw [delta_one] at h
  norm_num at h
  rw [le_antisymm h.1 h.2]
  norm_num

theorem bad_lower_law : ¬ arena.Law badLower := by
  intro h
  have hh := (h 1).1
  change (1 : ℝ) / 8 ≤ 1 - ‖theta 1‖ ^ 2 at hh
  rw [gap_one] at hh
  norm_num at hh

theorem bad_upper_law : ¬ arena.Law badUpper := by
  intro h
  have hh := (h 1).2
  change 1 - ‖theta 1‖ ^ 2 ≤ (3/2 : ℝ) * (-1) at hh
  rw [gap_one] at hh
  norm_num at hh

def family : Registration arena (type_of% @original_two_sided) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_two_sided, badLower, bad_lower_law⟩
  sensitivity := by
    constructor
    · intro i
      fin_cases i
      · refine ⟨badLower, ?_, rfl, bad_lower_law⟩
        intro j hj
        funext p N
        have hj0 : j ≠ (0 : Fin 2) := hj
        change delta N = if j = 0 then 1 else delta N
        rw [ite_eq_right hj0]
      · refine ⟨badUpper, ?_, rfl, bad_upper_law⟩
        intro j hj
        funext p N
        have hj1 : j ≠ (1 : Fin 2) := hj
        change delta N = if j = 1 then -1 else delta N
        rw [ite_eq_right hj1]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, phase, ?_⟩
    change delta 1 ≠ delta phase
    rw [delta_one]
    exact Ne.symm delta_phase_ne

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_two_sided) (Realization signature) (Type) Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.OriginalQutritGap.original_two_sided.information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => delta N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ↥(Matrix.unitaryGroup (Fin 3) ℂ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.OriginalQutritGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritGap
