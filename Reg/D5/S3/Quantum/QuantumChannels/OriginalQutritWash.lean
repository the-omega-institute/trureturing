import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.OriginalQutritWash
import Reg.Support.DependentFamily

/-! The three norm observations retain the full complex matrix and natural-iterate law. -/

open _root_.D5.S3.Quantum.QuantumChannels.OriginalQutritGap
open _root_.D5.S3.Quantum.QuantumChannels.OriginalQutritWash
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritWash

abbrev signature : Signature where
  Params := Unit
  State _ := Mat
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ X => if i = 0 then ‖vectorize 3 X‖ ^ 2 else ‖vectorize 3 X‖)
  (fun e => nomatch e)

def bad (i : Fin 3) : Realization signature := realize signature
  (fun j p X => if j = i then 10 else actual.readout j p X)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ X : Mat, X.trace = 0 →
      R.readout 0 () (wash X) ≤ (5/12 : ℝ) * ‖vectorize 3 X‖ ^ 2 ∧
      ∀ n : ℕ, R.readout 1 () ((wash : Mat → Mat)^[n] X) ≤
        (2/3 : ℝ)^n * ‖vectorize 3 X‖) ∧
    (∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → ∀ n : ℕ,
      R.readout 2 () ((wash : Mat → Mat)^[n] σ - (1/3 : ℂ) • (1 : Mat)) ≤
        Real.sqrt (2/3) * (2/3 : ℝ)^n)

private theorem bad_law (i : Fin 3) : ¬ arena.Law (bad i) := by
  intro h
  fin_cases i
  · have hh := (h.1 0 (by simp)).1
    change (10 : ℝ) ≤ (5/12 : ℝ) * ‖vectorize 3 (0 : Mat)‖ ^ 2 at hh
    norm_num at hh
  · have hh := (h.1 0 (by simp)).2 0
    change (10 : ℝ) ≤ (2/3 : ℝ)^0 * ‖vectorize 3 (0 : Mat)‖ at hh
    norm_num at hh
  · let u : Fin 3 → ℂ := Pi.single 0 1
    let σ : Mat := Matrix.vecMulVec u (star u)
    have hp : σ.PosSemidef := Matrix.posSemidef_vecMulVec_self_star u
    have ht : σ.trace = 1 := by
      norm_num [σ, u, Matrix.trace, Matrix.vecMulVec_apply, Fin.sum_univ_succ]
    have hh := h.2 σ hp ht 0
    change (10 : ℝ) ≤ Real.sqrt (2/3) * (2/3 : ℝ)^0 at hh
    simp only [pow_zero, mul_one] at hh
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3)]

def family : Registration arena (type_of% @explicit_wash_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨explicit_wash_bound, bad 0, bad_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad i, ?_, rfl, bad_law i⟩
      intro j hj
      funext p X
      change actual.readout j p X = if j = i then 10 else actual.readout j p X
      rw [ite_eq_right hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have hn : ‖vectorize 3 (1 : Mat)‖ ≠ 0 := by
      intro h
      have hv : vectorize 3 (1 : Mat) = 0 := norm_eq_zero.mp h
      have hm : (1 : Mat) = 0 := (vectorize 3).injective (by simpa using hv)
      exact one_ne_zero hm
    fin_cases i
    · change ‖vectorize 3 (0 : Mat)‖ ^ 2 ≠ ‖vectorize 3 (1 : Mat)‖ ^ 2
      simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        (pow_ne_zero 2 hn).symm
    · change ‖vectorize 3 (0 : Mat)‖ ≠ ‖vectorize 3 (1 : Mat)‖
      simpa only [map_zero, norm_zero] using hn.symm
    · change ‖vectorize 3 (0 : Mat)‖ ≠ ‖vectorize 3 (1 : Mat)‖
      simpa only [map_zero, norm_zero] using hn.symm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@explicit_wash_bound) (Realization signature) (Type) Unit := {
  unitName := `D5.S3.Quantum.QuantumChannels.OriginalQutritWash.explicit_wash_bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritWash.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i _ X => if i = 0 then ‖vectorize 3 X‖ ^ 2 else ‖vectorize 3 X‖)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.OriginalQutritWash
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }, {
      path := #["fn", "arg", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }, {
      path := #["arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.QuantumChannels.OriginalQutritWash
