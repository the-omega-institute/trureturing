import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Walks.HadamardSojournRigidity

/-! The time-eight conditional law as a readout on the coin. -/

namespace Reg.D5.S3.Quantum.Walks.HadamardSojournRigidity

open _root_.D5.S3.Quantum.Walks.HadamardSojournRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix BigOperators

set_option autoImplicit false

noncomputable section

private abbrev Coin := Matrix (Fin 2) (Fin 2) ℂ
private abbrev Vector := Fin 2 → ℂ

abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Vector (fun _ => Coin) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ φ U => exactUniform U φ 2) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (U : Coin) (φ : Vector), Uᴴ * U = 1 → (∑ i, Complex.normSq (φ i)) = 1 →
    (R.readout () φ U ↔ ∀ i j, ‖U i j‖ = 1 / Real.sqrt 2)

private def balancedCoin : Coin :=
  let a := (↑(1 / Real.sqrt 2 : ℝ) : ℂ)
  !![a, a; a, -a]

private lemma balancedCoin_unitary : balancedCoinᴴ * balancedCoin = 1 := by
  have hs : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  let a := (↑(1 / Real.sqrt 2 : ℝ) : ℂ)
  have hc : a ^ 2 = 1 / 2 := by
    change Complex.ofReal (1 / Real.sqrt 2) ^ 2 = _
    rw [← Complex.ofReal_pow, hs, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hc' : a * a = 1 / 2 := by simpa only [pow_two] using hc
  have hreal : (starRingEnd ℂ) a = a := Complex.conj_ofReal _
  change (!![a, a; a, -a] : Coin)ᴴ * !![a, a; a, -a] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hreal, hc'] <;> norm_num

private lemma balancedCoin_balanced (i j : Fin 2) : ‖balancedCoin i j‖ = 1 / Real.sqrt 2 := by
  have hr : 0 ≤ 1 / Real.sqrt 2 := by positivity
  have hnorm : ‖(↑(1 / Real.sqrt 2 : ℝ) : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  fin_cases i <;> fin_cases j
  · exact hnorm
  · exact hnorm
  · exact hnorm
  · change ‖-(↑(1 / Real.sqrt 2 : ℝ) : ℂ)‖ = _
    exact (norm_neg _).trans hnorm

private def initial : Vector := ![1, 0]

private lemma initial_unit : (∑ i, Complex.normSq (initial i)) = 1 := by simp [initial]

private lemma identity_unbalanced : ¬ ∀ i j : Fin 2, ‖(1 : Coin) i j‖ = 1 / Real.sqrt 2 := by
  intro h
  have hpos : 0 < 1 / Real.sqrt 2 := by positivity
  have hzero : 0 = 1 / Real.sqrt 2 := by simpa using h 0 1
  exact hpos.ne' hzero.symm

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact (h balancedCoin initial balancedCoin_unitary initial_unit).mpr balancedCoin_balanced

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨initial, balancedCoin, (1 : Coin), ?_⟩
  intro eq
  have h := (exactUniform_eight_iff balancedCoin initial balancedCoin_unitary initial_unit).mpr
    balancedCoin_balanced
  have hid : exactUniform (1 : Coin) initial 2 := Eq.mp eq h
  exact identity_unbalanced
    ((exactUniform_eight_iff (1 : Coin) initial (by simp) initial_unit).mp hid)

def family : Registration arena (type_of% @exactUniform_eight_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exactUniform_eight_iff, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@exactUniform_eight_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Walks.HadamardSojournRigidity.exactUniform_eight_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Walks.HadamardSojournRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ φ U => exactUniform U φ 2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Walks.HadamardSojournRigidity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Walks.HadamardSojournRigidity
