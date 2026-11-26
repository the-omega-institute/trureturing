import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.ParryKSEntropy
import Reg.Support.DependentFamily

/-! # Entropy bound readout on the bilateral Parry shift -/

open MeasureTheory
open scoped ENNReal BigOperators
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.TotalVariation.ParryBilateralLaw
open _root_.D5.S3.TotalVariation.ParryResetLaw
open _root_.D5.S3.TotalVariation.ParryKSEntropy
open _root_.D5.S3.Entropy.KolmogorovSinai
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.TotalVariation.ParryKSEntropy

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => -Real.log (parryParameter k)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => -Real.log (parryParameter k) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (k : ℕ) (_hk : 2 ≤ k),
    ∃ (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
      (μ : ProbabilityMeasure (RelationPath k))
      (Tμ : MeasurePreserving (@relationShift k) μ μ),
      (∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
        (μ : Measure (RelationPath k))
          {r | (fun i : Fin (n + 1) => ((e (false, r)).val (t + i.val)).2) = w} =
          ENNReal.ofReal (suffixLaw k (w 0)) *
            ∏ i : Fin n, ENNReal.ofReal (suffixKernel k (w i.castSucc) (w i.succ))) ∧
      ksEntropy Tμ = (F.readout () () k : EReal) ∧
      (∀ (ρ : ProbabilityMeasure (RelationPath k))
        (Tρ : MeasurePreserving (@relationShift k) ρ ρ),
        ksEntropy Tρ ≤ ((-Real.log (parryParameter k) : ℝ) : EReal))

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, μ, T, hcyl, hEq, hLe⟩ := h 2 (by decide)
  have hbad := hLe μ T
  rw [hEq] at hbad
  have hreal := EReal.coe_le_coe_iff.mp hbad
  change -Real.log (parryParameter 2) + 1 ≤ -Real.log (parryParameter 2) at hreal
  linarith

def evidence : Registration arena (type_of% (@bilateral_parry_entropy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bilateral_parry_entropy, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    have h2 : 2 ≤ (2 : ℕ) := le_rfl
    have h3 : 2 ≤ (3 : ℕ) := by decide
    have hroot := dbonacciPerronRoot_strictMonoOn h2 h3 (by decide : (2 : ℕ) < 3)
    change -Real.log (parryParameter 2) ≠ -Real.log (parryParameter 3)
    have hp : parryParameter 3 < parryParameter 2 := by
      simpa only [parryParameter, ite_eq_left h2, ite_eq_left h3] using
        (inv_lt_inv₀ (zero_lt_one.trans (dbonacciPerronRoot_spec 3 h3).1)
          (zero_lt_one.trans (dbonacciPerronRoot_spec 2 h2).1)).2 hroot
    have hpos : 0 < parryParameter 3 :=
      lt_trans (by norm_num) (parry_stationary_law 3 h3).1.1
    exact ne_of_lt (neg_lt_neg (Real.log_lt_log hpos hp))

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bilateral_parry_entropy) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParryKSEntropy.bilateral_parry_entropy
  realizationName := `Reg.D5.S3.TotalVariation.ParryKSEntropy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => -Real.log (parryParameter k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParryKSEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.TotalVariation.ParryKSEntropy
