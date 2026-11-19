import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.ParryKSMaximizer
import Reg.Support.DependentFamily

/-! # Entropy readout for the uniqueness of the bilateral Parry maximizer -/

open MeasureTheory
open scoped ENNReal BigOperators
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.TotalVariation.ParryBilateralLaw
open _root_.D5.S3.TotalVariation.ParryResetLaw
open _root_.D5.S3.TotalVariation.ParryFirstReturn
open _root_.D5.S3.TotalVariation.ParryKSMaximizer
open _root_.D5.S3.Entropy.KolmogorovSinai
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.TotalVariation.ParryKSMaximizer

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
  realize signature (fun _ _ k => -Real.log (parryParameter k) - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {k : ℕ} (_hk : 2 ≤ k)
      (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
      (μ : ProbabilityMeasure (RelationPath k))
      (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
        let j := ((e z).val t).2.val
        z.2.val (t - (j : ℤ) - 1) = false ∧
          ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
      (hcyl : ∀ (t : ℤ) (n : ℕ) (w : Fin (n + 1) → Fin k),
        (μ : Measure (RelationPath k))
          {r | (fun i : Fin (n + 1) => ((e (false, r)).val (t + i.val)).2) = w} =
          ENNReal.ofReal (suffixLaw k (w 0)) *
            ∏ i : Fin n, ENNReal.ofReal (suffixKernel k (w i.castSucc) (w i.succ)))
      (ρ : ProbabilityMeasure (RelationPath k))
      (Tρ : MeasurePreserving (@relationShift k) ρ ρ),
      ksEntropy Tρ ≤ (F.readout () () k : EReal) ∧
        (ksEntropy Tρ = ((-Real.log (parryParameter k) : ℝ) : EReal) ↔ ρ = μ)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, μ, ν, _, hsuffix, _, _, hμ, _, _, _, hcyl⟩ := bilateral_parry_law 2 (by decide)
  let Tμ : MeasurePreserving (@relationShift 2) μ μ := ⟨measurable_relationShift, hμ⟩
  have hbound := h (by decide : 2 ≤ (2 : ℕ)) e μ hsuffix hcyl μ Tμ
  have hbad := hbound.1
  rw [hbound.2.mpr rfl] at hbad
  have hreal := EReal.coe_le_coe_iff.mp hbad
  change -Real.log (parryParameter 2) ≤ -Real.log (parryParameter 2) - 1 at hreal
  linarith

def evidence : Registration arena (type_of% (@bilateral_parry_maximizer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bilateral_parry_maximizer, rejected, negative⟩
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
    (@bilateral_parry_maximizer) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParryKSMaximizer.bilateral_parry_maximizer
  realizationName := `Reg.D5.S3.TotalVariation.ParryKSMaximizer.evidence
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
    owner := `D5.S3.TotalVariation.ParryKSMaximizer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.TotalVariation.ParryKSMaximizer
