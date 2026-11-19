import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.ParrySectionMarginals
import Reg.Support.DependentFamily

/-! The first raw bit as an observation on the native relation path. -/

open MeasureTheory ProbabilityTheory
open _root_.D5.S3.TotalVariation.ParryBilateralLaw
open _root_.D5.S3.TotalVariation.ParryFirstReturn
open _root_.D5.S3.TotalVariation.ParryResetLaw
open _root_.D5.S3.TotalVariation.ParrySectionMarginals
open _root_.D5.S3.TotalVariation.TwistedResetPaths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal

namespace Reg.D5.S3.TotalVariation.ParrySectionMarginals

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State k := RelationPath k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r.val 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {k : ℕ} (_hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (_hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (_hμ : (μ : Measure (RelationPath k)).map relationShift = μ)
    (_hcylinder : ∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
        ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))),
    sectionMeasure (μ : Measure (RelationPath k)) {r | F.readout () k r = false} =
        ENNReal.ofReal (parryParameter k) ∧
      sectionMeasure (μ : Measure (RelationPath k)) {r | r.val 1 = false} =
        ENNReal.ofReal (2 * parryParameter k ^ 2) ∧
      (sectionMeasure (μ : Measure (RelationPath k))).map relationShift ≠
        sectionMeasure (μ : Measure (RelationPath k))

private def zeroPath : RelationPath 2 :=
  ⟨fun _ => false, fun _ => ⟨0, rfl⟩⟩

private def alternatingPath : RelationPath 2 :=
  ⟨fun t => decide (t % 2 = 0), fun t => by
    by_cases ht : t % 2 = 0
    · refine ⟨1, ?_⟩
      have he : (t + 1) % 2 ≠ 0 := by omega
      simp [he]
    · exact ⟨0, by simp [ht]⟩⟩

private theorem positive : arena.Law actual := @section_zero_marginals

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, μ, ν, hsign, hsuffix, hread, hcode, hμ, hν, hpush, hcyl, hsource⟩ :=
    bilateral_parry_law 2 (by decide)
  have bad := (h (k := 2) (by decide) e μ hsuffix hμ hsource).1
  have hp : 0 < parryParameter 2 := by
    linarith [(parry_stationary_law 2 (by decide)).1.1]
  have hzero : (0 : ℝ≥0∞) = ENNReal.ofReal (parryParameter 2) := by
    simpa [rejected, realize] using bad
  exact (ENNReal.ofReal_pos.mpr hp).ne' hzero.symm

def evidence : Registration arena (type_of% (@section_zero_marginals)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    refine ⟨2, zeroPath, alternatingPath, ?_⟩
    change zeroPath.val 0 ≠ alternatingPath.val 0
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@section_zero_marginals) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParrySectionMarginals.section_zero_marginals
  realizationName := `Reg.D5.S3.TotalVariation.ParrySectionMarginals.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => r.val 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParrySectionMarginals
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.TotalVariation.ParrySectionMarginals
