import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.ParryFirstReturn
import Reg.Support.DependentFamily

/-! # Return-clock readout on the actual native section theorem -/

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal BigOperators
open _root_.D5.S3.TotalVariation.ParryBilateralLaw
open _root_.D5.S3.TotalVariation.ParryResetLaw
open _root_.D5.S3.TotalVariation.TwistedResetPaths
open _root_.D5.S3.TotalVariation.ParryFirstReturn
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.TotalVariation.ParryFirstReturn
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State k := RelationPath k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => returnTime r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {k : ℕ}
    (hk : 2 ≤ k)
    (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
    (μ : ProbabilityMeasure (RelationPath k))
    (hsuffix : ∀ (z : Bool × RelationPath k) (t : ℤ),
      let j := ((e z).val t).2.val
      z.2.val (t - (j : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true)
    (hμ : (μ : Measure (RelationPath k)).map relationShift = μ)
    (hcylinder : ∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
        ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
          ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))),
    zeroSection k = {r | ((e (false, r)).val 0).2.val = 0} ∧
    (μ : Measure (RelationPath k)) (zeroSection k) = ENNReal.ofReal (1 / normalizer k) ∧
    0 < (μ : Measure (RelationPath k)) (zeroSection k) ∧
    IsProbabilityMeasure (sectionMeasure (μ : Measure (RelationPath k))) ∧
    MeasurePreserving returnMap (sectionMeasure (μ : Measure (RelationPath k)))
      (sectionMeasure (μ : Measure (RelationPath k))) ∧
    ((μ : Measure (RelationPath k)) = (μ : Measure (RelationPath k)) (zeroSection k) •
      ∑ i : Fin k, ((sectionMeasure (μ : Measure (RelationPath k))).restrict
        {r | i.val < returnTime r}).map (relationShift^[i.val])) ∧
    (∀ r : RelationPath k, 0 < F.readout () k r ∧ returnTime r ≤ k ∧
      returnMap r ∈ zeroSection k ∧
      ∀ n : ℕ, 0 < n → n < returnTime r → relationShift^[n] r ∉ zeroSection k)

private def zeroPath : RelationPath 2 :=
  ⟨fun _ => false, fun _ => ⟨0, rfl⟩⟩

private def alternatingPath : RelationPath 2 :=
  ⟨fun t => decide (t % 2 = 0), fun t => by
    by_cases ht : t % 2 = 0
    · refine ⟨1, ?_⟩
      have he : (t + 1) % 2 ≠ 0 := by omega
      simp [he]
    · exact ⟨0, by simpa [ht]⟩⟩

private theorem zeroTime : returnTime zeroPath = 1 := by
  unfold returnTime
  change Nat.find _ + 1 = 0 + 1
  apply congrArg (fun n : ℕ => n + 1)
  exact (Nat.find_eq_iff _).mpr ⟨rfl, by omega⟩

private theorem alternatingTime : returnTime alternatingPath = 2 := by
  unfold returnTime
  change Nat.find _ + 1 = 1 + 1
  apply congrArg (fun n : ℕ => n + 1)
  exact (Nat.find_eq_iff _).mpr ⟨by decide, by
    intro i hi
    have he : i = 0 := by omega
    subst i
    decide⟩

private theorem positive : arena.Law actual := @actual_first_return_system

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, μ, ν, hsign, hsuffix, hread, hcode, hμ, hν, hpush, hcyl, hsource⟩ :=
    bilateral_parry_law 2 (by decide)
  have hh := (h (k := 2) (by decide) e μ hsuffix hμ hsource).2.2.2.2.2.2 zeroPath
  exact Nat.not_lt_zero _ hh.1

def evidence : Registration arena (type_of% (@actual_first_return_system)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, zeroPath, alternatingPath, ?_⟩
    change returnTime zeroPath ≠ returnTime alternatingPath
    rw [zeroTime, alternatingTime]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_first_return_system) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParryFirstReturn.actual_first_return_system
  realizationName := `Reg.D5.S3.TotalVariation.ParryFirstReturn.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => returnTime r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParryFirstReturn
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.TotalVariation.ParryFirstReturn
