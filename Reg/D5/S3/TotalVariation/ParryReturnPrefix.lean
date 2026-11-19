import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.TotalVariation.ParryReturnPrefix

/-! The complete-return prefix and its unfinished true run form the observation. -/

open MeasureTheory
open _root_.D5.S3.TotalVariation.ParryBilateralLaw
open _root_.D5.S3.TotalVariation.ParryFirstReturn
open _root_.D5.S3.TotalVariation.ParryResetLaw
open _root_.D5.S3.TotalVariation.ParryReturnPrefix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal

namespace Reg.D5.S3.TotalVariation.ParryReturnPrefix

noncomputable section

abbrev signature : Signature where
  Params := Σ k : ℕ, Σ _ : List (Fin k), ℕ
  State p := RelationPath p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => matchesReturnPrefix r p.2.1 p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {k : ℕ} (μ : Measure (RelationPath k)) (weights : Fin k → ℝ≥0∞)
    (_hcyl : ∀ ns : List (Fin k),
      μ {r | matchesReturnTimes r ns = true} = (ns.map weights).prod)
    (ns : List (Fin k)) (j : ℕ),
    μ {r | F.readout () ⟨k, ns, j⟩ r = true} =
      (ns.map weights).prod * ∑ i : Fin (k - j), weights (returnTailIndex j i)

private theorem positive : arena.Law actual := @iid_return_prefix

private theorem negative : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, μ, ν, hsign, hsuffix, hread, hcode, hμ, hν, hpush, hcyl, hsource⟩ :=
    bilateral_parry_law 2 (by decide)
  let weight (i : Fin 2) := ENNReal.ofReal (parryParameter 2 ^ (i.val + 1))
  have hw (ns : List (Fin 2)) :
      sectionMeasure (μ : Measure (RelationPath 2)) {r | matchesReturnTimes r ns = true} =
        (ns.map weight).prod := by
    rw [return_time_cylinder_probability (by decide) e μ hsuffix hμ hsource]
    induction ns with
    | nil => simp
    | cons n ns ih =>
      simpa [List.map_cons, List.prod_cons, ENNReal.ofReal_mul
        (by have := (parry_stationary_law 2 (by decide)).1.1; positivity : 0 ≤ parryParameter 2 ^ (n.val + 1)),
        weight] using congrArg (ENNReal.ofReal (parryParameter 2 ^ (n.val + 1)) * ·) ih
  have bad := h (sectionMeasure (μ : Measure (RelationPath 2))) weight hw [] 0
  have hp : 0 < parryParameter 2 := by
    linarith [(parry_stationary_law 2 (by decide)).1.1]
  have hzero : (0 : ℝ≥0∞) = ∑ i : Fin 2, weight i := by
    simpa [rejected, realize, returnTailIndex] using bad
  have hpos : 0 < weight 0 := ENNReal.ofReal_pos.mpr (pow_pos hp _)
  exact (hpos.trans_le (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ 0))).ne'
    hzero.symm

private def zeroPath : RelationPath 2 :=
  ⟨fun _ => false, fun _ => ⟨0, rfl⟩⟩

private def alternatingPath : RelationPath 2 :=
  ⟨fun t => decide (t % 2 = 0), fun t => by
    by_cases ht : t % 2 = 0
    · refine ⟨1, ?_⟩
      have hn : (t + 1) % 2 ≠ 0 := by omega
      simp [hn]
    · exact ⟨0, by simp [ht]⟩⟩

def evidence : Registration arena (type_of% (@iid_return_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    refine ⟨⟨2, [], 1⟩, zeroPath, alternatingPath, ?_⟩
    change matchesReturnPrefix zeroPath [] 1 ≠ matchesReturnPrefix alternatingPath [] 1
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@iid_return_prefix) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.ParryReturnPrefix.iid_return_prefix
  realizationName := `Reg.D5.S3.TotalVariation.ParryReturnPrefix.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p r => matchesReturnPrefix r p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParryReturnPrefix
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.TotalVariation.ParryReturnPrefix
