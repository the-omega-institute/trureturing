import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.FIBUnequalMarginals

/-! Source observation for the sum of the two differences at unequal marginals. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FIBUnequalMarginals

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.FIBUnequalMarginals
open _root_.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ a b => a + b) (fun x => nomatch x)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun x => nomatch x)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s h k t w a b : ℝ},
    ((∃ A : Fin 5 → Set ℝ, Nested A ∧
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1) ∧
      volume.real (A 0) = s ∧ volume.real (A 1) = h ∧ volume.real (A 2) = k ∧
      volume.real (A 3) = t ∧ volume.real (A 4) = w ∧
      volume.real (A 4 \ A 0) = a ∧ volume.real (A 3 \ A 1) = b) ↔
      0 ≤ s ∧ h ≤ 1 ∧ k ≤ 1 ∧ t ≤ k ∧
      (max 0 (w - s) ≤ a ∧ a ≤ min w (h - s)) ∧
      (max 0 (t - h) ≤ b ∧ b ≤ min t (1 - h)) ∧ R.readout () a b ≤ k - s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have wrong := (law (s := 1 / 2) (h := 2 / 3) (k := 2 / 3) (t := 1 / 2) (w := 1 / 2)
    (a := 1 / 6) (b := 1 / 6)).2 (by norm_num [rejected, realize, max_def, min_def])
  have bound := (joint_range (s := 1 / 2) (h := 2 / 3) (k := 2 / 3) (t := 1 / 2) (w := 1 / 2)
    (a := 1 / 6) (b := 1 / 6)).1 wrong
  norm_num at bound

def family : Registration arena (type_of% (@joint_range)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joint_range, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun x => nomatch x⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@joint_range) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBUnequalMarginals.joint_range.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBUnequalMarginals.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => a + b) (fun x => nomatch x))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBUnequalMarginals
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.FIBUnequalMarginals
