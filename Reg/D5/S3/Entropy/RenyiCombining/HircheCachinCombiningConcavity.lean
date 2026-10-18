import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete Hirche threshold and combining claim. -/

namespace Reg.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
open _root_.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the threshold as real data at its strict lower bound. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ αhat => αhat) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the threshold and both complete order ranges of the source claim. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ αhat : ℝ, 1 < R.readout () () αhat ∧ αhat < (13863 : ℝ) / 10000 ∧
    (∀ α : ℝ, 0 < α → α < αhat → ∀ y ∈ Icc 0 (Real.log 2),
      ConvexOn ℝ (Icc 0 (Real.log 2)) (fun x => G α x y)) ∧
    (∀ α : ℝ, 2 ≤ α → ∀ y ∈ Icc 0 (Real.log 2),
      ConcaveOn ℝ (Icc 0 (Real.log 2)) (fun x => G α x y))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨αhat, hlow, _⟩
  change (1 : ℝ) < 0 at hlow
  exact (by norm_num : ¬ (1 : ℝ) < 0) hlow

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.unit
  realizationName :=
    `Reg.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ αhat => αhat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
    definition := some {
      owner := `D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
      name := `D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
