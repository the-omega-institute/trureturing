import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
import Reg.Support.DependentFamily

/-! The explicit lower readout varies with the exponent of the exact signed law. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => gapCoefficient * (β - 1 / 2)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ β : ℝ, 0 ≤ β → β < 1 → Integrable (signedKernel β)) ∧
    J (1 / 2) = 0 ∧ 0 < gapCoefficient ∧
    (∀ β : ℝ, 1 / 2 ≤ β → β < 1 → R.readout () () β ≤ J β)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law.2.2.2 (1 / 2) le_rfl (by norm_num)
  change (1 : ℝ) ≤ J (1 / 2) at h
  rw [law.2.1] at h
  norm_num at h

def family : Registration arena (type_of% @signed_mellin_cancellation_and_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_mellin_cancellation_and_gap, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), 1 / 2, 3 / 4, ?_⟩
    change gapCoefficient * ((1 : ℝ) / 2 - 1 / 2) ≠
      gapCoefficient * (3 / 4 - 1 / 2)
    have hc := signed_mellin_cancellation_and_gap.2.2.1
    have hpos : 0 < gapCoefficient * ((3 : ℝ) / 4 - 1 / 2) :=
      mul_pos hc (by norm_num)
    simpa only [sub_self, mul_zero] using hpos.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_mellin_cancellation_and_gap) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ β => gapCoefficient * (β - 1 / 2))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinKelvin
