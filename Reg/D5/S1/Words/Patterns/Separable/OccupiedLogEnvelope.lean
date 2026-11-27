import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope
import Reg.Support.DependentFamily

/-! At fixed scale, the actual lower envelope varies with the integer position. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope

open _root_.D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t z => t * discrepancyProfile z) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ceiling + 1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ t > (0 : ℝ), ∀ z : ℤ,
      R.readout () t z ≤ rawOccupation z ∧
      (2 / a) * t * discrepancyProfile z ≤ occupation z

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨t, ht, H⟩
  have h := (H 0).1
  change ceiling + 1 ≤ rawOccupation 0 at h
  obtain ⟨_, _, _, _, Hcap, _⟩ := actual_occupation_subsolution_comparison
  linarith only [h, (Hcap 0).2]

def family : Registration arena (type_of% @actual_raw_occupation_log_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_raw_occupation_log_envelope, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    change (1 : ℝ) * discrepancyProfile 1 ≠ 1 * discrepancyProfile 2
    rw [one_mul, one_mul]
    have hd : Real.sqrt 3 * Real.log 3 < Real.sqrt 4 * Real.log 4 := by
      have hlog : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      calc
        _ < Real.sqrt 3 * Real.log 4 :=
          mul_lt_mul_of_pos_left hlog (Real.sqrt_pos.mpr (by norm_num))
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num))
          (Real.log_nonneg (by norm_num))
    have hf : discrepancyProfile 2 < discrepancyProfile 1 := by
      simpa [discrepancyProfile, show (2 : ℝ) + 1 = 3 by norm_num,
        show (2 : ℝ) + 2 = 4 by norm_num] using
        (one_div_lt_one_div_of_lt (mul_pos (Real.sqrt_pos.mpr (by norm_num))
          (Real.log_pos (by norm_num))) hd)
    exact hf.ne'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_raw_occupation_log_envelope) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t z => t * discrepancyProfile z)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedLogEnvelope
