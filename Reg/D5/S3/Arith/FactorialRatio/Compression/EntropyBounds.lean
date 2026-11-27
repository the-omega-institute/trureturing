import D5.S3.Arith.FactorialRatio.Compression.EntropyBounds
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The signed entropy average as an observed real-valued function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyBounds

open Real
open _root_.D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
open _root_.D5.S3.Arith.FactorialRatio.Compression.EntropyBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    -(161 / 288 : ℝ) ≤ R.readout () () t ∧
      (161 / 288 : ℝ) < 2 * log 2 - 3 / 4 * log 3 ∧
      2 * log 2 - 3 / 4 * log 3 < (563 / 1000 : ℝ) ∧
      (563 / 1000 : ℝ) < Real.eulerMascheroniConstant

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 le_rfl (by norm_num)).1
  change -(161 / 288 : ℝ) ≤ -100 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change entropyIntegral 0 ≠ entropyIntegral 1
  rw [entropy_profile.2.1, entropy_profile.2.2.1]
  norm_num

def family : Registration arena (type_of% @sharp_entropy_profile_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_entropy_profile_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro i hi
      cases role
      cases i
      exact (hi rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_entropy_profile_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.EntropyBounds.sharp_entropy_profile_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => entropyIntegral t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.EntropyBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.EntropyBounds
