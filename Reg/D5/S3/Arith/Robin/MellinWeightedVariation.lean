import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.MellinWeightedVariation
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false

open _root_.D5.S3.Arith.Robin.MellinWeightedVariation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.MellinWeightedVariation

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => weight t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 1 < t → 0 ≤ R.readout () () t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (t := 2) (by norm_num)
  change (0 : ℝ) ≤ -1 at hh
  norm_num at hh

def family : Registration arena (type_of% (@weight_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change weight 1 ≠ weight 2
    have h1 : weight 1 = 0 := by simp [weight]
    have h2 : 0 < weight 2 := by
      unfold weight
      positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    rw [h1]
    exact ne_of_lt h2

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_nonneg) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.MellinWeightedVariation.weight_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.MellinWeightedVariation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.MellinWeightedVariation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.Robin.MellinWeightedVariation
