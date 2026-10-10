import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity

open Set MeasureTheory
open _root_.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
open _root_.D5.S3.Arith.Robin.ActualFactorialRobinHighDerivative (highRemainder)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ y => cumulative y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The entire signed cumulative and high-integral law is retained. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 0 ∧
    R.readout () () 2 = Real.log 2 - (Real.log 2) ^ 2 / 2 ∧
    (∀ Y : ℝ, 1 ≤ Y → Real.log Y / Y ≤ R.readout () () Y ∧
      R.readout () () Y ≤ 2 - (Real.log Y + 2) / Y ∧ R.readout () () Y < 2) ∧
    (∀ Y : ℝ, 1 < Y → 0 < R.readout () () Y) ∧
    (∀ Y : ℝ, 2 ≤ Y → kappa + Real.log Y / Y ≤ R.readout () () Y) ∧
    0 < kappa ∧
    (∀ r : ℝ, 0 < r →
      IntegrableOn (fun y => R.readout () () y * tailKernel r y) (Ioi (1 : ℝ)) ∧
      highRemainder r = ∫ u in Ioi (0 : ℝ), R.readout () () (Real.exp u) *
        ((r + u)⁻¹ ^ 2 + 2 * (r + u)⁻¹ ^ 3) ∧
      kappa * ((r + Real.log 2)⁻¹ + (r + Real.log 2)⁻¹ ^ 2) < highRemainder r ∧
      highRemainder r < 2 * (r⁻¹ + r⁻¹ ^ 2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : ℝ) = Real.log 2 - (Real.log 2) ^ 2 / 2 := h.2.1
  have hp := result.2.2.2.1 2 (by norm_num)
  rw [result.2.1, ← hz] at hp
  exact (lt_irrefl (0 : ℝ)) hp

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), 2, ?_⟩
    change cumulative 1 ≠ cumulative 2
    rw [result.1]
    exact (ne_of_gt (result.2.2.2.1 2 (by norm_num))).symm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ActualFactorialCumulativePositivity.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity.family
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
    owner := `D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨family⟩⟩
  options := #[]

/-- Source-level audit attempt for the original representation exposed to its
actual high-weight consumer. Source selection and binding evidence remain open. -/
abbrev yArena : Arena where
  signature := signature
  Law R := ∀ r : ℝ, 0 < r →
    highRemainder r = ∫ y in Ioi (1 : ℝ), R.readout () () y * tailKernel r y

theorem rejected_y_law : ¬ yArena.Law rejected := by
  intro h
  have hz : highRemainder 1 = 0 := by
    simpa [rejected, realize] using h 1 (by norm_num)
  have hl := (result.2.2.2.2.2.2 1 (by norm_num)).2.2.1
  have hk := result.2.2.2.2.2.1
  have hc : 0 < 1 + Real.log (2 : ℝ) := by positivity
  rw [hz] at hl
  have hp : 0 < kappa * ((1 + Real.log 2)⁻¹ + (1 + Real.log 2)⁻¹ ^ 2) := by positivity
  linarith

def yFamily : Registration yArena (type_of% (@positive_representation_y)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_representation_y, rejected, rejected_y_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_y_law⟩, fun e => nomatch e⟩
  dependence := family.dependence

def yRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_representation_y) (type_of% (realize signature actual.readout actual.anchor))
    (ℝ → ℝ) Unit where
  unitName := `D5.S3.Arith.Robin.ActualFactorialCumulativePositivity.positive_representation_y.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity.yFamily
  realizationSource := none
  generated := false
  arena := .source ⟨yArena⟩
  objectArena := .source ⟨yArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source yArena ⟨yFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some cumulative
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms yFamily
#print axioms yRegistration

#print axioms registration

end
end Reg.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
