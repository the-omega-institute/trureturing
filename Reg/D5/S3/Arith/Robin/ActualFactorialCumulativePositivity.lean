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

#print axioms registration

end
end Reg.D5.S3.Arith.Robin.ActualFactorialCumulativePositivity
