import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.QuadraticMidpointEnergy
import Reg.Support.SingleDependentReadout

/-! Observe the original length cap in the maximal-energy term on the left.
The original right-hand cap and the original prime and length premises remain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace Reg.D5.S3.CharacterSums.QuadraticMidpointEnergy

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.CharacterSums.QuadraticMidpointEnergy
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ ↦ ℕ) (fun _ ↦ ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ Z ↦ Z) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 1) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p Z : ℕ) [Fact p.Prime], 2 < p → Z < p →
    (∑ a : ZMod p, quadraticMaximalEnergy p (R.readout () p Z) a) ≤
      (p : ℝ) * Z * (5 + 2 * Real.log p)

private theorem one_le_energy (a : ZMod 3) :
    1 ≤ quadraticMaximalEnergy 3 1 a := by
  unfold quadraticMaximalEnergy
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro r ⟨m, w, hw, n, hn, rfl⟩
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · norm_num
    · simp [quadraticTerm, ZMod.stdAddChar_apply]
  · refine ⟨0, 1, by simp, 1, le_rfl, ?_⟩
    simp [quadraticTerm]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := h 3 0 (by decide) (by decide)
  have hz : (∑ a : ZMod 3, quadraticMaximalEnergy 3 1 a) ≤ 0 := by
    simpa [rejected, realize] using hh
  have hpos : (3 : ℝ) ≤ ∑ a : ZMod 3, quadraticMaximalEnergy 3 1 a := by
    calc
      3 = ∑ _a : ZMod 3, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun a _ ↦ one_le_energy a)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena (type_of% (@quadratic_maximal_energy_average_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨quadratic_maximal_energy_average_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quadratic_maximal_energy_average_le) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.CharacterSums.QuadraticMidpointEnergy.quadratic_maximal_energy_average_le
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.QuadraticMidpointEnergy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z ↦ Z) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.QuadraticMidpointEnergy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.QuadraticMidpointEnergy
