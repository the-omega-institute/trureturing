import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.MoebiusLogarithmic
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x => reciprocalSum x) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, |R.readout () () x| ≤ 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  norm_num [rejected, realize] at hb

def registration : Registration arena (∀ x : ℝ, |reciprocalSum x| ≤ 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨abs_reciprocalSum_le_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      cases e
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : ℝ), (2 : ℝ), ?_⟩
    norm_num [actual, realize, reciprocalSum,
      show Finset.Ioc 0 2 = {1, 2} by decide,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)]
    change (0 : ℝ) ≠ 1 / 2
    norm_num

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.MoebiusLogarithmic.abs_reciprocalSum_le_one)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ _ x => reciprocalSum x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.MoebiusLogarithmic.abs_reciprocalSum_le_one.__information_unit,
  realizationName := `Reg.D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ x => reciprocalSum x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration
end Reg.D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
