import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

namespace Reg.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role _ k => if role then carryless 13 k else carryless 11 k)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 7*k = R.readout false () k ↔ 5*k = R.readout true () k

def rejected (role : Bool) : Realization signature := realize signature
  (fun r _ k => if r = role then 1 else actual.readout r () k)
  (fun e => nomatch e)

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h 0
  cases role <;> simpa [arena, rejected, actual, realize, carryless_eq, binaryProduct] using hh

def registration : Registration arena
    (∀ k : ℕ, 7*k=carryless 11 k ↔ 5*k=carryless 13 k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence.result,
    rejected true, rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p k
      simp [rejected, realize, hj]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    cases i <;> simp [actual, realize, carryless_eq, binaryProduct, Nat.evenOddRec]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence.result)
    (type_of% (realize signature
      (fun role _ k => if role then carryless 13 k else carryless 11 k)
      (fun e => nomatch e))) (type_of% (@carryless)) Unit := {
  unitName := `Reg.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence.resultUnit,
  realizationName := `Reg.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun role _ k => if role then carryless 13 k else carryless 11 k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@carryless),
  sourceSelection := some {
    owner := `D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence,
    definition := none,
    coordinates := #[],
    readouts := #[
      { path := #["body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration_1
end
end Reg.D5.S1.Digit.Admissibility.CarrylessSevenFiveEquivalence
