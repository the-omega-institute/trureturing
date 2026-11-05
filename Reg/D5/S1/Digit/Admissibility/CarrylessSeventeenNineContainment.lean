import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment
import Reg.Support.DependentFamily

/-! # Source-bound audit of the carryless containment implication -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

namespace Reg.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment
noncomputable section

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
  (fun role _ k => if role then carryless 25 k else carryless 49 k)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 17*k = R.readout false () k → 9*k = R.readout true () k

def rejected (role : Bool) : Realization signature := realize signature
  (fun r _ k => if r = role then (if role then 1 else 17*k)
    else actual.readout r () k) (fun e => nomatch e)

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  cases role with
  | false =>
    have hh := h 1
    norm_num [arena, rejected, actual, realize, carryless_eq, binaryProduct] at hh
    change (9 : ℕ) = 25 at hh
    omega
  | true =>
    have hh := h 0
    norm_num [arena, rejected, actual, realize, carryless_eq, binaryProduct] at hh

def sourceRegistration : Registration arena
    (∀ k : ℕ, 17*k=carryless 49 k → 9*k=carryless 25 k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment.result,
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
    cases i <;> norm_num [actual, realize, carryless_eq, binaryProduct] <;> decide

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment.result)
    (type_of% (realize signature
      (fun role _ k => if role then carryless 25 k else carryless 49 k)
      (fun e => nomatch e))) (type_of% (@carryless)) Unit := {
  unitName := `Reg.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment.resultUnit,
  realizationName := `Reg.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun role _ k => if role then carryless 25 k else carryless 49 k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@carryless),
  sourceSelection := some {
    owner := `D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment,
    definition := none,
    coordinates := #[],
    readouts := #[
      { path := #["body", "domain", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sourceRegistration
#print axioms registration
end
end Reg.D5.S1.Digit.Admissibility.CarrylessSeventeenNineContainment
