import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence

namespace Reg.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence
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
  (fun role _ k => if role then carryless 19 k else carryless 25 k)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 9*k = R.readout false () k ↔ 15*k = R.readout true () k

private theorem low_digit (u k : ℕ) :
    ((carryless u k).testBit 0).toNat =
      ((u.testBit 0).toNat*(k.testBit 0).toNat)%2 := by
  have hs : ∀ t, ((carryless u k).testBit t).toNat =
      (∑ i ∈ Finset.range (t+1), (u.testBit i).toNat*(k.testBit (t-i)).toNat)%2 :=
    @Classical.choose_spec ℕ (fun z => ∀ t, (z.testBit t).toNat =
      (∑ i ∈ Finset.range (t+1), (u.testBit i).toNat*(k.testBit (t-i)).toNat)%2) _
  simpa using hs 0

def rejected (role : Bool) : Realization signature := realize signature
  (fun r _ k => if r = role then 1
    else actual.readout r () k) (fun e => nomatch e)

private theorem zero_value (u : ℕ) : carryless u 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  have hs : ∀ j, ((carryless u 0).testBit j).toNat =
      (∑ i ∈ Finset.range (j+1), (u.testBit i).toNat*((0:ℕ).testBit (j-i)).toNat)%2 :=
    @Classical.choose_spec ℕ (fun z => ∀ j, (z.testBit j).toNat =
      (∑ i ∈ Finset.range (j+1), (u.testBit i).toNat*((0:ℕ).testBit (j-i)).toNat)%2) _
  have h := hs t
  simp at h
  cases hc : (carryless u 0).testBit t <;> simp_all

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  have hh := h 0
  cases role <;> simpa [arena, rejected, actual, realize, zero_value] using hh

def registration : Registration arena
    (∀ k : ℕ, 9*k=carryless 25 k ↔ 15*k=carryless 19 k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected true, rejected_law true⟩
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
    intro h
    have h0 := low_digit (if i then 19 else 25) 0
    have h1 := low_digit (if i then 19 else 25) 1
    have heq : carryless (if i then 19 else 25) 0 =
        carryless (if i then 19 else 25) 1 := by
      cases i <;> simpa [actual, realize] using h
    rw [heq] at h0
    cases i <;> norm_num at h0 h1 <;> omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence.result)
    (type_of% (realize signature
      (fun role _ k => if role then carryless 19 k else carryless 25 k)
      (fun e => nomatch e))) (type_of% (@carryless)) Unit := {
  unitName := `Reg.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence.resultUnit,
  realizationName := `Reg.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence.registration,
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
    (fun role _ k => if role then carryless 19 k else carryless 25 k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@carryless),
  sourceSelection := some {
    owner := `D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence,
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
end Reg.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence
