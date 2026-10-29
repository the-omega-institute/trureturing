import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment
import Reg.Support.DependentFamily

/-! # Escape audit mirror for carryless multiplier containment -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Digit.Admissibility.CarrylessMultiplierEquivalence
open _root_.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment

namespace Reg.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment
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
  (fun role _ k => if role then carryless 31 k else carryless 29 k)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 13*k = R.readout false () k → 11*k = R.readout true () k

private theorem low_digit (u k : ℕ) :
    ((carryless u k).testBit 0).toNat =
      ((u.testBit 0).toNat*(k.testBit 0).toNat)%2 := by
  have hs : ∀ t, ((carryless u k).testBit t).toNat =
      (∑ i ∈ Finset.range (t+1), (u.testBit i).toNat*(k.testBit (t-i)).toNat)%2 :=
    @Classical.choose_spec ℕ (fun z => ∀ t, (z.testBit t).toNat =
      (∑ i ∈ Finset.range (t+1), (u.testBit i).toNat*(k.testBit (t-i)).toNat)%2) _
  simpa using hs 0

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

def rejected (role : Bool) : Realization signature := realize signature
  (fun r _ k => if r = role then
      if role then 1 else if k = 1 then 13 else actual.readout r () k
    else actual.readout r () k) (fun e => nomatch e)

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  cases role with
  | false =>
    have hh := h 1
    have hb : binaryProduct 31 1 = 31 := by
      unfold binaryProduct
      change Nat.evenOddRec 0 (fun _ r => 2 * r) (fun _ r => (2 * r) ^^^ 31)
        (2 * 0 + 1) = 31
      rw [Nat.evenOddRec_odd (H := by rfl)]
      norm_num
    norm_num [arena, rejected, actual, realize, carryless_eq, hb] at hh
  | true =>
    have hh := h 0
    simpa [arena, rejected, actual, realize, zero_value] using hh

def registration : Registration arena
    (∀ k : ℕ, 13*k=carryless 29 k → 11*k=carryless 31 k) where
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
    have h0 := low_digit (if i then 31 else 29) 0
    have h1 := low_digit (if i then 31 else 29) 1
    have heq : carryless (if i then 31 else 29) 0 =
        carryless (if i then 31 else 29) 1 := by
      cases i <;> simpa [actual, realize] using h
    rw [heq] at h0
    cases i <;> norm_num at h0 h1 <;> omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment.result)
    (type_of% (realize signature
      (fun role _ k => if role then carryless 31 k else carryless 29 k)
      (fun e => nomatch e))) (type_of% (@carryless)) Unit := {
  unitName := `Reg.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment.resultUnit,
  realizationName := `Reg.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment.registration,
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
    (fun role _ k => if role then carryless 31 k else carryless 29 k)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@carryless),
  sourceSelection := some {
    owner := `D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment,
    definition := none,
    coordinates := #[],
    readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration_1
end
end Reg.D5.S1.Digit.Admissibility.CarrylessThirteenElevenContainment
