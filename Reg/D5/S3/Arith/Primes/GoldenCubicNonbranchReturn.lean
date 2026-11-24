import D5.S3.Arith.Primes.GoldenCubicNonbranchReturn
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

open D5.S3.Arith.Primes.GoldenCubicNonbranchReturn

namespace Reg.D5.S3.Arith.Primes.GoldenCubicNonbranchReturn
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ × ℤ × ℕ)
    (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ (q : ℕ × ℤ × ℕ) =>
    Function.minimalPeriod step (q.2.1:ZMod (q.1^q.2.2))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let observed := R.readout () ()
    NonbranchPeriodLaw observed

private theorem zero_period {R : Type*} [CommRing R] :
    Function.minimalPeriod step (0:R)=1 := by
  apply Function.minimalPeriod_eq_one_iff_isFixedPt.mpr
  show step (0:R)=0
  simp [step]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change NonbranchPeriodLaw (fun _ => 0) at h
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h0 : Function.minimalPeriod step (↑(0:ℤ):ZMod 7)=1 := by
    rw [Int.cast_zero]
    exact zero_period
  have hv := h 7 (by decide) 0 (by decide) (by rw [h0]; decide)
  obtain ⟨_, hv⟩ := hv
  rcases hv with hconst | ⟨d, hd, hformula⟩
  · have hh := hconst 1 (by decide)
    rw [h0] at hh
    exact Nat.zero_ne_one hh
  · have hh := hformula 1 (by decide)
    rw [h0, one_mul, Nat.sub_eq_zero_of_le hd, pow_zero] at hh
    have hOrder (u : ZMod 1) : orderOf u = 1 := by
      rw [Subsingleton.elim u (1:ZMod 1), orderOf_one]
    rw [hOrder] at hh
    exact Nat.zero_ne_one hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hi : i=() := Subsingleton.elim _ _
  subst i
  refine ⟨(), (7,7,1), (7,7,2), ?_⟩
  change Function.minimalPeriod step (↑(7:ℤ):ZMod 7) ≠
    Function.minimalPeriod step (↑(7:ℤ):ZMod 49)
  rw [show (↑(7:ℤ):ZMod 7)=0 by decide,zero_period]
  intro heq
  have hf := Function.minimalPeriod_eq_one_iff_isFixedPt.mp heq.symm
  change step (↑(7:ℤ):ZMod 49)=(↑(7:ℤ):ZMod 49) at hf
  exact (by decide : step (↑(7:ℤ):ZMod 49)≠(↑(7:ℤ):ZMod 49)) hf

def family : Registration arena (type_of% @nonbranch_minimal_period) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nonbranch_minimal_period, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@nonbranch_minimal_period) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicNonbranchReturn.nonbranch_minimal_period.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicNonbranchReturn.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ (q : ℕ × ℤ × ℕ) =>
    Function.minimalPeriod step (q.2.1:ZMod (q.1^q.2.2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicNonbranchReturn
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Primes.GoldenCubicNonbranchReturn
