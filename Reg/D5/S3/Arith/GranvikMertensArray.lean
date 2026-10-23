import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GranvikMertensArray
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GranvikMertensArray

open _root_.D5.S3.Arith.GranvikMertensArray
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ n => Bool.rec (T n n) (T 1 n) role)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 1 ≤ n → R.readout false () n =
      (n : ℚ) * (ArithmeticFunction.moebius n : ℚ)) ∧
    (∀ k : ℕ, 2 ≤ k → R.readout true () k =
      2 + ∑ j ∈ Icc 1 k, (ArithmeticFunction.moebius j : ℚ))

def rejected (role : Bool) : Realization signature :=
  realize signature (fun r p n => if r = role then 0 else actual.readout r p n)
    (fun e => nomatch e)

theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  cases role with
  | false =>
    have hh := h.1 1 (by decide)
    norm_num [rejected, realize] at hh
  | true =>
    have hh := h.2 2 (by decide)
    norm_num [rejected, realize, show Icc 1 2 = {1, 2} by decide,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hh

theorem dependence : ObservationalDependence signature actual := by
  have hd : T 1 1 = 1 := by
    simpa using result.1 1 (by decide)
  have hr : T 1 2 = 2 := by
    have hh := result.2 2 (by decide)
    norm_num [show Icc 1 2 = {1, 2} by decide,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hh
    exact hh
  have hz (n : ℕ) : T n 0 = 0 := by
    rw [T.eq_def]
    simp
  intro role
  cases role with
  | false =>
    refine ⟨(), 0, 1, ?_⟩
    change T 0 0 ≠ T 1 1
    rw [hz 0, hd]
    norm_num
  | true =>
    refine ⟨(), 0, 2, ?_⟩
    change T 1 0 ≠ T 1 2
    rw [hz 1, hr]
    norm_num

def registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro other hne
      funext p n
      simp only [rejected, realize, if_neg hne]
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.GranvikMertensArray.result.audit
  realizationName := `Reg.D5.S3.Arith.GranvikMertensArray.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun role _ n => Bool.rec (T n n) (T 1 n) role)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GranvikMertensArray
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["fn", "arg", "body", "body", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.GranvikMertensArray
