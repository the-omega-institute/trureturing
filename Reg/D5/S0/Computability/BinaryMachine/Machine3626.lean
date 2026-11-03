import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.BinaryMachine.Machine3626
import Reg.Support.DependentFamily

/-! Whole-family source-bound audits for the three live operational declarations. -/

namespace Reg.D5.S0.Computability.BinaryMachine.Machine3626

open _root_.D5.S0.Computability.BinaryMachine.Machine3626
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Block

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (higher : List Bool),
    Trace (R.readout () () k) ⟨.A, block k higher, []⟩ none

def actual : Realization signature :=
  realize signature (fun _ _ k => 4 * 2 ^ k - 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actual_bridge : (type_of% @block_first_crossing) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h 0 []
  change Trace 0 _ none at ht
  cases ht

def registration : Registration arena (type_of% @block_first_crossing) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp block_first_crossing, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (1 : ℕ) ≠ 5; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@block_first_crossing)
    (type_of% (realize signature (fun _ _ k => 4 * 2 ^ k - 3) (fun e => nomatch e)))
    Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Block.block_first_crossing "__information_unit",
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Block.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 4 * 2 ^ k - 3) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.Machine3626,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "arg", "arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Block

namespace Prefix

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 0 < n),
    ∃ (k : ℕ) (higher : List Bool), R.readout () () n = block k higher ∧
      Trace (4 * 2 ^ k - 3) (initial n) none

def actual : Realization signature :=
  realize signature (fun _ _ n => n.bits) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

theorem actual_bridge : (type_of% @positive_input_first_crossing) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, higher, hk, _⟩ := h 1 (by decide)
  change [] = block k higher at hk
  cases k <;> simp [block, List.replicate_succ] at hk

def registration : Registration arena (type_of% @positive_input_first_crossing) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp positive_input_first_crossing, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change ([] : List Bool) ≠ [true]; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_input_first_crossing)
    (type_of% (realize signature (fun _ _ n => n.bits) (fun e => nomatch e)))
    Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Prefix.positive_input_first_crossing "__information_unit",
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Prefix.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => n.bits) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.Machine3626,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Prefix

namespace Exact

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 0 < n), ∃ t : ℕ,
    Trace t (initial n) none ∧ (t : ℤ) = R.readout () () n

def actual : Realization signature :=
  realize signature (fun _ _ n => ∑ d ∈ n.divisors,
    (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * ArithmeticFunction.moebius e) ^ 2 *
      (Nat.totient d : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actual_bridge : (type_of% @result) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht, he⟩ := h 1 (by decide)
  have hz : t = 0 := by change (t : ℤ) = 0 at he; omega
  subst t
  cases ht

def registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change (∑ d ∈ (1 : ℕ).divisors,
      (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * ArithmeticFunction.moebius e) ^ 2 *
        (Nat.totient d : ℤ)) ≠
      ∑ d ∈ (2 : ℕ).divisors,
      (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * ArithmeticFunction.moebius e) ^ 2 *
        (Nat.totient d : ℤ)
    norm_num [Nat.prime_two.divisors,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result)
    (type_of% (realize signature (fun _ _ n => ∑ d ∈ n.divisors,
    (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * ArithmeticFunction.moebius e) ^ 2 *
      (Nat.totient d : ℤ)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Exact.result "__information_unit",
  realizationName := `Reg.D5.S0.Computability.BinaryMachine.Machine3626.Exact.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => ∑ d ∈ n.divisors,
    (∑ e ∈ d.divisors, (-1 : ℤ) ^ (e + 1) * ArithmeticFunction.moebius e) ^ 2 *
      (Nat.totient d : ℤ)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.BinaryMachine.Machine3626,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn", "arg", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Exact

end Reg.D5.S0.Computability.BinaryMachine.Machine3626
