/- GID: D5/S3/ConceptDynamics/PartialIdentification/QuaternaryResponseTableCoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/QuaternaryResponseTableCoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   digest: A k-stratum Boolean potential-outcome response table is exactly a k-digit quaternary word, hence has 4^k possibilities; the golden base-four DFAO input at index k is the Zeckendorf representation of this exact table-space capacity. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteConditionalResponseTable
import D5.S1.Digit.GoldenBase4AutomataOracle
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/- Library audit (2026-09-06): pinned Mathlib already owns
   `finFunctionFinEquiv : (Fin n -> Fin m) ≃ Fin (m^n)`, `Fintype.card_fun`,
   and `Equiv.piCongrRight`. The repository already owns `base4PowerWord k =
   zeckendorfMSDWord (4^k)`. This module supplies only the response-pair/quaternary
   bridge. Equality of the two appearances of 4^k is a radix-capacity identity;
   it does not identify DFAO state count with causal support size. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.QuaternaryResponseTableCoding

open D5.S1.Digit.GoldenBase4AutomataOracle

/-- Standard radix-four encoding of one Boolean complete response pair.
The first potential-outcome bit is the high binary bit and the second is low. -/
def responsePairDigitEquiv : (Bool × Bool) ≃ Fin 4 where
  toFun
    | (false, false) => 0
    | (false, true) => 1
    | (true, false) => 2
    | (true, true) => 3
  invFun digit :=
    if digit = 0 then (false, false)
    else if digit = 1 then (false, true)
    else if digit = 2 then (true, false)
    else (true, true)
  left_inv := by
    intro response
    rcases response with ⟨control, treated⟩
    cases control <;> cases treated <;> rfl
  right_inv := by
    intro digit
    fin_cases digit <;> rfl

/-- Coordinatewise quaternary encoding of a k-stratum response table. -/
def responseTableDigitEquiv (k : Nat) :
    (Fin k → Bool × Bool) ≃ (Fin k → Fin 4) :=
  Equiv.piCongrRight (fun _ : Fin k => responsePairDigitEquiv)

/-- A response table is exactly one integer code strictly below 4^k.
`finFunctionFinEquiv` is Mathlib's explicit finite-radix equivalence. -/
def responseTableCodeEquiv (k : Nat) :
    (Fin k → Bool × Bool) ≃ Fin (4 ^ k) :=
  (responseTableDigitEquiv k).trans finFunctionFinEquiv

/-- The unrestricted k-row Boolean response-table carrier has exactly 4^k states. -/
theorem responseTable_card_eq_four_pow (k : Nat) :
    Fintype.card (Fin k → Bool × Bool) = 4 ^ k := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  norm_num

/-- Every table code lies below the exact quaternary capacity boundary. -/
theorem responseTableCode_lt_capacity {k : Nat} (table : Fin k → Bool × Bool) :
    (responseTableCodeEquiv k table).val < 4 ^ k :=
  (responseTableCodeEquiv k table).isLt

/-- The k-th input of the golden base-four DFAO is literally the Zeckendorf
encoding of the cardinality of the unrestricted k-row Boolean response-table
carrier. This equates capacities, not automaton states or probability models. -/
theorem golden_base4_power_word_is_response_table_capacity (k : Nat) :
    base4PowerWord k =
      zeckendorfMSDWord (Fintype.card (Fin k → Bool × Bool)) := by
  rw [responseTable_card_eq_four_pow]
  rfl

/-- The first k base-four golden-ratio digits define one distinguished response
table after the standard quaternary response-pair decoding. -/
noncomputable def goldenResponsePrefix (k : Nat) : Fin k → Bool × Bool :=
  fun i => responsePairDigitEquiv.symm (base4GoldenDigit i.1)

/-- Encoding the distinguished response table returns the original golden digit. -/
@[simp] theorem goldenResponsePrefix_digit (k : Nat) (i : Fin k) :
    responsePairDigitEquiv (goldenResponsePrefix k i) = base4GoldenDigit i.1 := by
  simp [goldenResponsePrefix]

#print axioms responseTable_card_eq_four_pow
#print axioms responseTableCode_lt_capacity
#print axioms golden_base4_power_word_is_response_table_capacity
#print axioms goldenResponsePrefix_digit

end D5.S3.ConceptDynamics.PartialIdentification.QuaternaryResponseTableCoding
