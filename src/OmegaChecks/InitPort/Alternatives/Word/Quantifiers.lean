module
import all Init.Data.BitVec.Decidable
import Init.Data.Nat.Lemmas

/-! Construct witnesses for decidable predicates over finite bit vectors. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem existsIffNotAll {n : Nat} (P : BitVec n → Prop) [DecidablePred P] :
    (¬∀ v, ¬P v) ↔ ∃ v, P v := by
  constructor
  · intro doubleNeg
    by_cases found : ∃ i : Fin (2^n), P (BitVec.ofFin i)
    · obtain ⟨i, hi⟩ := found
      exact ⟨BitVec.ofFin i, hi⟩
    · exact False.elim (doubleNeg fun v hit => found ⟨v.toFin, hit⟩)
  · exact fun ⟨v, hit⟩ missing => missing v hit

@[instance_reducible] public def BitVec.instDecidableExistsBitVecZero :
    type_of% @_root_.BitVec.instDecidableExistsBitVecZero := by
  intro P dec
  apply decidable_of_iff (¬∀ v, ¬P v)
  constructor
  · intro doubleNeg
    cases dec with
    | isTrue yes => exact ⟨0, yes⟩
    | isFalse no => exact False.elim (doubleNeg (BitVec.forall_zero_iff.mpr no))
  · exact fun ⟨v, hit⟩ missing => missing v hit

@[instance_reducible] public def BitVec.instDecidableExistsBitVecSucc :
    type_of% @_root_.BitVec.instDecidableExistsBitVecSucc := by
  intro n P _ _
  exact decidable_of_iff (¬∀ v, ¬P v) (existsIffNotAll P)

end OmegaChecks.InitPort.Alternatives
