/- GID: D5/S1/Words/Palindromes/ThueMorseSignedCut
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ThueMorseSignedCut
   mirror-E: none(waiver:literal-word-reflection)
   anchors: []
   utility: none
   digest: Allowed Thue-Morse factors increase signed weight by at most one. -/

import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.Palindromes.PeriodDoubling.SignedCutLowerBound

/-! Reflections of literal Thue-Morse factors and the signed cut potential. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.ThueMorse

open D5.S1.Words.Complexity
open D5.S1.Words.Palindromes.PeriodDoubling

/-- Reversal or exchange followed by reversal fixes the finite binary word. -/
def Allowed (w : List Bool) : Prop :=
  List.Palindrome w ∨ w = w.reverse.map Bool.not

/-- The original adjacent transition is the complement of the literal period-doubling word. -/
theorem transition_period_doubling (n : ℕ) :
    transition n = if u_pd n then 0 else 1 := by
  have val (m : ℕ) : u_pd m = decide (padicValNat 2 (m + 1) % 2 = 1) := by
    have hm : m < 2 ^ (m + 1) := by
      have h := Nat.lt_two_pow_self (n := m + 1)
      omega
    have h := (block_valuation (m + 1)).2 m hm
    simp [u_pd, h]
  have even (m : ℕ) : u_pd (2 * m) = false := by
    rw [val, padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * m + 1)]
    rfl
  have odd (m : ℕ) : u_pd (2 * m + 1) = !u_pd m := by
    have hv : padicValNat 2 (2 * m + 1 + 1) = 1 + padicValNat 2 (m + 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
        padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega), padicValNat_self]
    rw [val, val, hv]
    by_cases h : padicValNat 2 (m + 1) % 2 = 1
    · have hh : (1 + padicValNat 2 (m + 1)) % 2 ≠ 1 := by omega
      simp [h, hh]
    · have hh : (1 + padicValNat 2 (m + 1)) % 2 = 1 := by omega
      simp [h, hh]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · subst n
      simp [even]
    · subst n
      rw [transition_two_mul_add_one, ih m (by omega), odd]
      cases u_pd m <;> rfl

private def Reflect (start length : ℕ) (flip : Bool) : Prop :=
  ∀ r : ℕ, r < length →
    thueMorse (start + r) = (flip != thueMorse (start + (length - 1 - r)))

private theorem allowed_reflect (start length : ℕ)
    (h : Allowed (factor length start)) : ∃ flip, Reflect start length flip := by
  rcases h with h | h
  · refine ⟨false, ?_⟩
    intro r hr
    have he := congrArg (fun w : List Bool => w[r]?) h.reverse_eq
    simpa [List.getElem?_reverse, factor, hr, show length - 1 - r < length by omega] using he.symm
  · refine ⟨true, ?_⟩
    intro r hr
    have he := congrArg (fun w : List Bool => w[r]?) h
    simpa [List.getElem?_reverse, factor, hr, show length - 1 - r < length by omega] using he

private theorem reflect_derivative (start length : ℕ) (flip : Bool)
    (h : Reflect start length flip) :
    List.Palindrome (List.ofFn (fun r : Fin (length - 1) => u_pd (start + r))) := by
  apply List.Palindrome.of_reverse_eq
  apply List.ext_getElem
  · simp
  · intro r hr hs
    simp only [List.length_reverse, List.length_ofFn] at hr
    rw [List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    have h0 := h r (by omega)
    have h1 := h (r + 1) (by omega)
    have hidx : length - 1 - r = length - 1 - 1 - r + 1 := by omega
    have he : transition (start + (length - 1 - 1 - r)) = transition (start + r) := by
      simp only [transition]
      rw [show start + (length - 1 - 1 - r) + 1 = start + (length - 1 - r) by omega]
      rw [show start + r + 1 = start + (r + 1) by omega, h0, h1]
      have hi : start + (length - 1 - (r + 1)) = start + (length - 1 - 1 - r) := by omega
      rw [hi]
      cases flip <;> cases thueMorse (start + (length - 1 - r)) <;>
        cases thueMorse (start + (length - 1 - 1 - r)) <;> decide
    rw [transition_period_doubling, transition_period_doubling] at he
    have inj (x y : Bool) (h : (if x then 0 else 1 : ℕ) = if y then 0 else 1) : x = y := by
      cases x <;> cases y <;> simp_all
    exact inj _ _ he

end D5.S1.Words.Palindromes.ThueMorse

#print axioms D5.S1.Words.Palindromes.ThueMorse.transition_period_doubling
