/- GID: D5/S1/Recurrence/Residue/QuetRationalIterationDenominator
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/QuetRationalIterationDenominator
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: For m >= 2, Quet's reduced denominators satisfy the conjectured recurrence. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.QuetRationalIterationDenominator

mutual
  /-- Numerators of the iteration, with the source sequence at indices `n >= 1`. -/
  def num : ℕ → ℕ
    | 0 => 0
    | 1 => 1
    | n + 2 => num (n + 1) * (num (n + 1) + 2 * den (n + 1))

  /-- Denominators of the iteration, with the source sequence at indices `n >= 1`. -/
  def den : ℕ → ℕ
    | 0 => 1
    | 1 => 1
    | n + 2 => den (n + 1) * (num (n + 1) + den (n + 1))
end

/-- The rational sequence in the OEIS definition, extended by `b 0 = 0`. -/
def b : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => b (n + 1) + 1 / (1 + 1 / b (n + 1))

private theorem num_pos : ∀ n : ℕ, 1 ≤ n → 0 < num n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [num]
      | succ n =>
          intro _
          rw [num]
          exact Nat.mul_pos (ih (by omega)) (Nat.add_pos_left (ih (by omega)) _)

private theorem den_pos (n : ℕ) : 0 < den n := by
  induction n with
  | zero => simp [den]
  | succ n ih =>
      cases n with
      | zero => simp [den]
      | succ n =>
          rw [den]
          exact Nat.mul_pos ih (by omega)

private theorem b_pair : ∀ n : ℕ, b n = (num n : ℚ) / den n := by
  intro n
  induction n with
  | zero => simp [b, num, den]
  | succ n ih =>
      cases n with
      | zero => simp [b, num, den]
      | succ n =>
          rw [b, ih, num, den]
          have hp : (num (n + 1) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (num_pos (n + 1) (by omega)))
          have hq : (den (n + 1) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (den_pos (n + 1)))
          field_simp [hp, hq]
          norm_num [Nat.cast_mul, Nat.cast_add]
          ring

private theorem b_den (n : ℕ) (_hn : 1 ≤ n) : (b n).den = den n := by
  clear _hn
  rw [b_pair n]
  have hcopNat : Nat.Coprime (num n) (den n) := by
    induction n with
    | zero => simp [num, den]
    | succ n ih =>
        cases n with
        | zero => simp [num, den]
        | succ n =>
            have hleft : Nat.Coprime (num (n + 1)) (den (n + 1)) := ih
            rw [num, den, Nat.coprime_mul_iff_left]
            constructor
            · apply Nat.coprime_mul_iff_right.mpr
              exact ⟨hleft, Nat.coprime_self_add_right.mpr hleft⟩
            · apply Nat.coprime_mul_iff_right.mpr
              constructor
              · exact (Nat.coprime_add_mul_right_left (num (n + 1))
                  (den (n + 1)) 2).mpr hleft
              · have hsum :
                    Nat.Coprime (num (n + 1) + den (n + 1)) (den (n + 1)) :=
                    Nat.coprime_add_self_left.mpr hleft
                have hcross :=
                  (Nat.coprime_add_mul_left_right
                    (num (n + 1) + den (n + 1)) (den (n + 1)) 1).mpr hsum
                have hcross' :
                    Nat.Coprime (num (n + 1) + den (n + 1))
                      (num (n + 1) + 2 * den (n + 1)) := by
                  convert hcross using 1
                  all_goals omega
                exact hcross'.symm
  have hcop :
      Nat.Coprime (Int.natAbs (num n : ℤ)) (Int.natAbs (den n : ℤ)) := by
    simpa using hcopNat
  have h := Rat.den_div_eq_of_coprime (a := (num n : ℤ)) (b := (den n : ℤ))
    (by exact_mod_cast den_pos n) hcop
  have h' : ((num n : ℚ) / (den n : ℚ)).den = den n := by
    apply Int.ofNat_inj.mp
    simpa using h
  exact h'

/-- Quet's recurrence for the reduced denominators of the rational iteration `b`. -/
theorem result (m : ℕ) (hm : 2 ≤ m) :
    (b (m - 1)).den ^ 2 ∣ (b m).den ^ 3 ∧
      (b (m + 1)).den = (b m).den ^ 2 + (b m).den ^ 3 / (b (m - 1)).den ^ 2 -
        (b m).den * (b (m - 1)).den ^ 2 := by
  rw [b_den (m - 1) (by omega), b_den m (by omega), b_den (m + 1) (by omega)]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
  change den (n + 1) ^ 2 ∣ den (n + 2) ^ 3 ∧
    den (n + 3) = den (n + 2) ^ 2 + den (n + 2) ^ 3 / den (n + 1) ^ 2 -
      den (n + 2) * den (n + 1) ^ 2
  have hdm : den (n + 2) = den (n + 1) * (num (n + 1) + den (n + 1)) := rfl
  have hnm : num (n + 2) = num (n + 1) * (num (n + 1) + 2 * den (n + 1)) := rfl
  have hdn : den (n + 3) = den (n + 2) * (num (n + 2) + den (n + 2)) := rfl
  have hqpos : 0 < den (n + 1) ^ 2 := pow_pos (den_pos (n + 1)) _
  have hquot : den (n + 2) ^ 3 / den (n + 1) ^ 2 =
      den (n + 2) * (num (n + 1) + den (n + 1)) ^ 2 := by
    apply Nat.div_eq_of_eq_mul_right hqpos
    rw [hdm]
    ring
  have hle : den (n + 2) * den (n + 1) ^ 2 ≤
      den (n + 2) ^ 2 + den (n + 2) *
        (num (n + 1) + den (n + 1)) ^ 2 := by
    have hs : den (n + 1) ≤ num (n + 1) + den (n + 1) := by omega
    have hsquare : den (n + 1) ^ 2 ≤
        den (n + 1) * (num (n + 1) + den (n + 1)) := by
      simpa [pow_two] using Nat.mul_le_mul_left (den (n + 1)) hs
    have hsmall : den (n + 1) ^ 2 ≤
        den (n + 2) + (num (n + 1) + den (n + 1)) ^ 2 := by
      rw [hdm]
      exact le_add_of_le_left hsquare
    calc
      den (n + 2) * den (n + 1) ^ 2 ≤
          den (n + 2) * (den (n + 2) +
            (num (n + 1) + den (n + 1)) ^ 2) :=
        Nat.mul_le_mul_left _ hsmall
      _ = den (n + 2) ^ 2 + den (n + 2) *
          (num (n + 1) + den (n + 1)) ^ 2 := by ring
  constructor
  · rw [hdm]
    refine ⟨den (n + 1) * (num (n + 1) + den (n + 1)) ^ 3, ?_⟩
    ring
  · rw [hquot, hdn, hnm]
    symm
    apply (Nat.sub_eq_iff_eq_add' hle).2
    rw [hdm]
    ring

#print axioms num
#print axioms den
#print axioms b
#print axioms result

end D5.S1.Recurrence.Residue.QuetRationalIterationDenominator
