import D5.S3.Arith.ArtinSchreierTracePowersOfTwo
set_option autoImplicit false
open scoped PowerSeries
open Finset
namespace A396808Sparse
noncomputable section
abbrev F3 := ZMod 3
abbrev PS := F3⟦X⟧

def t : PS := by
  classical
  exact PowerSeries.mk fun n => if ∃ r : ℕ, n = 3 ^ r then 1 else 0

private theorem power_mul_iff (n : ℕ) :
    (∃ r : ℕ, 3*n = (3:ℕ)^r) ↔ ∃ r : ℕ, n = (3:ℕ)^r := by
  constructor
  · rintro ⟨r, hr⟩
    cases r with
    | zero => simp at hr
    | succ r => exact ⟨r, by simp only [pow_succ] at hr; omega⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r+1, by simp [pow_succ, Nat.mul_comm]⟩

private theorem power_not_dvd {n : ℕ} (hn : ¬3 ∣ n) :
    (∃ r : ℕ, n=(3:ℕ)^r) ↔ n=1 := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r with
    | zero => rfl
    | succ r => simp [pow_succ] at hn
  · rintro rfl
    exact ⟨0,rfl⟩

private theorem t_expand : PowerSeries.expand 3 (by decide) t = t - PowerSeries.X := by
  classical
  ext n
  rw [PowerSeries.coeff_expand, map_sub, PowerSeries.coeff_X]
  simp only [t, PowerSeries.coeff_mk]
  by_cases h : 3 ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [if_pos (by simp), Nat.mul_div_cancel_left _ (by decide), power_mul_iff,
      if_neg (show ¬3*k=1 by omega)]
    simp
  · rw [if_neg h, power_not_dvd h]
    split_ifs <;> simp

private theorem cube_eq_expand (f : PS) : f^3 = PowerSeries.expand 3 (by decide) f := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) 3 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

private theorem t_cube : t^3 = t - PowerSeries.X := by
  rw [cube_eq_expand, t_expand]

private theorem t_zero : PowerSeries.constantCoeff t = 0 := by
  classical
  simp only [t, PowerSeries.constantCoeff_mk]
  apply if_neg
  rintro ⟨r, hr⟩
  have : 0 < (3:ℕ)^r := pow_pos (by decide) _
  omega

private theorem power_pair_unique (i j k l : ℕ) (hij : i ≤ j) (hkl : k ≤ l)
    (heq : (3:ℕ)^i + (3:ℕ)^j = (3:ℕ)^k + (3:ℕ)^l) : i=k ∧ j=l := by
  have high : ∀ a b c d : ℕ, a ≤ b → b < d → (3:ℕ)^a + (3:ℕ)^b < (3:ℕ)^c + (3:ℕ)^d := by
    intro a b c d hab hbd
    have ha : (3:ℕ)^a ≤ (3:ℕ)^b := Nat.pow_le_pow_right (by decide) hab
    have hd : (3:ℕ)^(b+1) ≤ (3:ℕ)^d := Nat.pow_le_pow_right (by decide) hbd
    have hp : 0 < (3:ℕ)^b := pow_pos (by decide) _
    rw [pow_succ] at hd
    calc
      (3:ℕ)^a + (3:ℕ)^b ≤ 2*(3:ℕ)^b := by omega
      _ < (3:ℕ)^b*3 := by omega
      _ ≤ (3:ℕ)^d := hd
      _ ≤ (3:ℕ)^c + (3:ℕ)^d := Nat.le_add_left _ _
  have hjl : j=l := by
    rcases lt_trichotomy j l with h | h | h
    · have := high i j k l hij h; omega
    · exact h
    · have := high k l i j hkl h; omega
  subst l
  constructor
  · apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    exact Nat.add_right_cancel heq
  · rfl

#print axioms t_cube
#print axioms power_pair_unique
end
end A396808Sparse
