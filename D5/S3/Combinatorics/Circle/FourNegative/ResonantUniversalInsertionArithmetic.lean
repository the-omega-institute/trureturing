/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionArithmetic
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Parameterized arithmetic for multiplicative resonant insertion. -/
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import Mathlib.NumberTheory.PowModTotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth
open PeriodicShorteningArithmetic
open scoped BigOperators

/-! The arithmetic parameters of a resonant insertion.  The modulus is kept
integer-valued because the physical rows and all prefix states live in `ℤ`.-/

def resonanceQuotient (w m : ℕ) : ℕ := (m - 1) / w

def targetFirstHalf (k ell m : ℕ) : ℤ :=
  (m : ℤ) * (modulus k / 2 + 1) - 1

def targetSecondModulus (k ell m : ℕ) : ℤ :=
  2 * (targetFirstHalf k ell m) + 1

theorem resonance_quotient_mul {w m : ℕ} (hw : 0 < w) (hdiv : w ∣ m - 1) :
    w * resonanceQuotient w m = m - 1 := by
  exact Nat.mul_div_cancel' hdiv

theorem resonance_quotient_ge_three {w m : ℕ}
    (hw : 0 < w) (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) :
    3 ≤ resonanceQuotient w m := by
  have hmul := resonance_quotient_mul hw hdiv
  by_contra hq
  have hq2 : resonanceQuotient w m ≤ 2 := by omega
  have hmul_le : w * resonanceQuotient w m ≤ w * 2 :=
    Nat.mul_le_mul_left w hq2
  omega

private theorem two_pow_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      n + 1 + 1 ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

theorem odd_seed_has_resonant_period {w : ℕ} (hw : Odd w) :
    ∃ ell : ℕ, 1 ≤ ell ∧ w ∣ 2 ^ ell - 1 ∧ 3 * w + 1 ≤ 2 ^ ell := by
  by_cases hw1 : w = 1
  · subst w
    refine ⟨2, by decide, by simp, by decide⟩
  · have hwpos : 0 < w := by
      rcases hw with ⟨a, ha⟩
      omega
    let phi := Nat.totient w
    let t := 3 * w + 1
    let ell := phi * t
    have hphi : 0 < phi := Nat.totient_pos.mpr (by omega)
    have hcop : Nat.Coprime 2 w := hw.coprime_two_left
    have hmod : (2 ^ phi) % w = 1 :=
      Nat.pow_totient_mod_eq_one (by omega) hcop
    have hpmod : (2 ^ ell) % w = 1 := by
      dsimp [ell]
      rw [pow_mul, Nat.pow_mod, hmod]
      have hwmod : 1 % w = 1 := Nat.mod_eq_of_lt (by omega)
      simpa [hwmod]
    have hpone : 1 ≤ 2 ^ ell := Nat.one_le_two_pow
    have hsubmod : (2 ^ ell - 1) % w = 0 := by
      have hs := Nat.mod_sub_of_le (a := 2 ^ ell) (b := 1) (n := w)
        (by simpa [hpmod])
      rw [hpmod] at hs
      omega
    have hdiv : w ∣ 2 ^ ell - 1 := Nat.dvd_of_mod_eq_zero hsubmod
    have hlarge : 3 * w + 1 ≤ ell := by
      dsimp [ell, t]
      exact Nat.le_mul_of_pos_left t hphi
    refine ⟨ell, by omega, hdiv, ?_⟩
    exact le_trans (by omega) (two_pow_ge_succ ell)

theorem resonance_target_modulus {k ell m : ℕ} (hm : m = 2 ^ ell) :
    modulus (k + ell) = (m : ℤ) * (modulus k + 1) - 1 := by
  unfold modulus
  rw [pow_add, hm]
  norm_num
  ring

theorem shifted_source_row {w ell k m : ℕ} (hell : 1 ≤ ell)
    (hm : m = 2 ^ ell) (hw : 0 < w) (hdiv : w ∣ m - 1)
    (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hroomNew : w ≤ 2 ^ (k + ell - 1) - 1) (hdim : 2 ≤ k) (i : Fin k) :
    actualSource (k + ell) w ⟨i.val + ell, by omega⟩ =
      (m : ℤ) * actualSource k w i - (m - 1 : ℕ) * charge k w i := by
  have hdold := digit_data k w (by omega) hroom i
  have hdnew := digit_data (k + ell) w (by omega) hroomNew
      ⟨i.val + ell, by omega⟩
  have heqpow : (2 : ℤ) ^ (i.val + ell) =
      (m : ℤ) * (2 : ℤ) ^ i.val := by
    rw [pow_add, hm]
    norm_num
    simp [mul_comm]
  have heqdim : (2 : ℤ) ^ (k + ell) =
      (m : ℤ) * (2 : ℤ) ^ k := by
    rw [pow_add, hm]
    norm_num
    simp [mul_comm]
  have hcharge : charge (k + ell) w ⟨i.val + ell, by omega⟩ = charge k w i := by
    have he : k + ell - 1 - (i.val + ell) = k - 1 - i.val := by omega
    simp [charge, he]
  have hmpos : 0 < m := by rw [hm]; positivity
  have hmcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hdnew.2.1, hdold.2.1, heqpow, heqdim, hcharge, hmcast]
  ring

theorem shifted_charge_row {w ell k : ℕ} (j : Fin k) :
    charge (k + ell) w ⟨j.val + ell, by omega⟩ = charge k w j := by
  change (let z := (w : ℤ) / (2 : ℤ) ^ (k + ell - 1 - (j.val + ell));
      z / 2 + z % 2) =
    (let z := (w : ℤ) / (2 : ℤ) ^ (k - 1 - j.val); z / 2 + z % 2)
  simp only [show k + ell - 1 - (j.val + ell) = k - 1 - j.val by omega]

theorem canonical_second_relation (m w F Y C u b : ℤ)
    (hrel : Y = 2 * F - C + w * b) :
    m * Y - (m - 1) * C - w * (m - 1) * b + 2 * w * u =
      2 * (m * F - (m - 1) * C + w * u) - C + w * b := by
  rw [hrel]
  ring

theorem endpoint_shift_formula (m w q F Y C u b r : ℤ)
    (hq : w * q = m - 1)
    (hr : u + q * (F - C) = m * r)
    (hrel : Y = 2 * F - C + w * b) :
    m * F - (m - 1) * C + w * u = F + w * m * r ∧
      m * Y - (m - 1) * C - w * (m - 1) * b + 2 * w * u = Y + 2 * w * m * r := by
  constructor
  · calc
      m * F - (m - 1) * C + w * u =
          F + w * (u + q * (F - C)) := by
            have hmq : m = 1 + w * q := by omega
            rw [hmq]
            ring
      _ = F + w * m * r := by rw [hr]; ring
  · calc
      m * Y - (m - 1) * C - w * (m - 1) * b + 2 * w * u =
          2 * (m * F - (m - 1) * C + w * u) - C + w * b :=
            canonical_second_relation m w F Y C u b hrel
      _ = 2 * (F + w * m * r) - C + w * b := by
        rw [show m * F - (m - 1) * C + w * u = F + w * m * r from by
          calc
            m * F - (m - 1) * C + w * u = F + w * (u + q * (F - C)) := by
              have hmq : m = 1 + w * q := by omega
              rw [hmq]
              ring
            _ = F + w * m * r := by rw [hr]; ring]
      _ = Y + 2 * w * m * r := by rw [hrel]; ring

theorem resonant_hypotheses_facts {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hdiv : w ∣ m - 1)
    (hlarge : 3 * w + 1 ≤ m) (hk : ell ≤ k) :
    2 ≤ ell ∧ 2 ≤ k ∧ 0 < w ∧ Odd w ∧ w ≤ 2 ^ (k - 1) - 1 := by
  have hwpos : 0 < w := hw
  have hm2 : 4 ≤ m := by
    rw [hm]
    have hpow : 2 ^ 1 ≤ 2 ^ ell := Nat.pow_le_pow_right (by decide) hell
    have hpow' : 2 ^ 1 < 3 * w + 1 := by omega
    omega
  have hell2 : 2 ≤ ell := by
    by_contra h
    have : ell = 1 := by omega
    subst ell
    norm_num [hm] at hm2
  have hk2 : 2 ≤ k := by
    have hp : 2 ^ ell ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  have hoddm : Odd (m - 1) := by
    rw [hm]
    have hpow : 2 ^ ell = 2 * 2 ^ (ell - 1) := by
      calc
        2 ^ ell = 2 ^ ((ell - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (ell - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (ell - 1) := by omega
    refine ⟨2 ^ (ell - 1) - 1, ?_⟩
    omega
  have hoddw : Odd w := Odd.of_dvd_nat hoddm hdiv
  have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by omega
  have hwroom : w ≤ 2 ^ (k - 1) - 1 := by
    have hpell : 3 * w + 1 ≤ 2 ^ ell := by simpa [hm] using hlarge
    have hp : 3 * w + 1 ≤ 2 ^ k :=
      le_trans hpell (Nat.pow_le_pow_right (by decide) hk)
    rw [hpowk] at hp
    have hB : 0 < 2 ^ (k - 1) := by positivity
    by_contra hn
    have : 2 ^ (k - 1) ≤ w := by omega
    omega
  exact ⟨hell2, hk2, hwpos, hoddw, hwroom⟩

theorem resonant_old_modulus_odd {k : ℕ} (hk : 2 ≤ k) :
    Odd (2 ^ k - 1) := by
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by omega
  refine ⟨2 ^ (k - 1) - 1, ?_⟩
  calc
    2 ^ k - 1 = 2 * 2 ^ (k - 1) - 1 := by rw [hpow]
    _ = 2 * (2 ^ (k - 1) - 1) + 1 := by
      have hB : 0 < 2 ^ (k - 1) := by positivity
      omega

theorem resonant_low_source_row {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (i : Fin ell) :
    actualSource (k + ell) w ⟨i.val, by omega⟩ = (w : ℤ) * 2 ^ i.val ∧
      charge (k + ell) w ⟨i.val, by omega⟩ = 0 := by
  have hroom' : w ≤ 2 ^ ((k + ell) - 1) - 1 := by
    have hp : 2 ^ (k - 1) ≤ 2 ^ ((k + ell) - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h := digit_data (k + ell) w (by omega) hroom'
      ⟨i.val, by omega⟩
  have hi : i.val ≤ ell - 1 := by omega
  have hexp : k + ell - 1 - i.val ≥ k := by omega
  have hpow : (w : ℤ) < 2 ^ (k + ell - 1 - i.val) := by
    have hp : (2 : ℕ) ^ (k - 1) ≤ 2 ^ (k + ell - 1 - i.val) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hB : 0 < 2 ^ (k - 1) := by positivity
    have hwlt : w < 2 ^ (k - 1) := by omega
    have hpz : (2 : ℤ) ^ (k - 1) ≤ (2 : ℤ) ^ (k + ell - 1 - i.val) := by
      exact_mod_cast hp
    exact lt_of_lt_of_le (by exact_mod_cast hwlt) hpz
  have hz : (w : ℤ) / 2 ^ (k + ell - 1 - i.val) = 0 :=
    Int.ediv_eq_zero_of_lt (by positivity) hpow
  have hc : charge (k + ell) w ⟨i.val, by omega⟩ = 0 := by
    simp [charge, hz]
  rw [hc] at h
  refine ⟨?_, hc⟩
  rw [h.2.1]
  ring

theorem resonant_low_second_row {w ell k : ℕ}
    (hell : 1 ≤ ell) (hroom : w ≤ 2 ^ (k - 1) - 1) (hk : 2 ≤ k)
    (i : Fin ell) :
    actualSource (k + ell + 1) (2 * w) ⟨i.val, by omega⟩ =
      (2 * w : ℤ) * 2 ^ i.val := by
  have hroom' : 2 * w ≤ 2 ^ ((k + ell + 1) - 1) - 1 := by
    have hp : 2 ^ k ≤ 2 ^ ((k + ell + 1) - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hw : w ≤ 2 ^ (k - 1) - 1 := hroom
    have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (k - 1) := by omega
    omega
  have h := digit_data (k + ell + 1) (2 * w) (by omega) hroom'
      ⟨i.val, by omega⟩
  have hi : i.val ≤ ell - 1 := by omega
  have hexp : k + ell + 1 - 1 - i.val ≥ k := by omega
  have hpow : (2 * w : ℤ) < 2 ^ ((k + ell + 1) - 1 - i.val) := by
    have hp : (2 : ℕ) ^ k ≤ 2 ^ ((k + ell + 1) - 1 - i.val) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hw : 2 * w < 2 ^ k := by
      have : 2 * w ≤ 2 * (2 ^ (k - 1) - 1) := Nat.mul_le_mul_left 2 hroom
      have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        calc
          2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
          _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k - 1) := by omega
      have hB : 0 < 2 ^ (k - 1) := by positivity
      omega
    have hp' : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ ((k + ell + 1) - 1 - i.val) := by
      exact_mod_cast hp
    exact lt_of_lt_of_le (by exact_mod_cast hw) hp'
  have hz : (2 * w : ℤ) / 2 ^ ((k + ell + 1) - 1 - i.val) = 0 :=
    Int.ediv_eq_zero_of_lt (by positivity) hpow
  have hc : charge (k + ell + 1) (2 * w) ⟨i.val, by omega⟩ = 0 := by
    dsimp [charge]
    have hz' : (2 * w : ℤ) / 2 ^ (k + ell - i.val) = 0 := by simpa using hz
    change ((2 * w : ℤ) / 2 ^ (k + ell - i.val)) / 2 +
      ((2 * w : ℤ) / 2 ^ (k + ell - i.val)) % 2 = 0
    rw [hz']
    norm_num
  rw [hc] at h
  rw [h.2.1]
  norm_num [Nat.cast_mul]
  ring

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
