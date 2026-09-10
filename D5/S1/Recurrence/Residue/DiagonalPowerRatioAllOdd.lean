/- GID: D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Diagonal coefficient cancellation and Lucas parity prove Hanna's A397241 conjecture. -/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.LinearCombination

open PowerSeries

namespace D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd

variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (A B : PowerSeries R) : Prop :=
  ∀ k < n, coeff k A = coeff k B

private theorem agree_iff (n : ℕ) (A B : PowerSeries R) :
    Agree n A B ↔ (X : PowerSeries R) ^ n ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {A B : PowerSeries R}
    (h : Agree n A B) (m : ℕ) : Agree n (A ^ m) (B ^ m) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow A B m))

private theorem leading_mul {n : ℕ} {U : PowerSeries R}
    (h : X ^ n ∣ U) (V : PowerSeries R) :
    coeff n (U * V) = coeff n U * constantCoeff V := by
  obtain ⟨W, rfl⟩ := h
  rw [mul_assoc]
  have hc (T : PowerSeries R) : coeff n (X ^ n * T) = constantCoeff T := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul T n 0
  rw [hc, hc, map_mul]

-- The first coefficient where two unit series differ enters the m-th power with multiplier m.
private theorem diagonal_multiplier {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (m : ℕ) :
    coeff n (A ^ m) - coeff n (B ^ m) =
      (m : R) * (coeff n A - coeff n B) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow := (agree_iff _ _ _).mp (agree_pow h m)
    have hd := (agree_iff _ _ _).mp h
    have he : A ^ (m + 1) - B ^ (m + 1) =
        (A ^ m - B ^ m) * A + (A - B) * B ^ m := by ring
    rw [← map_sub, he, map_add, leading_mul hpow, leading_mul hd]
    simp only [map_sub, map_pow, hA, hB, one_pow, mul_one, ih, Nat.cast_add,
      Nat.cast_one]
    ring

private noncomputable def residual (A : PowerSeries R) (n : ℕ) : R :=
  (n : R) * coeff n (A ^ n) - ((n : R) - 1) * coeff n (A ^ (n + 1))

private theorem residual_difference {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) :
    residual A n - residual B n = coeff n A - coeff n B := by
  have hn := diagonal_multiplier hA hB h n
  have hs := diagonal_multiplier hA hB h (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hs
  dsimp [residual]
  linear_combination (n : R) * hn - ((n : R) - 1) * hs

private noncomputable def step (A : PowerSeries R) : PowerSeries R :=
  mk fun n => if n ≤ 1 then 1 else coeff n A - residual A n

private theorem step_zero (A : PowerSeries R) : constantCoeff (step A) = 1 := by
  simp [step]

private theorem step_contract {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree (n + 1) (step A) (step B) := by
  intro k hk
  simp only [step, coeff_mk]
  split_ifs with hk1
  · rfl
  · have hd := residual_difference hA hB (n := k) (fun j hj => h j (by omega))
    linear_combination -hd

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | d + 1 => step (approximation d)

private theorem approximation_zero (d : ℕ) :
    constantCoeff (approximation (R := R) d) = 1 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero _

private theorem approximation_stable {d s : ℕ} (h : d ≤ s) :
    Agree d (approximation (R := R) d) (approximation s) := by
  induction d generalizing s with
  | zero => intro k hk; omega
  | succ d ih =>
    cases s with
    | zero => omega
    | succ s =>
      exact step_contract (approximation_zero d) (approximation_zero s) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) :
    Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  have h0 : constantCoeff generatingSeries = 1 := by
    simpa only [coeff_zero_eq_constantCoeff] using
      (generating_agree 1 0 (by omega)).trans (by
        simpa only [coeff_zero_eq_constantCoeff] using approximation_zero (R := ℤ) 1)
  ext n
  exact (generating_agree (n + 2) n (by omega)).trans
    (step_contract h0 (approximation_zero (n + 1))
      (generating_agree (n + 1)) n (by omega)).symm

theorem generating_equation : coeff 0 generatingSeries = 1 ∧
    coeff 1 generatingSeries = 1 ∧ ∀ n : ℕ, 1 < n →
      (n : ℤ) * coeff n (generatingSeries ^ n) =
        ((n : ℤ) - 1) * coeff n (generatingSeries ^ (n + 1)) := by
  have hf (n : ℕ) := congrArg (coeff n) generating_fixed
  refine ⟨?_, ?_, ?_⟩
  · simpa [step] using hf 0
  · simpa [step] using hf 1
  · intro n hn
    have h := hf n
    simp only [step, coeff_mk, if_neg (by omega : ¬ n ≤ 1), residual] at h
    linear_combination h

private theorem equation_unique {A B : PowerSeries R}
    (hA0 : coeff 0 A = 1) (hB0 : coeff 0 B = 1)
    (hA1 : coeff 1 A = 1) (hB1 : coeff 1 B = 1)
    (hA : ∀ n : ℕ, 1 < n → residual A n = 0)
    (hB : ∀ n : ℕ, 1 < n → residual B n = 0) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; exact hA0.trans hB0.symm
    by_cases hn1 : n = 1
    · subst n; exact hA1.trans hB1.symm
    have hd := residual_difference
      (by simpa only [coeff_zero_eq_constantCoeff] using hA0)
      (by simpa only [coeff_zero_eq_constantCoeff] using hB0) ih
    rw [hA n (by omega), hB n (by omega), sub_self] at hd
    exact sub_eq_zero.mp hd.symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (h1 : coeff 1 B = 1)
    (he : ∀ n : ℕ, 1 < n → (n : ℤ) * coeff n (B ^ n) =
      ((n : ℤ) - 1) * coeff n (B ^ (n + 1))) : B = generatingSeries := by
  exact equation_unique h0 generating_equation.1 h1 generating_equation.2.1
    (fun n hn => sub_eq_zero.mpr (he n hn))
    (fun n hn => sub_eq_zero.mpr (generating_equation.2.2 n hn))

theorem central_binom_even (m : ℕ) (hm : 0 < m) : 2 ∣ (2 * m).choose m :=
  Nat.two_dvd_centralBinom_of_one_le hm

private theorem odd_diagonal_even (m : ℕ) (hm : 0 < m) :
    2 ∣ (4 * m + 1).choose (2 * m) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := 4 * m + 1) (k := 2 * m) (p := 2)
  have hd : (4 * m + 1) / 2 = 2 * m := by omega
  have hc : (2 * m).choose m % 2 = 0 := Nat.mod_eq_zero_of_dvd (central_binom_even m hm)
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod, hd, hc] using h

private theorem geometric_residual (n : ℕ) (hn : 1 < n) :
    residual (mk 1 : PowerSeries (ZMod 2)) n = 0 := by
  have hs : coeff n ((mk 1 : PowerSeries (ZMod 2)) ^ (n + 1)) = 0 := by
    rw [mk_one_pow_eq_mk_choose_add, coeff_mk, ← two_mul]
    exact (ZMod.natCast_eq_zero_iff_even).mpr
      (even_iff_two_dvd.mpr (central_binom_even n (by omega)))
  rw [residual, hs, mul_zero, sub_zero]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.natCast_zmod_two, zero_mul]
  · obtain ⟨m, rfl⟩ := ho
    have hc : coeff (2 * m + 1)
        ((mk 1 : PowerSeries (ZMod 2)) ^ (2 * m + 1)) = 0 := by
      rw [mk_one_pow_eq_mk_choose_add, coeff_mk]
      have hindex : 2 * m + (2 * m + 1) = 4 * m + 1 := by omega
      rw [hindex]
      exact (ZMod.natCast_eq_zero_iff_even).mpr
        (even_iff_two_dvd.mpr (odd_diagonal_even m (by omega)))
    rw [hc, mul_zero]

theorem mod_two_identity :
    generatingSeries.map (Int.castRingHom (ZMod 2)) = mk 1 := by
  let hom := Int.castRingHom (ZMod 2)
  have hm (n : ℕ) : residual (generatingSeries.map hom) n =
      hom (residual generatingSeries n) := by
    simp [residual, ← map_pow, coeff_map]
  apply equation_unique (A := generatingSeries.map hom) (B := mk 1)
  · simp [coeff_map, generating_equation.1, hom]
  · simp
  · simp [coeff_map, generating_equation.2.1, hom]
  · simp
  · intro n hn
    rw [hm, show residual generatingSeries n = 0 from
      sub_eq_zero.mpr (generating_equation.2.2 n hn), map_zero]
  · exact geometric_residual

theorem hanna_conjecture (n : ℕ) : Odd (a n) := by
  apply ZMod.intCast_eq_one_iff_odd.mp
  have h := congrArg (coeff n) mod_two_identity
  simpa [coeff_map, generatingSeries] using h

#print axioms generating_equation
#print axioms generating_unique
#print axioms central_binom_even
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.DiagonalPowerRatioAllOdd
