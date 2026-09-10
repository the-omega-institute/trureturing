/- GID: D5/S1/Recurrence/Parity/DiagonalIterateEven
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/DiagonalIterateEven
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Diagonal iteration determines an integer series with even diagonal coefficients. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (iterate)

namespace D5.S1.Recurrence.Parity.DiagonalIterateEven
variable {R : Type*} [CommRing R]

-- The coefficient perturbation argument follows the private helpers in
-- IterateProductNineModThree; that module exposes no public perturbation API.
private def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ k < n, coeff k f = coeff k g

private theorem agree_iff (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {f g : PowerSeries R}
    (h : Agree n f g) (k : ℕ) : Agree n (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp h |>.trans
    (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {f : PowerSeries R} (hf : constantCoeff f = 0)
    {n k : ℕ} (h : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) n h

private theorem agree_mul {n : ℕ} {f g u v : PowerSeries R}
    (hf : constantCoeff f = 0) (hv : constantCoeff v = 0)
    (hfg : Agree n f g) (huv : Agree n u v) :
    Agree (n + 1) (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have h1 := mul_dvd_mul (X_dvd_iff.mpr hf) ((agree_iff _ _ _).mp huv)
  have h2 := mul_dvd_mul ((agree_iff _ _ _).mp hfg) (X_dvd_iff.mpr hv)
  rw [mul_comm X, ← pow_succ] at h1
  rw [← pow_succ] at h2
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_subst {n : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hfg : Agree n f g) (huv : Agree n u v) :
    Agree n (f.subst u) (g.subst v) := by
  intro k hk
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro e
  by_cases he : e < n
  · rw [hfg e he, agree_pow huv e k hk]
  · rw [pow_low hu (by omega : k < e), pow_low hv (by omega : k < e),
      smul_zero, smul_zero]

private theorem subst_coeff (f u : PowerSeries R) (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (f.subst u) = ∑ k ∈ Finset.range (n + 1), coeff k f * coeff n (u ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero hu)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  exact hk (by dsimp; rw [pow_low hu (by omega), mul_zero])

private theorem leading_pow {u : PowerSeries R} (hu : constantCoeff u = 0)
    (hu1 : coeff 1 u = 1) (n : ℕ) : coeff n (u ^ n) = 1 := by
  obtain ⟨v, rfl⟩ := X_dvd_iff.mpr hu
  have hv : constantCoeff v = 1 := by simpa using hu1
  simp [mul_pow, coeff_X_pow_mul', hv]

private theorem pow_top {n : ℕ} {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree n u v) (k : ℕ) : coeff n (u ^ (k + 2)) = coeff n (v ^ (k + 2)) := by
  have hh := agree_mul hu (show constantCoeff (v ^ (k + 1)) = 0 by simp [hv])
    h (agree_pow h (k + 1)) n (by omega)
  simpa only [← pow_succ'] using hh

private theorem subst_outer_top {n : ℕ} {f g u : PowerSeries R}
    (hu : constantCoeff u = 0) (hu1 : coeff 1 u = 1) (h : Agree n f g) :
    coeff n (f.subst u) - coeff n (g.subst u) = coeff n f - coeff n g := by
  rw [subst_coeff f u hu, subst_coeff g u hu, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single n]
  · rw [leading_pow hu hu1, mul_one, mul_one]
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    rw [h k hk', sub_self]
  · simp

private theorem subst_inner_top {n : ℕ} {u v : PowerSeries R} (f : PowerSeries R)
    (hn : 1 < n) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree n u v) :
    coeff n (f.subst u) - coeff n (f.subst v) =
      coeff 1 f * (coeff n u - coeff n v) := by
  rw [subst_coeff f u hu, subst_coeff f v hv, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single 1]
  · simp only [pow_one, mul_sub]
  · intro k hk hk1
    rcases k with _ | _ | k
    · simp
    · exact (hk1 rfl).elim
    · rw [pow_top hu hv h k, sub_self]
  · simp [show 1 < n + 1 by omega]

private theorem subst_top {n : ℕ} {f g u v : PowerSeries R}
    (hn : 1 < n) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hu1 : coeff 1 u = 1) (hg1 : coeff 1 g = 1)
    (hfg : Agree n f g) (huv : Agree n u v) :
    coeff n (f.subst u) - coeff n (g.subst v) =
      (coeff n f - coeff n g) + (coeff n u - coeff n v) := by
  have h1 := subst_outer_top hu hu1 hfg
  have h2 := subst_inner_top g hn hu hv huv
  rw [hg1, one_mul] at h2
  linear_combination h1 + h2

private theorem iterate_normal {f : PowerSeries R} (hf : constantCoeff f = 0)
    (hf1 : coeff 1 f = 1) (j : ℕ) :
    constantCoeff (iterate f j) = 0 ∧ coeff 1 (iterate f j) = 1 := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    refine ⟨constantCoeff_subst_eq_zero hf _ ih.1, ?_⟩
    rw [iterate, subst_coeff _ _ hf]
    simp [Finset.sum_range_succ, hf1, ih.2]

private theorem iterate_agree {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree n f g) (j : ℕ) : Agree n (iterate f j) (iterate g j) := by
  induction j with
  | zero => intro k hk; rfl
  | succ j ih => exact agree_subst hf hg ih h

private theorem iterate_top {n : ℕ} {f g : PowerSeries R}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (h : Agree n f g) (j : ℕ) :
    coeff n (iterate f j) - coeff n (iterate g j) =
      (j : R) * (coeff n f - coeff n g) := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    rw [iterate, iterate, subst_top hn hf hg hf1 (iterate_normal hg hg1 j).2
      (iterate_agree hf hg h j) h, ih]
    push_cast
    ring


private noncomputable def residual (f : PowerSeries R) (n : ℕ) : R :=
  coeff n (iterate f n) - coeff n (iterate f (n - 1))

private theorem residual_top {n : ℕ} {f g : PowerSeries R}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1) (h : Agree n f g) :
    residual f n - residual g n = coeff n f - coeff n g := by
  have hnext := iterate_top hn hf hg hf1 hg1 h n
  have hprev := iterate_top hn hf hg hf1 hg1 h (n - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hprev
  dsimp only [residual]
  linear_combination hnext - hprev

private theorem diagonal_unique {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (hf2 : coeff 2 f = 1) (hg2 : coeff 2 g = 1)
    (hfe : ∀ n, 2 < n → residual f n = 0)
    (hge : ∀ n, 2 < n → residual g n = 0) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; simpa only [coeff_zero_eq_constantCoeff, hf, hg]
    by_cases hn1 : n = 1
    · subst n; exact hf1.trans hg1.symm
    by_cases hn2 : n = 2
    · subst n; exact hf2.trans hg2.symm
    have ht := residual_top (by omega : 1 < n) hf hg hf1 hg1 ih
    rw [hfe n (by omega), hge n (by omega), sub_self] at ht
    exact sub_eq_zero.mp ht.symm

#print axioms diagonal_unique
end D5.S1.Recurrence.Parity.DiagonalIterateEven
