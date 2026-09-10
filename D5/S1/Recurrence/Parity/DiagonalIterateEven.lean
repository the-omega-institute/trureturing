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
    · subst n; simp only [coeff_zero_eq_constantCoeff, hf, hg]
    by_cases hn1 : n = 1
    · subst n; exact hf1.trans hg1.symm
    by_cases hn2 : n = 2
    · subst n; exact hf2.trans hg2.symm
    have ht := residual_top (by omega : 1 < n) hf hg hf1 hg1 ih
    rw [hfe n (by omega), hge n (by omega), sub_self] at ht
    exact sub_eq_zero.mp ht.symm

private noncomputable def extend (n : ℕ) (f : PowerSeries R) : PowerSeries R :=
  f - C (residual f n) * X ^ n

private theorem extend_agree (n : ℕ) (f : PowerSeries R) : Agree n (extend n f) f := by
  intro k hk
  simp only [extend, map_sub, coeff_C_mul_X_pow, if_neg (show k ≠ n by omega), sub_zero]

private theorem residual_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree d f g)
    (n : ℕ) (hn : n < d) : residual f n = residual g n := by
  rw [residual, residual, iterate_agree hf hg h n n hn,
    iterate_agree hf hg h (n - 1) n hn]

private theorem extend_normal {n : ℕ} {f : PowerSeries R} (hn : 2 < n)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hf2 : coeff 2 f = 1) :
    constantCoeff (extend n f) = 0 ∧ coeff 1 (extend n f) = 1 ∧
      coeff 2 (extend n f) = 1 := by
  refine ⟨?_, (extend_agree n f 1 (by omega)).trans hf1,
    (extend_agree n f 2 hn).trans hf2⟩
  simpa only [coeff_zero_eq_constantCoeff, hf] using extend_agree n f 0 (by omega)

private theorem extend_correct {n : ℕ} {f : PowerSeries R} (hn : 2 < n)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hf2 : coeff 2 f = 1) :
    residual (extend n f) n = 0 := by
  have hz := extend_normal hn hf hf1 hf2
  have ht := residual_top (by omega : 1 < n) hz.1 hf hz.2.1 hf1 (extend_agree n f)
  simp only [extend, map_sub, coeff_C_mul_X_pow, ↓reduceIte] at ht
  dsimp only [extend]
  linear_combination ht

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => X + X ^ 2
  | j + 1 => extend (j + 3) (approximation j)

private theorem approximation_normal (j : ℕ) :
    constantCoeff (approximation (R := R) j) = 0 ∧
    coeff 1 (approximation (R := R) j) = 1 ∧ coeff 2 (approximation (R := R) j) = 1 := by
  induction j with
  | zero => simp [approximation, coeff_X, coeff_X_pow]
  | succ j ih => exact extend_normal (by omega) ih.1 ih.2.1 ih.2.2

private theorem approximation_correct (j n : ℕ) (hn : 2 < n) (hj : n < j + 3) :
    residual (approximation (R := R) j) n = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hnj : n < j + 3
    · exact (residual_agree (approximation_normal (j + 1)).1
        (approximation_normal j).1 (extend_agree (j + 3) (approximation j)) n hnj).trans
        (ih hnj)
    · have he : n = j + 3 := by omega
      subst n
      exact extend_correct (by omega) (approximation_normal j).1
        (approximation_normal j).2.1 (approximation_normal j).2.2

private theorem approximation_stable {j k : ℕ} (hjk : j ≤ k) :
    Agree (j + 3) (approximation (R := R) k) (approximation j) := by
  induction k, hjk using Nat.le_induction with
  | base => intro i hi; rfl
  | succ k hk ih =>
    intro i hi
    exact (extend_agree (k + 3) (approximation k) i (by omega)).trans (ih i hi)

private noncomputable def limitSeries : PowerSeries R :=
  mk fun n => coeff n (approximation n)

private theorem limit_agree (j : ℕ) : Agree (j + 3) (limitSeries (R := R)) (approximation j) := by
  intro n hn
  simp only [limitSeries, coeff_mk]
  by_cases hnj : n ≤ j
  · exact (approximation_stable hnj n (by omega)).symm
  · exact approximation_stable (by omega : j ≤ n) n hn

private theorem limit_spec : constantCoeff (limitSeries (R := R)) = 0 ∧
    coeff 1 (limitSeries (R := R)) = 1 ∧ coeff 2 (limitSeries (R := R)) = 1 ∧
    ∀ n, 2 < n → residual (limitSeries (R := R)) n = 0 := by
  have hz : constantCoeff (limitSeries (R := R)) = 0 := by
    simpa only [coeff_zero_eq_constantCoeff, (approximation_normal 0).1] using
      limit_agree (R := R) 0 0 (by omega)
  refine ⟨hz, (limit_agree 0 1 (by omega)).trans (approximation_normal 0).2.1,
    (limit_agree 0 2 (by omega)).trans (approximation_normal 0).2.2, ?_⟩
  intro n hn
  exact (residual_agree hz (approximation_normal n).1 (limit_agree n) n (by omega)).trans
    (approximation_correct n n hn (by omega))

noncomputable def generatingSeries : PowerSeries ℤ := limitSeries

noncomputable def a (n : ℕ) : ℤ := coeff n (iterate generatingSeries n)

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧ coeff 2 generatingSeries = 1 ∧
    ∀ n, 2 < n → coeff n (iterate generatingSeries n) =
      coeff n (iterate generatingSeries (n - 1)) := by
  exact ⟨limit_spec.1, limit_spec.2.1, limit_spec.2.2.1,
    fun n hn => sub_eq_zero.mp (limit_spec.2.2.2 n hn)⟩

theorem generating_unique (f : PowerSeries ℤ)
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hf2 : coeff 2 f = 1)
    (he : ∀ n, 2 < n → coeff n (iterate f n) = coeff n (iterate f (n - 1))) :
    f = generatingSeries :=
  diagonal_unique hf limit_spec.1 hf1 limit_spec.2.1 hf2 limit_spec.2.2.1
    (fun n hn => sub_eq_zero.mpr (he n hn)) limit_spec.2.2.2

-- The brief's initial value 4 is inconsistent with g₁=g₂=1; the value is 2.
private theorem initial_echo : a 2 = 2 := by
  have hg := generating_equation
  have hx : iterate generatingSeries 1 = generatingSeries := by
    simp [iterate, subst_X (.of_constantCoeff_zero hg.1)]
  rw [a, iterate, hx, subst_coeff _ _ hg.1]
  simp [Finset.sum_range_succ, hg.2.1, hg.2.2.1, leading_pow hg.1 hg.2.1]

private noncomputable def quadratic : PowerSeries (ZMod 2) := X + X ^ 2

private instance : CharP (PowerSeries (ZMod 2)) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))

private theorem quadratic_unit : IsUnit (coeff 1 quadratic) := by
  simp [quadratic, coeff_X_pow]

private noncomputable def H : PowerSeries (ZMod 2) :=
  quadratic.substInvOfIsUnit quadratic_unit

private theorem H_zero : constantCoeff H = 0 := constantCoeff_substInvOfIsUnit _ _

private theorem H_quadratic : H + H ^ 2 = X := by
  have he := subst_substInvOfIsUnit_right quadratic (by simp [quadratic]) quadratic_unit
  change quadratic.subst H = X at he
  simpa only [quadratic, subst_add (.of_constantCoeff_zero H_zero),
    subst_pow (.of_constantCoeff_zero H_zero), subst_X (.of_constantCoeff_zero H_zero)] using he

private theorem H_one : coeff 1 H = 1 := by
  have hc := congrArg (coeff 1) H_quadratic
  simpa only [map_add, pow_low H_zero (by omega : 1 < 2), add_zero, coeff_one_X] using hc

private theorem H_two : coeff 2 H = 1 := by
  have hc := congrArg (coeff 2) H_quadratic
  simp only [map_add, leading_pow H_zero H_one, coeff_X, show (2 : ℕ) ≠ 1 by omega,
    if_false] at hc
  have hz : (2 : ZMod 2) = 0 := by decide
  linear_combination hc - hz

private theorem iterate_add {f : PowerSeries R}
    (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (j k : ℕ) :
    iterate f (j + k) = (iterate f j).subst (iterate f k) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    change (iterate f (j + k)).subst f = (iterate f j).subst ((iterate f k).subst f)
    rw [ih]
    exact subst_comp_subst_apply (.of_constantCoeff_zero (iterate_normal hf hf1 k).1)
      (.of_constantCoeff_zero hf) (iterate f j)

private theorem H_recurrence (m : ℕ) :
    iterate H (m + 1) + iterate H (m + 1) ^ 2 = iterate H m := by
  induction m with
  | zero => simpa [iterate, subst_X (.of_constantCoeff_zero H_zero)] using H_quadratic
  | succ m ih =>
    change (iterate H (m + 1)).subst H + ((iterate H (m + 1)).subst H) ^ 2 =
      (iterate H m).subst H
    simpa only [subst_add (.of_constantCoeff_zero H_zero),
      subst_pow (.of_constantCoeff_zero H_zero)] using
      congrArg (subst H) ih

private theorem double_gap (u : PowerSeries (ZMod 2)) (hu : constantCoeff u = 0)
    (q : ℕ) (he : u + u ^ (2 ^ q) = X) :
    u.subst u + (u.subst u) ^ (2 ^ (q + q)) = X := by
  have hv : u.subst u + (u.subst u) ^ (2 ^ q) = u := by
    simpa only [subst_add (.of_constantCoeff_zero hu), subst_pow (.of_constantCoeff_zero hu),
      subst_X (.of_constantCoeff_zero hu)] using congrArg (subst u) he
  have hw := congrArg (fun v : PowerSeries (ZMod 2) => v ^ (2 ^ q)) hv
  rw [add_pow_char_pow _ _ 2 q, ← pow_mul, ← pow_add] at hw
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
  linear_combination hv + hw + he - (u.subst u) ^ (2 ^ q) * htwo

-- Successive doubling opens a degree gap far beyond the iteration index.
private theorem H_dyadic_gap (r : ℕ) :
    iterate H (2 ^ r) + iterate H (2 ^ r) ^ (2 ^ (2 ^ r)) = X := by
  induction r with
  | zero => simpa [iterate, subst_X (.of_constantCoeff_zero H_zero)] using H_quadratic
  | succ r ih =>
    have hd := double_gap (iterate H (2 ^ r)) (iterate_normal H_zero H_one _).1 (2 ^ r) ih
    rw [← iterate_add H_zero H_one] at hd
    simpa only [pow_succ, Nat.mul_two] using hd

private theorem H_dyadic_coeff (r n : ℕ) (hn : n < 2 ^ (2 ^ r)) :
    coeff n (iterate H (2 ^ r)) = coeff n (X : PowerSeries (ZMod 2)) := by
  have hc := congrArg (coeff n) (H_dyadic_gap r)
  simpa only [map_add, pow_low (iterate_normal H_zero H_one _).1 hn, add_zero] using hc

#print axioms H_dyadic_gap
#print axioms generating_equation
#print axioms generating_unique
#print axioms initial_echo
end D5.S1.Recurrence.Parity.DiagonalIterateEven
