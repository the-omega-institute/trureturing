/- GID: D5/S3/Fourier/Concentration/CyclicGridMomentGap
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicGridMomentGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound separation of phase supports by the real projection variance. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.Fourier.Concentration.CyclicMomentStability

set_option autoImplicit false

open Finset

namespace D5.S3.Fourier.Concentration.CyclicGridMomentGap

open CyclicMomentStability

private theorem sign_pair_squared_error {J : Type*} [Fintype J]
    (w e : J → ℝ) (P : J → Prop) [DecidablePred P]
    (hw : ∀ j, 0 ≤ w j)
    (hmass : ∑ j, w j = 1) {L : ℝ}
    (hpair : ∀ i j, P i → ¬ P j → 0 < w i → 0 < w j →
      L ≤ (e i + e j) ^ 2) :
    (∑ i with P i, w i) * (∑ j with ¬ P j, w j) * L ≤
      ∑ j, w j * (e j) ^ 2 := by
  let plus := univ.filter P
  let minus := univ.filter (fun j => ¬ P j)
  let a := ∑ i ∈ plus, w i
  let b := ∑ j ∈ minus, w j
  let A := ∑ i ∈ plus, w i * (e i) ^ 2
  let B := ∑ j ∈ minus, w j * (e j) ^ 2
  have hab : a + b = 1 := (sum_filter_add_sum_filter_not univ P w).trans hmass
  have hV : A + B = ∑ j, w j * (e j) ^ 2 :=
    sum_filter_add_sum_filter_not univ P (fun j => w j * (e j) ^ 2)
  have ha : 0 ≤ a := sum_nonneg (fun j _ => hw j)
  have hb : 0 ≤ b := sum_nonneg (fun j _ => hw j)
  have hnonneg : 0 ≤ ∑ j, w j * (e j) ^ 2 := sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  change a * b * L ≤ _
  rcases (mul_nonneg ha hb).eq_or_lt with habzero | habpos
  · simpa [← habzero] using hnonneg
  have hterm (i : J) (hi : i ∈ plus) (j : J) (hj : j ∈ minus) :
      w i * w j * (a * b * L) ≤
        w i * w j * (a * (e i) ^ 2 + b * (e j) ^ 2) := by
    rcases (hw i).eq_or_lt with hwi | hwi
    · simp [← hwi]
    rcases (hw j).eq_or_lt with hwj | hwj
    · simp [← hwj]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hwi.le hwj.le)
    calc
      _ ≤ a * b * (e i + e j) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (hpair i j (mem_filter.mp hi).2 (mem_filter.mp hj).2 hwi hwj)
          (mul_nonneg ha hb)
      _ ≤ _ := by
        have hidentity :
            a * (e i) ^ 2 + b * (e j) ^ 2 - a * b * (e i + e j) ^ 2 =
              (a * e i - b * e j) ^ 2 := by
          linear_combination -(a * e i ^ 2 + b * e j ^ 2) * hab
        linarith [sq_nonneg (a * e i - b * e j)]
  have hsum := sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
  have hleft : (∑ i ∈ plus, ∑ j ∈ minus, w i * w j * (a * b * L)) =
      (a * b) * (a * b * L) := by
    simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
    rfl
  have hright : (∑ i ∈ plus, ∑ j ∈ minus,
      w i * w j * (a * (e i) ^ 2 + b * (e j) ^ 2)) = (a * b) * (A + B) := by
    simp_rw [mul_add, sum_add_distrib]
    have h₁ (i j : J) : w i * w j * (a * (e i) ^ 2) = a * (w i * (e i) ^ 2) * w j := by ring
    have h₂ (i j : J) : w i * w j * (b * (e j) ^ 2) = w i * (b * (w j * (e j) ^ 2)) := by ring
    simp_rw [h₁, h₂, ← mul_sum, ← sum_mul]
    rw [← mul_sum]
    change a * A * b + a * (b * B) = _
    ring
  rw [hleft, hright, hV] at hsum
  exact le_of_mul_le_mul_left hsum habpos

private theorem real_product_error (a b a' b' : ℂ) {r : ℝ}
    (ha : ‖a'‖ = r) (hb : ‖b‖ = r) :
    |(a * star b).re - (a' * star b').re| ≤ r * (‖a - a'‖ + ‖b - b'‖) := by
  rw [← Complex.sub_re]
  have heq : a * star b - a' * star b' =
      (a - a') * star b + a' * star (b - b') := by rw [star_sub]; ring
  calc
    _ ≤ ‖a * star b - a' * star b'‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(a - a') * star b‖ + ‖a' * star (b - b')‖ := by rw [heq]; exact norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, norm_star, norm_star, ha, hb]; ring

private theorem sign_product_eq {J : Type*} [Fintype J]
    (w : J → ℝ) (P : J → Prop) [DecidablePred P] (hw : ∑ j, w j = 1) :
    4 * (∑ j with P j, w j) * (∑ j with ¬ P j, w j) =
      1 - (∑ j, w j * (if P j then (1 : ℝ) else -1)) ^ 2 := by
  let a := ∑ j with P j, w j
  let b := ∑ j with ¬ P j, w j
  have hmass : a + b = 1 := (sum_filter_add_sum_filter_not univ P w).trans hw
  have hsign : (∑ j, w j * (if P j then (1 : ℝ) else -1)) = a - b := by
    rw [← sum_filter_add_sum_filter_not univ P (fun j => w j * (if P j then 1 else -1))]
    have ha : (∑ j with P j, w j * (if P j then (1 : ℝ) else -1)) = a :=
      sum_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]
    have hb : (∑ j with ¬ P j, w j * (if P j then (1 : ℝ) else -1)) = -b := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]
    rw [ha, hb, sub_eq_add_neg]
  rw [hsign]
  change 4 * a * b = 1 - (a - b) ^ 2
  nlinarith [congrArg (fun x : ℝ => x ^ 2) hmass]

private theorem averaged_phase_contact_deficit {J : Type*} [Fintype J]
    (w : J → ℝ) (X : J → ℂ) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j)
    {c t δ V : ℝ} (hc : 0 < c) (ht : t ^ 2 = c * (1 - c)) (hX : ∀ j, ‖X j‖ ^ 2 = c)
    (hsep : ∀ j k, 0 < w j → 0 < w k → c * δ ≤ |(X j * star (X k)).re|) :
    let P (j : J) := 0 ≤ (X j).im
    let η (j : J) : ℝ := if P j then 1 else -1
    let A (j : J) := (c : ℂ) + (↑(η j * t) : ℂ) * Complex.I
    let d := max (δ - |2 * c - 1|) 0
    (∑ j, w j * ‖X j - A j‖ ^ 2) ≤ (1 + 4 / t ^ 2) * V →
    (∑ j, w j * η j) ^ 2 ≤ 4 * V / t ^ 4 →
    c * d ^ 2 ≤ 4 * (1 + 4 / t ^ 2 + c * d ^ 2 / t ^ 4) * V := by
  dsimp only
  intro hE hbal
  let P (j : J) := 0 ≤ (X j).im
  let η (j : J) : ℝ := if P j then 1 else -1
  let A (j : J) := (c : ℂ) + (↑(η j * t) : ℂ) * Complex.I
  let e (j : J) := ‖X j - A j‖
  let d := max (δ - |2 * c - 1|) 0
  let r := Real.sqrt c
  have hrpos : 0 < r := Real.sqrt_pos.2 hc
  have hr : r ^ 2 = c := Real.sq_sqrt hc.le
  have hrad (j : J) : ‖X j‖ = r := by
    exact le_antisymm (le_of_sq_le_sq ((hX j).trans hr.symm).le hrpos.le)
      (le_of_sq_le_sq (hr.trans (hX j).symm).le (norm_nonneg _))
  have hpair (i j : J) (hi : P i) (hj : ¬ P j) (hwi : 0 < w i) (hwj : 0 < w j) :
      c * d ^ 2 ≤ (e i + e j) ^ 2 := by
    have hAi : ‖A i‖ = r := by
      have hnorm : ‖A i‖ ^ 2 = c := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [A, η, ite_eq_left hi, one_mul, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, ← pow_two]
        nlinarith [ht]
      exact le_antisymm (le_of_sq_le_sq (hnorm.trans hr.symm).le hrpos.le)
        (le_of_sq_le_sq (hr.trans hnorm.symm).le (norm_nonneg _))
    have hprod := real_product_error (X i) (X j) (A i) (A j) hAi (hrad j)
    have hcontact : (A i * star (A j)).re = c * (2 * c - 1) := by
      simp [A, η, hi, hj, Complex.mul_re, Complex.add_re, Complex.add_im]
      nlinarith [ht]
    have habs : |(A i * star (A j)).re| = c * |2 * c - 1| := by
      rw [hcontact, abs_mul, abs_of_pos hc]
    have htriangle := abs_add_le ((X i * star (X j)).re - (A i * star (A j)).re)
        (A i * star (A j)).re
    rw [sub_add_cancel, habs] at htriangle
    have hraw : r * (r * (δ - |2 * c - 1|)) ≤ r * (e i + e j) := by
      change |(X i * star (X j)).re - (A i * star (A j)).re| ≤ r * (e i + e j) at hprod
      nlinarith only [hr, hsep i j hwi hwj, htriangle, hprod,
        congrArg (fun x : ℝ => x * (δ - |2 * c - 1|)) hr]
    have hbound : r * d ≤ e i + e j := by
      dsimp [d]
      rw [mul_max_of_nonneg _ _ hrpos.le, mul_zero]
      exact max_le (le_of_mul_le_mul_left hraw hrpos)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    calc
      _ = (r * d) ^ 2 := by rw [mul_pow, hr]
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hrpos.le (le_max_right _ _)) hbound 2
  let a := ∑ j with P j, w j
  let b := ∑ j with ¬ P j, w j
  have hpairSum := sign_pair_squared_error w e P hweights hw hpair
  change a * b * (c * d ^ 2) ≤ ∑ j, w j * e j ^ 2 at hpairSum
  have hmass := sign_product_eq w P hw
  change 4 * a * b = 1 - (∑ j, w j * η j) ^ 2 at hmass
  change (∑ j, w j * η j) ^ 2 ≤ 4 * V / t ^ 4 at hbal
  change (∑ j, w j * e j ^ 2) ≤ (1 + 4 / t ^ 2) * V at hE
  have hab : (1 - 4 * V / t ^ 4) / 4 ≤ a * b := by linarith
  have hfinal := (mul_le_mul_of_nonneg_right hab (mul_nonneg hc.le (sq_nonneg d))).trans
    (hpairSum.trans hE)
  change c * d ^ 2 ≤ 4 * (1 + 4 / t ^ 2 + c * d ^ 2 / t ^ 4) * V
  linear_combination 4 * hfinal


/-- The real projection variance bounds the separation of opposite-sign phases. -/
theorem phase_separation_variance_bound
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j)
    (δ : ℝ)
    (hsep : ∀ j k, 0 < w j → 0 < w k → δ ≤ |(z j * star (z k)).re|) :
    let m := ∑ j, (w j : ℂ) * z j
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let c := ‖m‖ ^ 2
    let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
    let s := c * (1 - c)
    let d := (fun adjustment : ℝ => max adjustment 0) (δ - |2 * c - 1|)
    0 < d → c * d ^ 2 ≤ 4 * (1 + 4 / s + c * d ^ 2 / s ^ 2) * D := by
  let b := ∑ j, (w j : ℂ) * z j ^ 2
  let m := ∑ j, (w j : ℂ) * z j
  let c := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
  let s := c * (1 - c)
  let d := max (δ - |2 * c - 1|) 0
  change 0 < d → c * d ^ 2 ≤ 4 * (1 + 4 / s + c * d ^ 2 / s ^ 2) * D
  intro hd
  have hδ' : δ ≤ 1 := by
    have hpositive : ∃ j, 0 < w j := by
      by_contra! hnonpos
      have hsum : ∑ j, w j ≤ 0 := sum_nonpos fun j _ => hnonpos j
      rw [hw] at hsum
      norm_num at hsum
    obtain ⟨j, hj⟩ := hpositive
    have h := hsep j j hj hj
    rw [mul_comm, Complex.star_def, Complex.conj_mul', hz j] at h
    norm_num at h
    exact h
  have hc0 : 0 ≤ c := sq_nonneg _
  have hcmax : c ≤ 1 := by
    have h := norm_sum_le univ (fun j => (w j : ℂ) * z j)
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweights _),
      hz, mul_one, hw] at h
    exact (sq_le_one_iff_abs_le_one _).2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact h)
  have hboundary (hc : c = 0 ∨ c = 1) : d = 0 := by
    rcases hc with hc | hc <;> norm_num [d, hc] <;> exact hδ'
  have hc : 0 < c := by
    rcases hc0.eq_or_lt with hc | hc
    · exact (hd.ne' (hboundary (.inl hc.symm))).elim
    · exact hc
  have hc1 : c < 1 := by
    rcases hcmax.eq_or_lt with hc | hc
    · exact (hd.ne' (hboundary (.inr hc))).elim
    · exact hc
  let t := Real.sqrt s
  have ht : t ^ 2 = s := Real.sq_sqrt (mul_nonneg hc.le (sub_nonneg.mpr hc1.le))
  have ht4 : t ^ 4 = s ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ht]
  have hX (j : J) : ‖X j‖ ^ 2 = c := by simp [X, hz, c]
  have hgsep (j k : J) (hj : 0 < w j) (hk : 0 < w k) :
      c * δ ≤ |(X j * star (X k)).re| := by
    have hm : star m * m = (c : ℂ) := by
      simpa [Complex.star_def, c, Complex.ofReal_pow] using Complex.conj_mul' m
    have he : X j * star (X k) = (c : ℂ) * (z j * star (z k)) := by
      rw [← hm]
      simp only [X, star_mul, star_star]
      ring
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hsep j k hj hk) hc.le
  have hstability := first_two_moment_stability z w hz hw hweights hc hc1
  have hphase := averaged_phase_contact_deficit w X hw hweights hc ht hX hgsep (V := D)
    (by simpa only [sub_add_eq_sub_sub] using hstability.1) hstability.2
  change c * d ^ 2 ≤ 4 * (1 + 4 / t ^ 2 + c * d ^ 2 / t ^ 4) * D at hphase
  rwa [ht, ht4] at hphase

private theorem centered_quarter_residue (q : ℕ) (hq : 0 < q) (hfour : ¬ 4 ∣ q) (d : ℤ) :
    let n := (4 * d - q).bmod (2 * q);
    -(q : ℤ) ≤ n ∧ n ≤ q ∧ (if Even q then (2 : ℤ) else 1) ≤ abs n := by
  let n := (4 * d - q).bmod (2 * q)
  change -(q : ℤ) ≤ n ∧ n ≤ q ∧ (if Even q then (2 : ℤ) else 1) ≤ abs n
  have hm : 0 < 2 * q := Nat.mul_pos (by decide) hq
  have hnlo : -(q : ℤ) ≤ n := by
    have ht := Int.le_bmod (x := 4 * d - q) hm
    change -(q : ℤ) ≤ (4 * d - q).bmod (2 * q)
    omega
  have hnhi : n ≤ q := by
    have ht := Int.bmod_lt (x := 4 * d - q) hm
    change (4 * d - q).bmod (2 * q) ≤ (q : ℤ)
    omega
  refine ⟨hnlo, hnhi, ?_⟩
  have he : n + (2 : ℤ) * q * (4 * d - q).bdiv (2 * q) = 4 * d - q := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Int.bmod_add_bdiv (4 * d - q) (2 * q)
  let k := (4 * d - q).bdiv (2 * q)
  change n + 2 * (q : ℤ) * k = 4 * d - q at he
  by_cases hEven : Even q
  · rw [ite_eq_left hEven]
    obtain ⟨a, ha⟩ := hEven
    have ha' : (q : ℤ) = (a : ℤ) + (a : ℤ) := by exact_mod_cast ha
    have he' : n + 4 * ((a : ℤ) * k) = 4 * d - (q : ℤ) := by rw [ha'] at he ⊢; linarith
    have hq_int : ¬ (4 : ℤ) ∣ (q : ℤ) := by exact_mod_cast hfour
    have hn1 : n ≠ 0 := by omega
    have hn2 : n % 2 = 0 := by omega
    rcases le_or_gt 0 n with hn | hn
    · rw [abs_of_nonneg hn]; omega
    · rw [abs_of_neg hn]; omega
  · rw [ite_eq_right hEven]
    have hOdd : q % 2 = 1 := by
      by_contra! h
      exact hEven (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero (by omega)))
    have hnodd : n % 2 = 1 := by
      have hm : 2 * (q : ℤ) * k = 2 * ((q : ℤ) * k) := by ring
      rw [hm] at he
      omega
    rcases le_or_gt 0 n with hn | hn
    · rw [abs_of_nonneg hn]; omega
    · rw [abs_of_neg hn]; omega

private theorem quarter_cos_separation (q : ℕ) (hq : 0 < q) (hfour : ¬ 4 ∣ q) (d : ℤ) :
    Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q)) ≤
      |Real.cos (2 * Real.pi * d / q)| := by
  let n := (4 * d - q).bmod (2 * q)
  let k := (4 * d - q).bdiv (2 * q)
  let c : ℝ := if Even q then 2 else 1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨hnlo, hnhi, hnm⟩ := centered_quarter_residue q hq hfour d
  change -(q : ℤ) ≤ n at hnlo
  change n ≤ (q : ℤ) at hnhi
  have hnm' : c ≤ |(n : ℝ)| := by
    by_cases he : Even q
    · simp only [he, ite_true, c] at hnm ⊢
      exact_mod_cast hnm
    · simp only [he, ite_false, c] at hnm ⊢
      exact_mod_cast hnm
  have hnq : |(n : ℝ)| ≤ q := abs_le.mpr ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc : 0 ≤ c := by dsimp [c]; split <;> norm_num
  have hshift : 2 * Real.pi * (d : ℝ) / q - Real.pi / 2 =
      (n : ℝ) * Real.pi / (2 * q) + (k : ℝ) * Real.pi := by
    have hraw : n + 2 * (q : ℤ) * k = 4 * d - (q : ℤ) := by
      simpa only [n, k, Nat.cast_mul, Nat.cast_ofNat] using Int.bmod_add_bdiv (4 * d - q) (2 * q)
    have hcast : (n : ℝ) + 2 * (q : ℝ) * (k : ℝ) = 4 * (d : ℝ) - (q : ℝ) := by
      exact_mod_cast hraw
    field_simp
    linear_combination -hcast
  have hpoint : |Real.cos (2 * Real.pi * (d : ℝ) / q)| =
      Real.sin (|(n : ℝ)| * Real.pi / (2 * q)) := by
    rw [← abs_neg (Real.cos _), ← Real.sin_sub_pi_div_two, hshift, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg,
      abs_one, one_zpow, one_mul]
    have hlarge : |(n : ℝ)| * Real.pi / (2 * q) ≤ Real.pi / 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith [mul_le_mul_of_nonneg_right hnq hπ.le]
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · rw [abs_of_nonneg hn] at hlarge ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by positivity, by linarith⟩)
    · rw [abs_of_neg hn] at hlarge ⊢
      have hneg : -(n : ℝ) * Real.pi / (2 * q) = -((n : ℝ) * Real.pi / (2 * q)) := by ring
      rw [hneg, Real.sin_neg]
      have hs : 0 ≤ Real.sin (-(n : ℝ) * Real.pi / (2 * q)) :=
        Real.sin_nonneg_of_mem_Icc ⟨by exact div_nonneg (mul_nonneg (neg_nonneg.mpr hn.le) hπ.le) (by positivity), by linarith⟩
      rw [hneg, Real.sin_neg] at hs
      exact abs_of_nonpos (by linarith)
  rw [hpoint]
  change Real.sin (c * Real.pi / (2 * q)) ≤ _
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have hn : 0 ≤ c * Real.pi / (2 * q) := by positivity
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith [mul_le_mul_of_nonneg_right hnq hπ.le]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnm' hπ.le) (by positivity)

/-- On a cyclic grid without an element of order four, the separation is explicit. -/
theorem cyclic_grid_fourier_gap (q : ℕ) [NeZero q] (hfour : ¬4 ∣ q)
    (w : ZMod q → ℝ) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j) :
    let δ := Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
    let m := ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)
    let b := ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q)
    let c := ‖m‖ ^ 2
    let projection := (star m ^ 2 * b).re
    let D := c / 2 - c ^ 2 + projection / 2
    let s := c * (1 - c)
    let d := max (δ - |2 * c - 1|) 0
    0 < d → c * d ^ 2 ≤ 4 * (1 + 4 / s + c * d ^ 2 / s ^ 2) * D := by
  let χ := ZMod.stdAddChar (N := q)
  let z (j : ZMod q) := χ (-j)
  let m := ∑ j, (w j : ℂ) * z j
  let δ := Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hz (j : ZMod q) : ‖z j‖ = 1 := χ.norm_apply _
  have hm : ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q) = m := by
    rw [ZMod.dft_apply]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_one, smul_eq_mul, mul_comm]
  have hb : (∑ j, (w j : ℂ) * z j ^ 2) =
      ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q) := by
    rw [ZMod.dft_apply]
    refine sum_congr rfl fun j _ => ?_
    have harg : -(j * 2) = 2 • (-j) := by rw [mul_two, two_nsmul, neg_add_rev]
    change (w j : ℂ) * χ (-j) ^ 2 = χ (-(j * 2)) • (w j : ℂ)
    rw [harg, AddChar.map_nsmul_eq_pow, smul_eq_mul, mul_comm]
  have hstar (j : ZMod q) : star (z j) = χ j := by
    have hn : z j ≠ 0 := by intro h; simpa [h] using hz j
    apply mul_right_cancel₀ hn
    have h1 : star (z j) * z j = (1 : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', hz]
      norm_num
    rw [h1]
    change 1 = χ j * χ (-j)
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hsep (j k : ZMod q) (_ : 0 < w j) (_ : 0 < w k) :
      δ ≤ |(z j * star (z k)).re| := by
    rw [hstar]
    change δ ≤ |(χ (-j) * χ k).re|
    rw [← AddChar.map_add_eq_mul, neg_add_eq_sub]
    have hd : (((k - j).val : ℤ) : ZMod q) = k - j := by exact_mod_cast (k - j).natCast_zmod_val
    have hcval : (χ (k - j)).re = Real.cos (2 * Real.pi * ((k - j).val : ℝ) / q) := by
      rw [congrArg (fun a => (χ a).re) hd.symm]
      change (ZMod.stdAddChar (((k - j).val : ℤ) : ZMod q)).re = _
      rw [ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
      congr 2
      push_cast
      ring
    rw [hcval]
    simpa [δ] using quarter_cos_separation q hq hfour ((k - j).val : ℤ)
  dsimp only
  rw [hm, ← hb]
  exact phase_separation_variance_bound z w hz hw hweights δ hsep

end D5.S3.Fourier.Concentration.CyclicGridMomentGap
