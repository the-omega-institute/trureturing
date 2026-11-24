/- GID: D5/S3/Fourier/Concentration/CyclicGridMomentGap
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicGridMomentGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the first Fourier moment away from one half on separated phase supports. -/

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

private theorem exists_small_weighted_error {J : Type*} [Fintype J]
    (w E : J → ℝ) (P : J → Prop) [DecidablePred P]
    (hw : ∀ j, 0 ≤ w j) (hE : ∀ j, 0 ≤ E j) {cap : ℝ} (hc : 0 ≤ cap)
    (hmass : 1 / 4 ≤ ∑ j with P j, w j)
    (hbudget : (∑ j, w j * E j) < cap / 4) :
    ∃ j, P j ∧ 0 < w j ∧ E j ≤ cap := by
  by_contra! hn
  have hterm (j : J) (hj : j ∈ univ.filter P) : w j * cap ≤ w j * E j := by
    rcases (hw j).eq_or_lt with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonneg_left (hn j (mem_filter.mp hj).2 h).le (hw j)
  have hcap : cap / 4 ≤ ∑ j with P j, w j * E j := calc
    _ = (1 / 4 : ℝ) * cap := by ring
    _ ≤ (∑ j with P j, w j) * cap := mul_le_mul_of_nonneg_right hmass hc
    _ ≤ _ := by rw [sum_mul]; exact sum_le_sum hterm
  have htotal : (∑ j with P j, w j * E j) ≤ ∑ j, w j * E j :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => mul_nonneg (hw j) (hE j)
  exact (not_lt_of_ge (hcap.trans htotal)) hbudget

private theorem sign_masses_ge_quarter {J : Type*} [Fintype J]
    (w : J → ℝ) (P : J → Prop) [DecidablePred P]
    (hw : ∑ j, w j = 1)
    (hbal : (∑ j, w j * (if P j then (1 : ℝ) else -1)) ^ 2 ≤ 1 / 4) :
    (1 / 4 ≤ ∑ j with P j, w j) ∧ (1 / 4 ≤ ∑ j with ¬P j, w j) := by
  let a := ∑ j with P j, w j
  let b := ∑ j with ¬P j, w j
  have hmass : a + b = 1 := (sum_filter_add_sum_filter_not univ P w).trans hw
  have hsign : (∑ j, w j * (if P j then (1 : ℝ) else -1)) = a - b := by
    classical
    rw [← sum_filter_add_sum_filter_not univ P (fun j => w j * (if P j then 1 else -1))]
    have ha : (∑ j with P j, w j * (if P j then (1 : ℝ) else -1)) = a :=
      sum_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]
    have hb : (∑ j with ¬P j, w j * (if P j then (1 : ℝ) else -1)) = -b := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]
    rw [ha, hb, sub_eq_add_neg]
  rw [hsign] at hbal
  have hsq : (a - b) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    calc
      _ ≤ 1 / 4 := hbal
      _ = _ := by norm_num
  have hs := abs_le.mp (abs_le_of_sq_le_sq hsq (by norm_num))
  exact ⟨by change 1 / 4 ≤ a; linarith [hs.1], by change 1 / 4 ≤ b; linarith [hs.2]⟩

private theorem gap_error_budgets {c t δ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ δ / 8)
    (hc' : c ≤ (1 + ε) / 2)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (ht : t ^ 2 = c * (1 - c))
    (hgap : (1 + ε) / 2 - c < δ ^ 2 / 1024) :
    let g := (1 + ε) / 2 - c
    4 * (c * g) / t ^ 4 ≤ 1 / 4 ∧
      (1 + 4 / t ^ 2) * (c * g) < c * δ ^ 2 / 36 := by
  dsimp only
  have hδsq : δ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (by rwa [abs_of_pos hδ])
  have hgsmall : (1 + ε) / 2 - c < 1 / 1024 := hgap.trans_le (by linarith)
  have hcsmall : 1 / 4 ≤ c := by linarith
  have hcupper : c ≤ 3 / 4 := by linarith
  have htlo : 3 / 16 ≤ t ^ 2 := by
    rw [ht]
    nlinarith [mul_nonneg (sub_nonneg.mpr hcsmall) (sub_nonneg.mpr hcupper)]
  have htpos : 0 < t ^ 2 := by linarith
  have htfour : (3 / 16 : ℝ) ^ 2 ≤ t ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 16) htlo 2
  constructor
  · apply (div_le_iff₀ (show 0 < t ^ 4 by linarith)).mpr
    have hg0 : 0 ≤ (1 + ε) / 2 - c := by linarith
    have hf : 4 * (c * ((1 + ε) / 2 - c)) ≤ 3 * ((1 + ε) / 2 - c) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcupper) hg0]
    linarith
  · have hf : 4 / t ^ 2 ≤ 22 := by apply (div_le_iff₀ htpos).mpr; linarith
    have hcpos : 0 < c := by linarith
    have hD : 0 ≤ c * ((1 + ε) / 2 - c) := mul_nonneg hcpos.le (by linarith)
    calc
      _ ≤ 23 * (c * ((1 + ε) / 2 - c)) := mul_le_mul_of_nonneg_right (by linarith) hD
      _ < 23 * (c * (δ ^ 2 / 1024)) := mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_left hgap hcpos) (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hcpos.le (sq_nonneg δ)]

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

private theorem gap_of_phase_contacts {J : Type*} [Fintype J]
    (w : J → ℝ) (X : J → ℂ) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j)
    {c t δ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ δ / 8) (hc : 0 < c)
    (hc' : c ≤ (1 + ε) / 2) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (ht : t ^ 2 = c * (1 - c)) (hX : ∀ j, ‖X j‖ ^ 2 = c)
    (hgap : ∀ j k, 0 < w j → 0 < w k → c * δ ≤ |(X j * star (X k)).re|) :
    let η (j : J) : ℝ := if 0 ≤ (X j).im then 1 else -1
    let A (j : J) : ℂ := (c : ℂ) + (↑(η j * t) : ℂ) * Complex.I
    let E := c * ((1 + ε) / 2 - c)
    (∑ j, w j * ‖X j - A j‖ ^ 2) ≤ (1 + 4 / t ^ 2) * E →
    (∑ j, w j * η j) ^ 2 ≤ 4 * E / t ^ 4 →
    c ≤ (1 + ε) / 2 - δ ^ 2 / 1024 := by
  dsimp only
  let P (j : J) := 0 ≤ (X j).im
  let η (j : J) : ℝ := if P j then 1 else -1
  let A (j : J) : ℂ := (c : ℂ) + (↑(η j * t) : ℂ) * Complex.I
  let E := c * ((1 + ε) / 2 - c)
  change (∑ j, w j * ‖X j - A j‖ ^ 2) ≤ (1 + 4 / t ^ 2) * E →
    (∑ j, w j * η j) ^ 2 ≤ 4 * E / t ^ 4 → c ≤ (1 + ε) / 2 - δ ^ 2 / 1024
  intro he hb
  by_contra! hcontr
  have hsmall : (1 + ε) / 2 - c < δ ^ 2 / 1024 := by linarith
  obtain ⟨hbal, herr⟩ := gap_error_budgets hε0 hε hc' hδ hδ' ht hsmall
  have hsign := sign_masses_ge_quarter w P hw (hb.trans hbal)
  let C := c * δ ^ 2 / 9
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hc.le (sq_nonneg _)) (by norm_num)
  have hbudget : (∑ j, w j * ‖X j - A j‖ ^ 2) < C / 4 := by
    have h := he.trans_lt herr
    convert h using 1
    dsimp [C]
    ring
  obtain ⟨i, hi, hwi, hEi⟩ := exists_small_weighted_error w (fun j => ‖X j - A j‖ ^ 2)
    P hweights (fun _ => sq_nonneg _) hC hsign.1 hbudget
  obtain ⟨j, hj, hwj, hEj⟩ := exists_small_weighted_error w (fun j => ‖X j - A j‖ ^ 2)
    (fun j => ¬ P j) hweights (fun _ => sq_nonneg _) hC hsign.2 hbudget
  let r := Real.sqrt c
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr : r ^ 2 = c := Real.sq_sqrt hc.le
  have hXj : ‖X j‖ = r := by
    exact le_antisymm (le_of_sq_le_sq ((hX j).trans hr.symm).le hr0)
      (le_of_sq_le_sq (hr.trans (hX j).symm).le (norm_nonneg _))
  have hAi : ‖A i‖ = r := by
    have hnorm : ‖A i‖ ^ 2 = c := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [A, η, ite_eq_left hi, one_mul, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, ← pow_two]
      nlinarith [ht]
    exact le_antisymm (le_of_sq_le_sq (hnorm.trans hr.symm).le hr0)
      (le_of_sq_le_sq (hr.trans hnorm.symm).le (norm_nonneg _))
  have hd (k : J) (h : ‖X k - A k‖ ^ 2 ≤ C) : ‖X k - A k‖ ≤ r * δ / 3 := by
    have hcap : C = (r * δ / 3) ^ 2 := by dsimp [C]; rw [div_pow, mul_pow, hr]; norm_num
    exact le_of_sq_le_sq (h.trans_eq hcap) (by positivity)
  have hprod := real_product_error (X i) (X j) (A i) (A j) hAi hXj
  have hperp : (A i * star (A j)).re = c * (2 * c - 1) := by
    simp [A, η, hi, hj, Complex.mul_re, Complex.add_re, Complex.add_im]
    nlinarith [ht]
  have hh : |(X i * star (X j)).re - c * (2 * c - 1)| ≤ c * δ * (2 / 3) := calc
    _ ≤ _ := hperp ▸ hprod
    _ ≤ r * (r * δ / 3 + r * δ / 3) :=
      mul_le_mul_of_nonneg_left (add_le_add (hd i hEi) (hd j hEj)) hr0
    _ = _ := by calc
      _ = r ^ 2 * δ * (2 / 3) := by ring
      _ = _ := by rw [hr]
  have hmain : |c * (2 * c - 1)| < c * δ / 3 := by
    rw [abs_mul, abs_of_pos hc, mul_div_assoc]
    apply mul_lt_mul_of_pos_left _ hc
    have hδsq : δ ^ 2 ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
    apply abs_lt.mpr
    constructor <;> linarith
  have hsum := abs_add_le ((X i * star (X j)).re - c * (2 * c - 1)) (c * (2 * c - 1))
  rw [sub_add_cancel] at hsum
  linarith [hgap i j hwi hwj]

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

private theorem centered_second_moment_bound
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j) :
    let m := ∑ j, (w j : ℂ) * z j
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    ‖b - m ^ 2‖ ≤ 1 - ‖m‖ ^ 2 := by
  let m := ∑ j, (w j : ℂ) * z j
  let b := ∑ j, (w j : ℂ) * z j ^ 2
  have hwC : ∑ j, (w j : ℂ) = 1 := by exact_mod_cast hw
  have hcent : ∑ j, (w j : ℂ) * (z j - m) ^ 2 = b - m ^ 2 := calc
    _ = ∑ j, ((w j : ℂ) * z j ^ 2 - 2 * m * ((w j : ℂ) * z j) +
        (w j : ℂ) * m ^ 2) := sum_congr rfl fun j _ => by ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hwC]
      change b - 2 * m * m + 1 * m ^ 2 = b - m ^ 2
      ring
  have hlin : ∑ j, w j * (z j * star m).re = ‖m‖ ^ 2 := by
    have hm : ∑ j, (w j : ℂ) * (z j * star m) = (‖m‖ ^ 2 : ℝ) := by
      simp_rw [← mul_assoc, ← sum_mul]
      simpa [m, Complex.ofReal_pow, mul_comm] using Complex.conj_mul' m
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using congrArg Complex.re hm
  have hsq : ∑ j, w j * ‖z j - m‖ ^ 2 = 1 - ‖m‖ ^ 2 := calc
    _ = ∑ j, (w j - 2 * (w j * (z j * star m).re) + w j * ‖m‖ ^ 2) := by
      refine sum_congr rfl fun j _ => ?_
      have hzsq : Complex.normSq (z j) = 1 := by rw [← Complex.sq_norm, hz j, one_pow]
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im]
      rw [Complex.normSq_apply] at hzsq
      linear_combination w j * hzsq
    _ = _ := by rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hlin, hw]; ring
  have ht := norm_sum_le univ (fun j => (w j : ℂ) * (z j - m) ^ 2)
  rw [hcent] at ht
  simp_rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hweights _)] at ht
  rw [hsq] at ht
  exact ht

/-- Separation from orthogonality improves the first-moment bound for a small second moment. -/
theorem first_moment_gap_of_small_second
    {J : Type*} [Fintype J] (z : J → ℂ) (w : J → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ j k, 0 < w j → 0 < w k → δ ≤ |(z j * star (z k)).re|) :
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let deficit := (fun separation : ℝ => separation ^ 2 / 1024) δ
    ‖b‖ ≤ δ / 8 →
      ‖∑ j, (w j : ℂ) * z j‖ ^ 2 ≤ (1 + ‖b‖) / 2 - deficit := by
  let b := ∑ j, (w j : ℂ) * z j ^ 2
  let ε := ‖b‖
  let m := ∑ j, (w j : ℂ) * z j
  let c := ‖m‖ ^ 2
  let X (j : J) := star m * z j
  let t := Real.sqrt (c * (1 - c))
  change ε ≤ δ / 8 → c ≤ (1 + ε) / 2 - δ ^ 2 / 1024
  intro hε
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
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hc' : c ≤ (1 + ε) / 2 := by
    have hmom := centered_second_moment_bound z w hz hw hweights
    change ‖b - m ^ 2‖ ≤ 1 - c at hmom
    have htri : c ≤ ε + ‖b - m ^ 2‖ := calc
      c = ‖m ^ 2‖ := (norm_pow _ _).symm
      _ = ‖b + -(b - m ^ 2)‖ := by congr 1; ring
      _ ≤ _ := by rw [← norm_neg (b - m ^ 2)]; exact norm_add_le _ _
    linarith
  rcases (sq_nonneg ‖m‖).eq_or_lt with hc0 | hc
  · have h := (sq_le_one_iff_abs_le_one δ).mpr (by rwa [abs_of_pos hδ])
    change 0 = c at hc0
    rw [← hc0]
    linarith
  have hc1 : c < 1 := by linarith
  have ht : t ^ 2 = c * (1 - c) := Real.sq_sqrt (mul_nonneg hc.le (sub_nonneg.mpr hc1.le))
  have hX (j : J) : ‖X j‖ ^ 2 = c := by simp [X, hz, c]
  have hg (j k : J) (hj : 0 < w j) (hk : 0 < w k) :
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
  have hs := first_two_moment_stability z w hz hw hweights hc hc1
  let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
  have hreal : (star m ^ 2 * b).re ≤ c * ε := calc
    _ ≤ ‖star m ^ 2 * b‖ := Complex.re_le_norm _
    _ = c * ε := by simp [norm_pow, c, ε]
  have hvar : D ≤ c * ((1 + ε) / 2 - c) := calc
    D ≤ c / 2 - c ^ 2 + c * ε / 2 :=
      add_le_add (le_refl (c / 2 - c ^ 2))
        (div_le_div_of_nonneg_right hreal (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring
  have hcoef : 0 ≤ 1 + 4 / t ^ 2 := by positivity
  have hden : 0 ≤ t ^ 4 := by positivity
  apply gap_of_phase_contacts w X hw hweights hε0 hε hc hc' hδ hδ' ht hX hg
  · exact (by simpa only [sub_add_eq_sub_sub] using hs.1 : _ ≤ (1 + 4 / t ^ 2) * D).trans
      (mul_le_mul_of_nonneg_left hvar hcoef)
  · exact hs.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvar (by norm_num)) hden)

/-- On a cyclic grid without an element of order four, the separation is explicit. -/
theorem cyclic_grid_fourier_gap (q : ℕ) [NeZero q] (hfour : ¬4 ∣ q)
    (w : ZMod q → ℝ) (hw : ∑ j, w j = 1) (hweights : ∀ j, 0 ≤ w j) :
    let δ := Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
    let b := ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q)
    ‖b‖ ≤ δ / 8 →
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)‖ ^ 2 ≤ (1 + ‖b‖) / 2 - δ ^ 2 / 1024 := by
  let χ := ZMod.stdAddChar (N := q)
  let z (j : ZMod q) := χ (-j)
  let m := ∑ j, (w j : ℂ) * z j
  let δ := Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · split <;> positivity
    · by_cases hqE : Even q
      · rw [ite_eq_left hqE]
        have hq2 : 2 ≤ q := by obtain ⟨a, ha⟩ := hqE; omega
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr (show (2 : ℝ) ≤ q by exact_mod_cast hq2)) Real.pi_pos.le]
      · rw [ite_eq_right hqE]
        have hq1 : 1 ≤ q := hq
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ q by exact_mod_cast hq1)) Real.pi_pos.le]
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
  exact first_moment_gap_of_small_second z w hz hw hweights hδ hsep

end D5.S3.Fourier.Concentration.CyclicGridMomentGap
