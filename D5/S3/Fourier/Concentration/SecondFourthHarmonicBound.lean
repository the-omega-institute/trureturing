/- GID: D5/S3/Fourier/Concentration/SecondFourthHarmonicBound
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/SecondFourthHarmonicBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The joint second and fourth harmonic constraints yield a sharp first harmonic bound. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.Fourier.Concentration.SecondFourthHarmonicBound

universe u

/-- A quartic comparison bounds the mean of a real projection. -/
private theorem projected_mean_bound {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (hx : ∀ j, |x j| ≤ 1) (a r : ℝ) (ha : 0 < a)
    (hr : ∑ j, w j * x j ^ 2 ≤ r)
    (hmix : ∑ j, w j * ((1 - x j ^ 2) * (x j ^ 2 - a ^ 2)) ≤ 0) :
    ∑ j, w j * x j ≤ (a + r) / (1 + a) := by
  have point (y : ℝ) (hy : |y| ≤ 1) :
      2 * a * (1 + a) * ((1 + a) * (y - 1) + (1 - y ^ 2)) ≤
        (1 - y ^ 2) * (y ^ 2 - a ^ 2) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hy
    have hproduct := mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hhi) (sq_nonneg (y - a)))
      (show 0 ≤ y + 1 + 2 * a by linarith)
    calc
      _ ≤ 2 * a * (1 + a) * ((1 + a) * (y - 1) + (1 - y ^ 2)) +
          (1 - y) * (y - a) ^ 2 * (y + 1 + 2 * a) :=
        le_add_of_nonneg_right hproduct
      _ = _ := by ring
  have h := sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (point (x j) (hx j)) (hw j)
  have hsum :
      (∑ j, w j * (2 * a * (1 + a) * ((1 + a) * (x j - 1) + (1 - x j ^ 2)))) =
        (2 * a * (1 + a)) *
          ((1 + a) * ((∑ j, w j * x j) - 1) + (1 - ∑ j, w j * x j ^ 2)) := by
    simp only [mul_left_comm (w _) (2 * a * (1 + a)), ← mul_sum]
    congr 1
    simp_rw [mul_add, mul_left_comm (w _) (1 + a), mul_sub, mul_one]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hw1, mul_one]
  rw [hsum] at h
  have hcoef : 0 < 2 * a * (1 + a) := mul_pos (by linarith) (by linarith)
  have hinner := nonpos_of_mul_nonpos_right (h.trans hmix) hcoef
  apply (le_div_iff₀ (by linarith : 0 < 1 + a)).2
  nlinarith only [hinner, hr]

/-- The weighted moment of the given harmonic of the phase. -/
noncomputable def harmonic {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (n : ℕ) : ℂ := ∑ j, (w j : ℂ) * z j ^ n

/-- The optimal first harmonic magnitude for caps on the second and fourth harmonics. -/
noncomputable def harmonicBound (caps : ℝ × ℝ) : ℝ :=
  let (e, k) := caps
  let b := min e (Real.sqrt ((1 + k) / 2))
  let r := (1 + b) / 2
  if b = 1 then 1 else
    let a := min (Real.sqrt r) (Real.sqrt ((1 + k) / (4 * (1 - b))))
    (a + r) / (1 + a)

private theorem weighted_sq {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) :
    (∑ j, w j * f j) ^ 2 ≤ ∑ j, w j * f j ^ 2 := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset ι)
    (r := fun j => w j * f j) (f := w) (g := fun j => w j * f j ^ 2)
    (fun j _ => hw j) (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
    (fun j _ => le_of_eq (by ring))
  simpa only [hw1, one_mul] using h

private theorem harmonic_re {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (n : ℕ) : (harmonic w z n).re = ∑ j, w j * (z j ^ n).re := by
  simp [harmonic, Complex.re_sum, Complex.mul_re]

private theorem twice_sq_re (z : ℂ) (hz : ‖z‖ = 1) :
    2 * z.re ^ 2 = 1 + (z ^ 2).re := by
  have hn : z.re * z.re + z.im * z.im = 1 := by
    simpa [Complex.normSq_apply, hz] using Complex.normSq_eq_norm_sq z
  simp only [pow_two, Complex.mul_re]
  nlinarith only [hn]

private theorem twice_sq_mean {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw1 : ∑ j, w j = 1) (z : ι → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    2 * (∑ j, w j * (z j).re ^ 2) = 1 + (harmonic w z 2).re := by
  rw [harmonic_re, ← hw1, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  calc
    _ = w j * (2 * (z j).re ^ 2) := by ring
    _ = _ := by rw [twice_sq_re _ (hz j)]; ring

private theorem eighth_projection_deficit (z : ℂ) (hz : ‖z‖ = 1) :
    8 * (z.re ^ 2 - z.re ^ 4) = 1 - (z ^ 4).re := by
  have h₂ := twice_sq_re z hz
  have h₄ := twice_sq_re (z ^ 2) (by rw [norm_pow, hz, one_pow])
  rw [show (z ^ 2) ^ 2 = z ^ 4 by ring] at h₄
  have h₂' : (z ^ 2).re = 2 * z.re ^ 2 - 1 := by linarith only [h₂]
  rw [h₂'] at h₄
  linarith only [show 2 * (2 * z.re ^ 2 - 1) ^ 2 =
    8 * z.re ^ 4 - 8 * z.re ^ 2 + 2 by ring, h₄]

private theorem projection_frontier {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (z : ι → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (e k : ℝ) (he : 0 ≤ e) (he₁ : e ≤ 1) (hk : 0 ≤ k)
    (h₂ : ‖harmonic w z 2‖ ≤ e) (h₄ : ‖harmonic w z 4‖ ≤ k) :
    (harmonic w z 1).re ≤ harmonicBound (e, k) := by
  let b := min e (Real.sqrt ((1 + k) / 2))
  let r := (1 + b) / 2
  have hx (j : ι) : |(z j).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (hz j)
  have hb₀ : 0 ≤ b := le_min he (Real.sqrt_nonneg _)
  have hb₁ : b ≤ 1 := (min_le_left _ _).trans he₁
  rw [harmonic_re]
  simp only [pow_one]
  change (∑ j, w j * (z j).re) ≤
    if b = 1 then 1 else
      let a := min (Real.sqrt r) (Real.sqrt ((1 + k) / (4 * (1 - b))))
      (a + r) / (1 + a)
  by_cases hb : b = 1
  · rw [ite_eq_left hb, ← hw1]
    exact sum_le_sum fun j _ =>
      mul_le_of_le_one_right (hw j) ((abs_le.mp (hx j)).2)
  rw [ite_eq_right hb]
  have hb' : b < 1 := lt_of_le_of_ne hb₁ hb
  have hsecond : (harmonic w z 2).re ≤ b := by
    refine le_min ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans h₂)) ?_
    have hm := weighted_sq w (fun j => (z j ^ 2).re) hw hw1
    rw [← harmonic_re] at hm
    have ht := twice_sq_mean w hw1 (fun j => z j ^ 2)
      (fun j => by simp [hz j])
    have hr₄ : harmonic w (fun j => z j ^ 2) 2 = harmonic w z 4 := by
      unfold harmonic
      congr 1
      ext j
      rw [← pow_mul]
    rw [hr₄] at ht
    have hc := (le_abs_self (harmonic w z 4).re).trans
      ((Complex.abs_re_le_norm _).trans h₄)
    exact Real.le_sqrt_of_sq_le (by linarith only [hm, ht, hc])
  have hr : ∑ j, w j * (z j).re ^ 2 ≤ r := by
    dsimp [r]
    linarith only [twice_sq_mean w hw1 z hz, hsecond]
  have hr₀ : 0 ≤ r := by dsimp [r]; positivity
  by_cases hswitch : Real.sqrt r ≤ Real.sqrt ((1 + k) / (4 * (1 - b)))
  · rw [min_eq_left hswitch]
    calc
      _ ≤ Real.sqrt r := Real.le_sqrt_of_sq_le ((weighted_sq w _ hw hw1).trans hr)
      _ = _ := (eq_div_iff (by positivity)).2 (by nlinarith only [Real.sq_sqrt hr₀])
  rw [min_eq_right (le_of_not_ge hswitch)]
  let a := Real.sqrt ((1 + k) / (4 * (1 - b)))
  have hapos : 0 < a := Real.sqrt_pos.2 (div_pos (by linarith) (by linarith))
  have haeq : 4 * (1 - b) * a ^ 2 = 1 + k := by
    dsimp [a]
    rw [Real.sq_sqrt (div_nonneg (by linarith) (by linarith)), mul_div_cancel₀]
    linarith
  have hdef : 8 * (∑ j, w j * ((z j).re ^ 2 - (z j).re ^ 4)) =
      1 - (harmonic w z 4).re := by
    rw [harmonic_re, ← hw1]
    simp_rw [mul_sum, ← sum_sub_distrib, mul_left_comm (8 : ℝ),
      eighth_projection_deficit _ (hz _), mul_sub, mul_one]
  have hfour : -k ≤ (harmonic w z 4).re := by
    linarith only [neg_abs_le (harmonic w z 4).re,
      Complex.abs_re_le_norm (harmonic w z 4), h₄]
  apply projected_mean_bound w (fun j => (z j).re) hw hw1 hx a r hapos hr
  have hs :
      (∑ j, w j * ((1 - (z j).re ^ 2) * ((z j).re ^ 2 - a ^ 2))) =
        (∑ j, w j * ((z j).re ^ 2 - (z j).re ^ 4)) -
          (1 - ∑ j, w j * (z j).re ^ 2) * a ^ 2 := by
    have hunit : 1 - (∑ j, w j * (z j).re ^ 2) =
        ∑ j, w j * (1 - (z j).re ^ 2) := by
      conv_lhs => rw [← hw1, ← sum_sub_distrib]
      simp only [mul_sub, mul_one]
    rw [hunit, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hscale := mul_le_mul_of_nonneg_right (sub_le_sub_left hr 1) (sq_nonneg a)
  have heq : 8 * ((1 - r) * a ^ 2) = 1 + k := by
    dsimp [r]
    linarith only [show 8 * ((1 - (1 + b) / 2) * a ^ 2) = 4 * (1 - b) * a ^ 2 by ring, haeq]
  linarith only [hdef, hfour, hscale, heq]

private theorem harmonic_rotate {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ)
    (u : ℂ) (n : ℕ) :
    harmonic w (fun j => u * z j) n = u ^ n * harmonic w z n := by
  simp only [harmonic, mul_pow, mul_sum, mul_left_comm (↑(w _) : ℂ)]

private theorem harmonic_frontier_upper {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (z : ι → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (e k : ℝ) (he : 0 ≤ e) (he₁ : e ≤ 1) (hk : 0 ≤ k)
    (h₂ : ‖harmonic w z 2‖ ≤ e) (h₄ : ‖harmonic w z 4‖ ≤ k) :
    ‖harmonic w z 1‖ ≤ harmonicBound (e, k) := by
  let m := harmonic w z 1
  have hbound (u : ℂ) (hu : ‖u‖ = 1) :
      (u * m).re ≤ harmonicBound (e, k) := by
    have hphase (j : ι) : ‖u * z j‖ = 1 := by rw [norm_mul, hu, hz j, mul_one]
    have hnorm (n : ℕ) : ‖harmonic w (fun j => u * z j) n‖ = ‖harmonic w z n‖ := by
      rw [harmonic_rotate, norm_mul, norm_pow, hu, one_pow, one_mul]
    have hproj := projection_frontier w hw hw1 (fun j => u * z j) hphase
      e k he he₁ hk (by rwa [hnorm]) (by rwa [hnorm])
    rwa [harmonic_rotate, pow_one] at hproj
  change ‖m‖ ≤ harmonicBound (e, k)
  by_cases hm : m = 0
  · simpa [hm] using hbound 1 (by simp)
  let u := (starRingEnd ℂ) m / (‖m‖ : ℂ)
  have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hu : ‖u‖ = 1 := by
    simp [u, hmpos.ne']
  have hum : u * m = (‖m‖ : ℂ) := by
    have hstar : (starRingEnd ℂ) m * m = (‖m‖ : ℂ) ^ 2 := by
      simpa only [Complex.ofReal_pow] using Complex.conj_mul' m
    rw [show u * m = (starRingEnd ℂ) m * m / (‖m‖ : ℂ) by simp [u, div_mul_eq_mul_div], hstar]
    field_simp [norm_ne_zero_iff.mpr hm]
  simpa [hum] using hbound u hu

private theorem three_phase_law (a r : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (har : a ^ 2 ≤ r) (hr₁ : r ≤ 1) :
    ∃ (w : Fin 3 → ℝ) (z : Fin 3 → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧
      harmonic w z 1 = (((a + r) / (1 + a) : ℝ) : ℂ) ∧
      harmonic w z 2 = ((2 * r - 1 : ℝ) : ℂ) ∧
      harmonic w z 4 = ((1 - 8 * (1 - r) * a ^ 2 : ℝ) : ℂ) := by
  let v := Real.sqrt (1 - a ^ 2)
  let p : ℂ := ⟨a, v⟩
  let l := (r - a ^ 2) / (1 - a ^ 2)
  let w : Fin 3 → ℝ := ![l, (1 - l) / 2, (1 - l) / 2]
  let z : Fin 3 → ℂ := ![1, p, (starRingEnd ℂ) p]
  have had : 0 < 1 - a ^ 2 := by
    have h := mul_pos (sub_pos.mpr ha₁) (show 0 < 1 + a by linarith)
    nlinarith only [h]
  have hpd : ‖p‖ = 1 := by
    have hn : Complex.normSq p = 1 := by
      change a * a + v * v = 1
      nlinarith only [Real.sq_sqrt had.le]
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith only [hn, norm_nonneg p]
  have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr har) had.le
  have hl₁ : l ≤ 1 := (div_le_one₀ had).2 (by linarith)
  have hbal : l + (1 - l) * a ^ 2 = r := by
    dsimp [l]
    field_simp
    ring
  refine ⟨w, z, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [w] <;> linarith
  · simp [Fin.sum_univ_three, w]
    ring
  · intro j
    fin_cases j <;> simp [z, hpd]
  have hmoment (n : ℕ) :
      harmonic w z n = ((l + (1 - l) * (p ^ n).re : ℝ) : ℂ) := by
    rw [harmonic, Fin.sum_univ_three]
    simp only [w, z, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, one_pow, mul_one]
    change (l : ℂ) + (((1 - l) / 2 : ℝ) : ℂ) * p ^ n +
      (((1 - l) / 2 : ℝ) : ℂ) * ((starRingEnd ℂ) p) ^ n =
        ((l + (1 - l) * (p ^ n).re : ℝ) : ℂ)
    rw [← map_pow (starRingEnd ℂ)]
    have hreal : ((starRingEnd ℂ) (p ^ n)).re = (p ^ n).re := rfl
    have himag : ((starRingEnd ℂ) (p ^ n)).im = -(p ^ n).im := rfl
    apply Complex.ext <;>
      (simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hreal, himag, -map_pow]
       try ring)
  have hp₂ : (p ^ 2).re = 2 * a ^ 2 - 1 := by
    have h := twice_sq_re p hpd
    change 2 * a ^ 2 = 1 + (p ^ 2).re at h
    linarith only [h]
  have hp₄ : (p ^ 4).re = 1 - 8 * (a ^ 2 - a ^ 4) := by
    have h := eighth_projection_deficit p hpd
    change 8 * (a ^ 2 - a ^ 4) = 1 - (p ^ 4).re at h
    linarith only [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmoment]
    simp only [pow_one]
    norm_cast
    change l + (1 - l) * a = (a + r) / (1 + a)
    apply (eq_div_iff (by positivity)).2
    nlinarith only [hbal]
  · rw [hmoment, hp₂]
    norm_cast
    nlinarith only [hbal]
  · rw [hmoment, hp₄]
    norm_cast
    have h := congrArg (fun x : ℝ => 8 * a ^ 2 * x) hbal
    nlinarith only [h, hbal]

private theorem harmonic_frontier_attained (e k : ℝ) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (hk : 0 ≤ k) (hk₁ : k ≤ 1) :
    ∃ (w : Fin 3 → ℝ) (z : Fin 3 → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧
      ‖harmonic w z 2‖ ≤ e ∧ ‖harmonic w z 4‖ ≤ k ∧
      ‖harmonic w z 1‖ = harmonicBound (e, k) := by
  let b := min e (Real.sqrt ((1 + k) / 2))
  let r := (1 + b) / 2
  have hb₀ : 0 ≤ b := le_min he (Real.sqrt_nonneg _)
  have hbe : b ≤ e := min_le_left _ _
  have hb₁ : b ≤ 1 := hbe.trans he₁
  have hbk : b ^ 2 ≤ (1 + k) / 2 := by
    have h := pow_le_pow_left₀ hb₀ (min_le_right e (Real.sqrt ((1 + k) / 2))) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  by_cases hb : b = 1
  · have heq : e = 1 := by linarith
    have hkq : k = 1 := by rw [hb] at hbk; linarith
    obtain ⟨w, z, hw, hw₁, hz, hm₁, hm₂, hm₄⟩ :=
      three_phase_law 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨w, z, hw, hw₁, hz, ?_, ?_, ?_⟩
    · norm_num [hm₂, heq]
    · norm_num [hm₄, hkq]
    · change ‖harmonic w z 1‖ = (if b = 1 then 1 else _)
      rw [ite_eq_left hb]
      norm_num [hm₁]
  have hblt : b < 1 := lt_of_le_of_ne hb₁ hb
  let u := (1 + k) / (4 * (1 - b))
  let a := min (Real.sqrt r) (Real.sqrt u)
  have hr₀ : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hu : 0 ≤ u := div_nonneg (by linarith) (by linarith)
  have ha₀ : 0 ≤ a := le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have har : a ^ 2 ≤ r := by
    have h := pow_le_pow_left₀ ha₀ (min_le_left (Real.sqrt r) (Real.sqrt u)) 2
    rwa [Real.sq_sqrt hr₀] at h
  have ha₁ : a < 1 := by nlinarith only [har, hr₁, ha₀]
  obtain ⟨w, z, hw, hw₁, hz, hm₁, hm₂, hm₄⟩ := three_phase_law a r ha₀ ha₁ har hr₁.le
  refine ⟨w, z, hw, hw₁, hz, ?_, ?_, ?_⟩
  · rw [hm₂, Complex.norm_real, Real.norm_eq_abs,
      show 2 * r - 1 = b by dsimp [r]; ring, abs_of_nonneg hb₀]
    exact hbe
  · rw [hm₄, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hmax (h : a ^ 2 = u) : 8 * (1 - r) * a ^ 2 = 1 + k := by
      rw [h]
      dsimp [r, u]
      field_simp
      ring
    have hfac : 0 ≤ 8 * (1 - r) := by linarith
    have hau : a ^ 2 ≤ u := by
      have h := pow_le_pow_left₀ ha₀ (min_le_right (Real.sqrt r) (Real.sqrt u)) 2
      rwa [Real.sq_sqrt hu] at h
    refine ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_left hau hfac
      have hden : 0 < 4 * (1 - b) := by linarith
      have hc : 8 * (1 - r) * u = 1 + k := by
        dsimp [u, r]
        field_simp
        ring
      linarith only [h, hc]
    · by_cases h : Real.sqrt r ≤ Real.sqrt u
      · have ha : a ^ 2 = r := by dsimp [a]; rw [min_eq_left h, Real.sq_sqrt hr₀]
        rw [ha]
        have hc : 1 - 8 * (1 - r) * r = 2 * b ^ 2 - 1 := by dsimp [r]; ring
        linarith only [hc, hbk]
      · have ha : a ^ 2 = u := by
          dsimp [a]
          rw [min_eq_right (le_of_not_ge h), Real.sq_sqrt hu]
        linarith only [hmax ha, hk]
  · rw [hm₁, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold harmonicBound
    change (a + r) / (1 + a) = (if b = 1 then 1 else (a + r) / (1 + a))
    exact (ite_eq_right hb).symm

/-- The universal first harmonic bound is attained by a law with at most three phases. -/
theorem sharp_second_fourth_harmonic_bound (e k : ℝ) (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) :
    let bound := harmonicBound (e, k)
    (∀ {ι : Type u} [Fintype ι] (w : ι → ℝ)
      (_ : ∀ j, 0 ≤ w j) (_ : ∑ j, w j = 1) (z : ι → ℂ) (_ : ∀ j, ‖z j‖ = 1),
      ‖harmonic w z 2‖ ≤ e → ‖harmonic w z 4‖ ≤ k → ‖harmonic w z 1‖ ≤ bound) ∧
    (∃ (w : Fin 3 → ℝ) (z : Fin 3 → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧ ‖harmonic w z 2‖ ≤ e ∧ ‖harmonic w z 4‖ ≤ k ∧
        ‖harmonic w z 1‖ = bound) := by
  change _ ∧ _
  exact ⟨fun {ι} _ w hw hw₁ z hz h₂ h₄ =>
    harmonic_frontier_upper w hw hw₁ z hz e k he₀ he₁ hk₀ h₂ h₄,
    harmonic_frontier_attained e k he₀ he₁ hk₀ hk₁⟩

#print axioms sharp_second_fourth_harmonic_bound

end D5.S3.Fourier.Concentration.SecondFourthHarmonicBound
