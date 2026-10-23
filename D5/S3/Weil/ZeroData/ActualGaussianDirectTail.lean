/- Complete omitted-distance tail, using direct reciprocal-square mass.
   No shells, no extra height, and no compilation claim. -/
import D5.S3.Weil.ZeroData.ActualGaussianLocalWindow
import D5.S3.Arith.Robin.ZeroPowerSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualGaussianMass
open D5.S3.Weil.ZeroData.ActualGaussianZeroSum
open D5.S3.Weil.ZeroData.ActualGaussianLocalWindow

namespace D5.S3.Weil.ZeroData.ActualGaussianDirectTail

private theorem exp_cancel (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The one scalar estimate replaces the entire infinite shell decomposition.
The strict complement is used below; this estimate even includes equality. -/
theorem shifted_tail_majorant (t γ m : ℝ) (ht : t ≠ 0)
    (hγ : 10 < γ) (hm : 1 ≤ m) (hd : 6 ≤ |t - γ|) :
    Real.exp (-m * (t - γ) ^ 2) ≤
      (γ + 10) ^ 2 * Real.exp (-36 * m) * t⁻¹ ^ 2 := by
  let d := |t - γ|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hd6 : 6 ≤ d := hd
  have hdsq : 36 ≤ d ^ 2 := by nlinarith
  have htbound : |t| ≤ γ + d := by
    have h := abs_add_le (t - γ) γ
    rw [sub_add_cancel, abs_of_pos (by linarith : 0 < γ)] at h
    linarith
  have hscale : γ + d ≤ (γ + 6) * d / 6 := by
    nlinarith
  have htsq : t ^ 2 ≤ (γ + 6) ^ 2 * (d ^ 2 / 36) := by
    have h := sq_le_sq₀ (abs_nonneg t) (by positivity : 0 ≤ (γ + 6) * d / 6)
    have hh := h.mpr (htbound.trans hscale)
    rw [sq_abs] at hh
    nlinarith
  have hr : d ^ 2 / 36 ≤ Real.exp (m * (d ^ 2 - 36)) := by
    have hlin : d ^ 2 / 36 ≤ 1 + m * (d ^ 2 - 36) := by
      have hp := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hdsq)
      nlinarith
    exact hlin.trans (by simpa only [add_comm] using
      Real.add_one_le_exp (m * (d ^ 2 - 36)))
  have hprod : t ^ 2 * Real.exp (-m * (d ^ 2 - 36)) ≤ (γ + 10) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hr (sq_nonneg (γ + 6))
    have h2 := mul_le_mul_of_nonneg_right (htsq.trans h1)
      (Real.exp_nonneg (-m * (d ^ 2 - 36)))
    have hc := exp_cancel (m * (d ^ 2 - 36))
    have hprod : (γ + 6) ^ 2 * Real.exp (m * (d ^ 2 - 36)) *
        Real.exp (-m * (d ^ 2 - 36)) = (γ + 6) ^ 2 := by
      have hcancel : Real.exp (m * (d ^ 2 - 36)) *
          Real.exp (-m * (d ^ 2 - 36)) = 1 := by
        calc
          _ = Real.exp (m * (d ^ 2 - 36)) *
              Real.exp (-(m * (d ^ 2 - 36))) := by
            congr 2 <;> ring
          _ = 1 := exp_cancel _
      calc
        _ = (γ + 6) ^ 2 *
            (Real.exp (m * (d ^ 2 - 36)) * Real.exp (-m * (d ^ 2 - 36))) := by ring
        _ = _ := by rw [hcancel]; ring
    rw [hprod] at h2
    nlinarith
  have hsplit : Real.exp (-m * d ^ 2) =
      Real.exp (-m * (d ^ 2 - 36)) * Real.exp (-36 * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : Real.exp (-m * d ^ 2) * t ^ 2 ≤
      (γ + 10) ^ 2 * Real.exp (-36 * m) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg (-36 * m))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_ne_zero ht)]
  simpa only [d, sq_abs] using hfin

theorem omitted_summand_norm (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (k : ℕ) (hk : 6 < |(actualZero k).im - γ|) :
    ‖summand m γ (actualZero k)‖ ≤
      ((γ + 10) ^ 2 * Real.exp (-19 * m)) * ((actualZero k).im)⁻¹ ^ 2 := by
  let ρ := actualZero k
  have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  have hs' : 0 < ρ.re ∧ ρ.re < 1 := by
    simpa only [ρ, actualZero] using hs
  have ht : ρ.im ≠ 0 := by
    intro he
    have hh := occurrence_height k
    change 10 < |ρ.im| at hh
    rw [he, abs_zero] at hh
    linarith
  have hb : ρ.re ^ 2 + 16 * ρ.re ≤ 17 := by
    nlinarith [mul_nonneg hs'.1.le (sub_nonneg.mpr hs'.2.le)]
  have hnorm : ‖summand m γ ρ‖ =
      Real.exp (m * (ρ.re ^ 2 + 16 * ρ.re - (ρ.im - γ) ^ 2)) := by
    rw [summand, Complex.norm_exp]
    congr 1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hnorm]
  calc
    _ ≤ Real.exp (17 * m) * Real.exp (-m * (ρ.im - γ) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ Real.exp (17 * m) *
        ((γ + 10) ^ 2 * Real.exp (-36 * m) * ρ.im⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (shifted_tail_majorant _ _ _ ht hγ hm hk.le)
        (Real.exp_nonneg _)
    _ = _ := by
      have he : Real.exp (17 * m) * Real.exp (-36 * m) = Real.exp (-19 * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = ((γ + 10) ^ 2 * (Real.exp (17 * m) * Real.exp (-36 * m))) *
            ρ.im⁻¹ ^ 2 := by ring
        _ = _ := by rw [he]

def omitted (m γ : ℝ) (k : ℕ) : ℂ :=
  if 6 < |(actualZero k).im - γ| then summand m γ (actualZero k) else 0

theorem omitted_summable (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    Summable (omitted m γ) := by
  apply Summable.of_norm_bounded
    (inverse_square_summable.mul_left ((γ + 10) ^ 2 * Real.exp (-19 * m)))
  intro k
  by_cases hk : 6 < |(actualZero k).im - γ|
  · simpa only [omitted, if_pos hk] using omitted_summand_norm m γ hm hγ k hk
  · simp only [omitted, if_neg hk, norm_zero]
    positivity

theorem omitted_tail_le_two (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖∑' k : ℕ, omitted m γ k‖ ≤ 2 * (γ + 10) ^ 2 * Real.exp (-19 * m) := by
  have hb : ∀ k, ‖omitted m γ k‖ ≤
      ((γ + 10) ^ 2 * Real.exp (-19 * m)) * ((actualZero k).im)⁻¹ ^ 2 := by
    intro k
    by_cases hk : 6 < |(actualZero k).im - γ|
    · simpa only [omitted, if_pos hk] using omitted_summand_norm m γ hm hγ k hk
    · simp only [omitted, if_neg hk, norm_zero]
      positivity
  have hs := (inverse_square_summable.mul_left
    ((γ + 10) ^ 2 * Real.exp (-19 * m))).hasSum
  have habs := (omitted_summable m γ hm hγ).norm
  calc
    _ ≤ ∑' k : ℕ, ‖omitted m γ k‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ((γ + 10) ^ 2 * Real.exp (-19 * m)) *
        (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) := by
      simpa only [tsum_mul_left] using habs.tsum_le_tsum hb hs.summable
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left mass_lt_two.le
        (by positivity : 0 ≤ (γ + 10) ^ 2 * Real.exp (-19 * m))
      nlinarith

/-- Literal original F3 constant, on the strict omitted family. -/
theorem omitted_tail_original (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    ‖∑' k : ℕ, if 6 < |(actualZero k).im - γ|
      then summand m γ (actualZero k) else 0‖ ≤
        4 * (γ + 10) ^ 2 * Real.exp (-19 * m) := by
  exact (omitted_tail_le_two m γ hm hγ).trans (by
    nlinarith [mul_nonneg (sq_nonneg (γ + 10)) (Real.exp_nonneg (-19 * m))])

/-- Absolute convergence precedes the exact closed-local/strict-complement
split. In particular every distance-six occurrence stays in the finite sum. -/
theorem E_eq_local_add_omitted (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    E m γ = (∑ k ∈ localWindow γ, summand m γ (actualZero k)) +
      ∑' k : ℕ, omitted m γ k := by
  classical
  let h : ℕ → ℂ := fun k =>
    if k ∈ localWindow γ then summand m γ (actualZero k) else 0
  have hh : Summable h := by
    apply Summable.of_norm_bounded (E_summable m γ hm).norm
    intro k
    by_cases hk : k ∈ localWindow γ <;> simp [h, hk]
  have heq : (fun k => summand m γ (actualZero k)) = h + omitted m γ := by
    funext k
    by_cases hk : |(actualZero k).im - γ| ≤ 6
    · simp [h, omitted, mem_localWindow, hk, not_lt.mpr hk]
    · simp [h, omitted, mem_localWindow, hk, lt_of_not_ge hk]
  have hhead : (∑' k, h k) = ∑ k ∈ localWindow γ, summand m γ (actualZero k) := by
    rw [tsum_eq_sum (s := localWindow γ) (fun k hk => by simp [h, hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [h, hk]
  unfold E
  calc
    _ = ∑' k : ℕ, (h k + omitted m γ k) := by
      rw [heq]
      rfl
    _ = (∑' k : ℕ, h k) + ∑' k : ℕ, omitted m γ k :=
      hh.tsum_add (omitted_summable m γ hm hγ)
    _ = _ := by rw [hhead]

/-- The already merged power-sum theorem supplies the ORIGINAL 500-scale
Cassel time, applied to the actual complete closed local window. -/
theorem original_cassel_time (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hγ : 0 < ρ.im) :
    let δ := ρ.re - 1 / 2
    let D := ρ.im + 10
    let m₀ := 100 * D ^ 2 / δ ^ 2
    let m₁ := 500 * D ^ 4 / δ ^ 2
    let a := ρ.re ^ 2 + 16 * ρ.re
    ∃ m : ℝ, m₀ ≤ m ∧ m ≤ m₁ ∧
      Real.exp (a * m) ≤ (∑ k ∈ localWindow ρ.im, summand m ρ.im (actualZero k)).re := by
  classical
  let δ := ρ.re - 1 / 2
  let D := ρ.im + 10
  let m₀ := 100 * D ^ 2 / δ ^ 2
  let m₁ := 500 * D ^ 4 / δ ^ 2
  let a := ρ.re ^ 2 + 16 * ρ.re
  let s := localWindow ρ.im
  let O := ↥s
  let q (k : ℕ) := (actualZero k - Complex.I * (ρ.im : ℂ)) ^ 2 +
    16 * (actualZero k - Complex.I * (ρ.im : ℂ))
  let z (k : O) := Complex.exp ((m₀ : ℂ) * (q k.1 - (a : ℂ)))
  obtain ⟨r, hr⟩ := actualData.zero_exhaustive hρ
  let k₀ := actualOccurrenceEquiv.symm ⟨r, ⟨0, actualData.multiplicity_pos r⟩⟩
  have hk₀ : actualZero k₀ = ρ := by simp [actualZero, k₀, hr]
  have hk₀mem : k₀ ∈ s := by
    change k₀ ∈ localWindow ρ.im
    rw [mem_localWindow, hk₀]
    simp
  let j : O := ⟨k₀, hk₀mem⟩
  have hrcoord : ρ - Complex.I * (ρ.im : ℂ) = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp
  have hq : q k₀ = (a : ℂ) := by
    dsimp [q, a]
    rw [hk₀, hrcoord]
    push_cast
    ring
  have hz : z j = 1 := by
    change Complex.exp ((m₀ : ℂ) * (q k₀ - (a : ℂ))) = 1
    rw [hq, sub_self, mul_zero, Complex.exp_zero]
  let e : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  obtain ⟨ν, hνlo, hνhi, hselect⟩ :=
    D5.S3.Arith.Robin.ZeroPowerSum.exists_pow_sum_re_ge_one
      (fun i => z (e i)) ⟨e.symm j, by simpa only [e.apply_symm_apply] using hz⟩
  have hselect' : 1 ≤ (∑ k : O, z k ^ ν).re := by
    simpa only [e.sum_comp (fun k : O => z k ^ ν)] using hselect
  have hνloR : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hνlo
  have hcard : Fintype.card O = s.card := Fintype.card_coe _
  have hνhiR : (ν : ℝ) ≤ 2 * (s.card : ℝ) + 1 := by
    rw [hcard] at hνhi
    exact_mod_cast hνhi
  have hcount : (s.card : ℝ) ≤ 2 * D ^ 2 := localWindow_card ρ.im hγ
  have hD : 10 < D := by dsimp [D]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hm₀ : 0 < m₀ := by dsimp [m₀]; positivity
  have hνD : (ν : ℝ) ≤ 5 * D ^ 2 := by nlinarith
  let m := (ν : ℝ) * m₀
  have hmlo : m₀ ≤ m := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hνloR hm₀.le
  have hmhi : m ≤ m₁ := by
    calc
      _ ≤ (5 * D ^ 2) * m₀ := mul_le_mul_of_nonneg_right hνD hm₀.le
      _ = _ := by dsimp [m₀, m₁]; ring
  have hterm (k : O) : summand m ρ.im (actualZero k.1) =
      (Real.exp (a * m) : ℂ) * z k ^ ν := by
    dsimp only [summand, z]
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [q, m]
    push_cast
    ring
  have hsum : (∑ k ∈ s, summand m ρ.im (actualZero k)) =
      (Real.exp (a * m) : ℂ) * ∑ k : O, z k ^ ν := by
    rw [← Finset.sum_coe_sort s]
    simp_rw [hterm]
    rw [Finset.mul_sum]
  refine ⟨m, hmlo, hmhi, ?_⟩
  rw [hsum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hselect' (Real.exp_nonneg (a * m))

/-- Full E, at the original finite Cassel time, after paying the entire
strict omitted tail. Neither a full-E lower bound nor a tail is a premise. -/
theorem full_E_original_time (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hγ : 0 < ρ.im) :
    let δ := ρ.re - 1 / 2
    let D := ρ.im + 10
    let m₀ := 100 * D ^ 2 / δ ^ 2
    let m₁ := 500 * D ^ 4 / δ ^ 2
    let a := ρ.re ^ 2 + 16 * ρ.re
    ∃ m : ℝ, m₀ ≤ m ∧ m ≤ m₁ ∧ 1 ≤ m ∧
      Real.exp (a * m) / 2 ≤ (E m ρ.im).re := by
  dsimp only
  let δ := ρ.re - 1 / 2
  let D := ρ.im + 10
  let a := ρ.re ^ 2 + 16 * ρ.re
  obtain ⟨m, hmlo, hmhi, hlocal⟩ := original_cassel_time ρ hρ hβ hγ
  have hheight : 10 < ρ.im := by
    simpa only [abs_of_pos hγ] using actual_height_gt_ten ρ hρ
  have hD : 20 < D := by dsimp [D]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhi : δ < 1 / 2 := by dsimp [δ]; linarith [hρ.2.2]
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have htime : 100 * D ^ 2 ≤ m * δ ^ 2 := (div_le_iff₀ hδsq).mp hmlo
  have hmpos : 0 < m := (div_pos (by positivity : 0 < 100 * D ^ 2) hδsq).trans_le hmlo
  have hmD : D ^ 2 ≤ m := by
    have hδsmall : δ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hδsmall hmpos.le, sq_nonneg D]
  have hm : 1 ≤ m := by nlinarith
  have ha : 0 ≤ a := by dsimp [a]; nlinarith [sq_nonneg ρ.re]
  have hexp : 1 ≤ Real.exp (a * m) := Real.one_le_exp (mul_nonneg ha hmpos.le)
  have habsorb : 2 * D ^ 2 * Real.exp (-19 * m) ≤ (1 : ℝ) / 2 := by
    have h4 : 4 * D ^ 2 ≤ Real.exp (19 * m) := by
      linarith [Real.add_one_le_exp (19 * m)]
    have hmul := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg (-19 * m))
    have hc := exp_cancel (19 * m)
    have hprod : 4 * D ^ 2 * Real.exp (-19 * m) ≤ 1 := by
      calc
        _ ≤ Real.exp (19 * m) * Real.exp (-19 * m) := hmul
        _ = 1 := by
          simpa using exp_cancel (19 * m)
    nlinarith
  have htail := omitted_tail_le_two m ρ.im hm hheight
  have hre : -(2 * D ^ 2 * Real.exp (-19 * m)) ≤
      (∑' k, omitted m ρ.im k).re := by
    have hh := Complex.abs_re_le_norm (∑' k, omitted m ρ.im k)
    have hh' := (abs_le.mp (hh.trans htail)).1
    exact hh'
  have he := E_eq_local_add_omitted m ρ.im hm hheight
  have heR := congrArg Complex.re he
  simp only [Complex.add_re] at heR
  change Real.exp (a * m) ≤
    (∑ k ∈ localWindow ρ.im, summand m ρ.im (actualZero k)).re at hlocal
  refine ⟨m, hmlo, hmhi, hm, ?_⟩
  change Real.exp (a * m) / 2 ≤ (E m ρ.im).re
  linarith

end D5.S3.Weil.ZeroData.ActualGaussianDirectTail
