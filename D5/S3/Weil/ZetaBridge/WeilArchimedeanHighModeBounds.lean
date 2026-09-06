/- GID: D5/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds
   mirror-E: none(waiver:operator-identification-and-Hilbert-transform-bridge)
   anchors: []
   digest: Frequency-decaying bounds for the actual arithmetic Gamma symbol and its diagonal correction, with absolute convergence. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-!
# Actual archimedean high-mode estimates

The public statement extracts the Gamma term from the existing complete
`arithmeticBoundarySymbol`. It also bounds the explicit diagonal correction
series. No new Weil form, Hilbert-transform estimate, or desired form lower
bound is assumed. The first estimate improves the constant 2 to 1+1/|omega|.
Together with the correction estimate it supplies the arithmetic constants in
the logarithmic high-mode lower bound proved in the existing theory volume.
The Fourier/operator identification, discrete Hilbert bound, and resulting
full-form logarithmic inequality remain separate paper bridges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.WeilArchimedeanHighModeBounds

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

private def rate (j : ℕ) : ℝ := 2 * (j : ℝ) + 1 / 2
private def majorant (w : ℝ) (j : ℕ) : ℝ := w / (rate j ^ 2 + w ^ 2)
private def sineTerm (L w : ℝ) (j : ℕ) : ℝ :=
  w * (1 - Real.exp (-rate j * L)) / (rate j ^ 2 + w ^ 2)
private def correction (L w : ℝ) (j : ℕ) : ℝ :=
  (1 - Real.exp (-rate j * L)) * (rate j ^ 2 - w ^ 2) /
    (rate j ^ 2 + w ^ 2) ^ 2

private theorem rate_pos (j : ℕ) : 0 < rate j := by
  dsimp [rate]
  positivity

private theorem tail_step {w : ℝ} (hw : 0 < w) (j : ℕ) :
    majorant w (j + 1) ≤
      w * ((w + 2 * (j : ℝ) + 1 / 2)⁻¹ -
        (w + 2 * (j : ℝ) + 5 / 2)⁻¹) := by
  let d : ℝ := w + 2 * (j : ℝ) + 1 / 2
  let D : ℝ := (2 * (j : ℝ) + 5 / 2) ^ 2 + w ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : 0 < d + 2 := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : d * (d + 2) ≤ 2 * D := by
    dsimp [d, D]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [sq_nonneg (w - 2 * (j : ℝ) - 3 / 2)]
  have hb : rate (j + 1) = 2 * (j : ℝ) + 5 / 2 := by
    dsimp [rate]
    push_cast
    ring
  have ht : 1 / D ≤ 2 / (d * (d + 2)) := by
    apply (div_le_div_iff₀ hD (mul_pos hd hd2)).mpr
    simpa using hden
  calc
    majorant w (j + 1) = w * (1 / D) := by rw [majorant, hb]; dsimp [D]; ring
    _ ≤ w * (2 / (d * (d + 2))) := mul_le_mul_of_nonneg_left ht hw.le
    _ = _ := by
      have he : w + 2 * (j : ℝ) + 5 / 2 = d + 2 := by dsimp [d]; ring
      rw [he]
      change w * (2 / (d * (d + 2))) = w * (d⁻¹ - (d + 2)⁻¹)
      field_simp [ne_of_gt hd, ne_of_gt hd2]
      <;> ring

private theorem tail_partial {w : ℝ} (hw : 0 < w) (M : ℕ) :
    (∑ j ∈ Finset.range M, majorant w (j + 1)) ≤
      w * ((w + 1 / 2)⁻¹ - (w + 1 / 2 + 2 * (M : ℝ))⁻¹) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hs := tail_step hw M
      have h1 : w + 2 * (M : ℝ) + 1 / 2 = w + 1 / 2 + 2 * (M : ℝ) := by ring
      have h2 : w + 2 * (M : ℝ) + 5 / 2 = w + 1 / 2 + 2 * ((M + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [h1, h2] at hs
      simp only [mul_sub] at ih hs ⊢
      linarith

private theorem partial_bound {w : ℝ} (hw : 0 < w) (M : ℕ) :
    (∑ j ∈ Finset.range M, majorant w j) ≤ 1 + 1 / w := by
  cases M with
  | zero => simp only [Finset.sum_range_zero]; positivity
  | succ M =>
      rw [Finset.sum_range_succ']
      have ht := tail_partial hw M
      have hratio : w * (w + 1 / 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one (by positivity)).mpr (by linarith)
      have hlast : 0 ≤ w * (w + 1 / 2 + 2 * (M : ℝ))⁻¹ := by positivity
      have h0 : majorant w 0 ≤ 1 / w := by
        change w / ((1 / 2 : ℝ) ^ 2 + w ^ 2) ≤ 1 / w
        apply (div_le_div_iff₀ (by positivity) hw).mpr
        nlinarith
      simp only [mul_sub] at ht
      linarith

private theorem majorant_sum {w : ℝ} (hw : 0 < w) :
    Summable (majorant w) ∧ (∑' j : ℕ, majorant w j) ≤ 1 + 1 / w := by
  have hnon (j : ℕ) : 0 ≤ majorant w j := by dsimp [majorant]; positivity
  exact ⟨summable_of_sum_range_le hnon (partial_bound hw),
    Real.tsum_le_of_sum_range_le hnon (partial_bound hw)⟩

private theorem factor_bounds {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    0 ≤ 1 - Real.exp (-rate j * L) ∧ 1 - Real.exp (-rate j * L) ≤ 1 := by
  have hp := Real.exp_pos (-rate j * L)
  have he : Real.exp (-rate j * L) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (rate_pos j).le) hL)
  constructor <;> linarith

private theorem sine_abs_le {L w : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    ‖sineTerm L w j‖ ≤ majorant |w| j := by
  obtain ⟨h0, h1⟩ := factor_bounds hL j
  have hd : 0 < rate j ^ 2 + w ^ 2 := by have := rate_pos j; positivity
  rw [Real.norm_eq_abs]
  dsimp [sineTerm, majorant]
  rw [abs_div, abs_mul, abs_of_nonneg h0, abs_of_pos hd, sq_abs]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg w) h1) hd.le

private theorem correction_abs_le {L w : ℝ} (hL : 0 ≤ L) (hw : w ≠ 0) (j : ℕ) :
    ‖correction L w j‖ ≤ majorant |w| j / |w| := by
  obtain ⟨h0, h1⟩ := factor_bounds hL j
  have hd : 0 < rate j ^ 2 + w ^ 2 := by have := rate_pos j; positivity
  have hdiff : |rate j ^ 2 - w ^ 2| ≤ rate j ^ 2 + w ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (rate j), sq_nonneg w]
  have hnum : (1 - Real.exp (-rate j * L)) * |rate j ^ 2 - w ^ 2| ≤
      rate j ^ 2 + w ^ 2 := by
    have h := mul_le_mul h1 hdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  rw [Real.norm_eq_abs]
  dsimp [correction]
  rw [abs_div, abs_mul, abs_of_nonneg h0, abs_of_pos (sq_pos_of_pos hd)]
  calc
    _ ≤ (rate j ^ 2 + w ^ 2) / (rate j ^ 2 + w ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = majorant |w| j / |w| := by
      dsimp [majorant]
      rw [sq_abs]
      field_simp [ne_of_gt hd, abs_ne_zero.mpr hw]
      <;> ring

/-- The Gamma component of the actual arithmetic symbol has envelope
1+L/(2*pi*|n|). The explicit diagonal correction is absolutely summable and
bounded by 1/(pi*|n|)+L/(2*pi^2*n^2). These are arithmetic series conclusions;
no unknown spectral quantity or desired high-mode lower bound is an input. -/
theorem arithmetic_archimedean_high_mode_bounds
    {c : ℕ} (hc : 2 ≤ c) (n : ℤ) (hn : n ≠ 0) :
    let L : ℝ := Real.log (c : ℝ)
    let w : ℝ := 2 * Real.pi * (n : ℝ) / L
    let b : ℕ → ℝ := fun j => 2 * (j : ℝ) + 1 / 2
    let R : ℕ → ℝ := fun j =>
      (1 - Real.exp (-b j * L)) * (b j ^ 2 - w ^ 2) / (b j ^ 2 + w ^ 2) ^ 2
    |arithmeticBoundarySymbol c n +
      2 * w * (Real.cosh (L / 2) - 1) / (w ^ 2 + 1 / 4) +
      ∑ j ∈ Finset.range c,
        (ArithmeticFunction.vonMangoldt j / Real.sqrt j) * Real.sin (w * Real.log j)|
        ≤ 1 + L / (2 * Real.pi * |(n : ℝ)|) ∧
    Summable (fun j => ‖R j‖) ∧
    |(2 / L) * ∑' j : ℕ, R j| ≤
      1 / (Real.pi * |(n : ℝ)|) + L / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
  dsimp only
  let L : ℝ := Real.log (c : ℝ)
  let w : ℝ := 2 * Real.pi * (n : ℝ) / L
  have hc1 : (1 : ℝ) < (c : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hc)
  have hL : 0 < L := Real.log_pos hc1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hw : w ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnR) hL.ne'
  have hwabs : |w| = 2 * Real.pi * |(n : ℝ)| / L := by
    dsimp [w]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hL]
    norm_num
  have hmajor := majorant_sum (abs_pos.mpr hw)
  have hs : Summable (fun j => ‖sineTerm L w j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (sine_abs_le hL.le) hmajor.1
  have hsbound : |∑' j : ℕ, sineTerm L w j| ≤ 1 + 1 / |w| := by
    calc
      _ = ‖∑' j : ℕ, sineTerm L w j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j : ℕ, ‖sineTerm L w j‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' j : ℕ, majorant |w| j :=
        hs.tsum_le_tsum (sine_abs_le hL.le) hmajor.1
      _ ≤ _ := hmajor.2
  have hrs : Summable (fun j => ‖correction L w j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (correction_abs_le hL.le hw) (hmajor.1.div_const |w|)
  have hrbound : |∑' j : ℕ, correction L w j| ≤ (1 + 1 / |w|) / |w| := by
    calc
      _ = ‖∑' j : ℕ, correction L w j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j : ℕ, ‖correction L w j‖ := norm_tsum_le_tsum_norm hrs
      _ ≤ ∑' j : ℕ, majorant |w| j / |w| :=
        hrs.tsum_le_tsum (correction_abs_le hL.le hw) (hmajor.1.div_const |w|)
      _ = (∑' j : ℕ, majorant |w| j) / |w| := by rw [tsum_div_const]
      _ ≤ _ := div_le_div_of_nonneg_right hmajor.2 (abs_nonneg w)
  constructor
  · have hid : arithmeticBoundarySymbol c n +
        2 * w * (Real.cosh (L / 2) - 1) / (w ^ 2 + 1 / 4) +
        (∑ j ∈ Finset.range c,
          (ArithmeticFunction.vonMangoldt j / Real.sqrt j) * Real.sin (w * Real.log j)) =
        -(∑' j : ℕ, sineTerm L w j) := by
      unfold arithmeticBoundarySymbol
      change (- (2 * w * (Real.cosh (L / 2) - 1) / (w ^ 2 + 1 / 4)) -
        (∑' j : ℕ, sineTerm L w j) -
        (∑ j ∈ Finset.range c,
          (ArithmeticFunction.vonMangoldt j / Real.sqrt j) * Real.sin (w * Real.log j))) +
        _ + _ = _
      ring
    change |arithmeticBoundarySymbol c n + _ + _| ≤ _
    rw [hid, abs_neg]
    calc
      _ ≤ 1 + 1 / |w| := hsbound
      _ = _ := by rw [hwabs]; field_simp [hL.ne', Real.pi_ne_zero, abs_ne_zero.mpr hnR]; ring
  · refine ⟨hrs, ?_⟩
    change |(2 / L) * ∑' j : ℕ, correction L w j| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / L)]
    calc
      _ ≤ (2 / L) * ((1 + 1 / |w|) / |w|) :=
        mul_le_mul_of_nonneg_left hrbound (by positivity)
      _ = _ := by
        rw [hwabs, ← sq_abs (n : ℝ)]
        field_simp [hL.ne', Real.pi_ne_zero, abs_ne_zero.mpr hnR]
        <;> ring

#print axioms arithmetic_archimedean_high_mode_bounds

end D5.S3.Weil.ZetaBridge.WeilArchimedeanHighModeBounds
