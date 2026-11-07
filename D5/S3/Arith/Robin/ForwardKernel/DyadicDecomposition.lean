/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicDecomposition
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-band variance controls every block in a dyadic smoothing decomposition. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingBounds
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance

/-! Terminal dyadic scales and uniform smoothing bounds from a common variance band. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicDecomposition

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The first dyadic scale above the longer power has logarithmically bounded index. -/
theorem exists_dyadic_terminal_scale {X a b : ℝ} (hX : 1 ≤ X) (hab : a < b) :
    ∃ N : ℕ, X ^ b ≤ (2 : ℝ) ^ N * X ^ a ∧
      (2 : ℝ) ^ N * X ^ a < 2 * X ^ b ∧
      (N : ℝ) ≤ 1 + (b - a) * Real.log X / Real.log 2 := by
  have hX0 : 0 < X := by linarith
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 _
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hhk : X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hab.le
  by_cases he : X ^ a = X ^ b
  · refine ⟨0, by simp [he], by simpa [he] using (show X ^ b < 2 * X ^ b by linarith), ?_⟩
    have hl : 0 ≤ (b - a) * Real.log X / Real.log 2 :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hab.le) (Real.log_nonneg hX))
        (Real.log_nonneg (by norm_num))
    simpa using (show (0 : ℝ) ≤ 1 + (b - a) * Real.log X / Real.log 2 by linarith)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hh).mpr hhk)
    (by norm_num : (1 : ℝ) < 2)
  by_cases hpow : (2 : ℝ) ^ n = X ^ b / X ^ a
  · refine ⟨n, (div_le_iff₀ hh).mp hpow.ge, ?_, ?_⟩
    · have heq := (eq_div_iff hh.ne').mp hpow
      linarith
    · have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) n) hn
      rw [Real.log_pow, Real.log_div hk.ne' hh.ne', Real.log_rpow hX0,
        Real.log_rpow hX0] at hl
      have hnle : (n : ℝ) ≤ (b - a) * Real.log X / Real.log 2 :=
        (le_div_iff₀ (Real.log_pos (by norm_num))).mpr (by nlinarith [hl])
      linarith
  · refine ⟨n + 1, (div_lt_iff₀ hh).mp hn' |>.le, ?_, ?_⟩
    · have hstrict : (2 : ℝ) ^ n < X ^ b / X ^ a := lt_of_le_of_ne hn hpow
      have := (lt_div_iff₀ hh).mp hstrict
      rw [pow_succ]
      nlinarith
    · have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) n) hn
      rw [Real.log_pow, Real.log_div hk.ne' hh.ne', Real.log_rpow hX0,
        Real.log_rpow hX0] at hl
      have hnle : (n : ℝ) ≤ (b - a) * Real.log X / Real.log 2 :=
        (le_div_iff₀ (Real.log_pos (by norm_num))).mpr (by nlinarith [hl])
      push_cast
      linarith

/-- Double averages telescope into blocks at consecutive dyadic scales. -/
theorem doubleAverage_dyadic_decomposition (E : ℝ → ℝ) (h x : ℝ) (N : ℕ) :
    doubleAverage h E x = doubleAverage ((2 : ℝ) ^ N * h) E x +
      ∑ j ∈ Finset.range N, smoothingBlock ((2 : ℝ) ^ j * h) E x := by
  have ht := Finset.sum_range_sub' (fun j => doubleAverage ((2 : ℝ) ^ j * h) E x) N
  have he (j : ℕ) : (2 : ℝ) ^ (j + 1) * h = 2 * ((2 : ℝ) ^ j * h) := by
    rw [pow_succ]; ring
  simp only [he, pow_zero, one_mul] at ht
  change doubleAverage h E x = _ + ∑ j ∈ Finset.range N,
    (doubleAverage ((2 : ℝ) ^ j * h) E x -
      doubleAverage (2 * ((2 : ℝ) ^ j * h)) E x)
  linarith

private lemma outer_increment_square_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (8 * X ^ b),
        (∫ x in (X / 4)..(8 * X), increment E u x ^ 2) ≤
          C * X * max u (X ^ a) * Real.log X := by
  let a₀ := (α + a) / 2
  let b₀ := (b + β) / 2
  have hαa₀ : α < a₀ := by dsimp [a₀]; linarith [hBa.2.1]
  have ha₀a : a₀ < a := by dsimp [a₀]; linarith [hBa.2.1]
  have hbb₀ : b < b₀ := by dsimp [b₀]; linarith
  have hb₀β : b₀ < β := by dsimp [b₀]; linarith
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨C, hC, hbound⟩ := MovingLengthVariance.band_increment_square_bound hE
    ⟨hBa.1, hαa₀, ha₀a.trans hBa.2.2.1, hBa.2.2.2⟩
    (ha₀a.trans (hab.trans hbb₀)) hb₀β hV
  have hsmall := FixedLengthCovariance.shifted_band ha₀a (hab.trans hbb₀) ha1
    (c := 1) (d := (1 / 2 : ℝ)) (q := 1) (r := 0)
    zero_lt_one (by norm_num) zero_lt_one le_rfl
  have hlarge := FixedLengthCovariance.shifted_band (ha₀a.trans hab) hbb₀ hb1
    (c := 1) (d := (1 / 2 : ℝ)) (q := 1) (r := 0)
    zero_lt_one (by norm_num) zero_lt_one le_rfl
  have hsmall' := FixedLengthCovariance.shifted_band ha₀a (hab.trans hbb₀) ha1
    (c := 1) (d := 2) (q := 1) (r := 0)
    zero_lt_one (by norm_num) zero_lt_one le_rfl
  have hlarge' := FixedLengthCovariance.shifted_band (ha₀a.trans hab) hbb₀ hb1
    (c := 1) (d := 2) (q := 1) (r := 0)
    zero_lt_one (by norm_num) zero_lt_one le_rfl
  have ht₁ : Tendsto (fun X : ℝ => X / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have ht₂ : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  refine ⟨5 * C, by positivity, ?_⟩
  filter_upwards [ht₁.eventually hbound, ht₂.eventually hbound,
    hsmall, hlarge, hsmall', hlarge', eventually_ge_atTop (2 : ℝ)]
      with X h₁ h₂ hs hl hs' hl' hX
  simp only [fixedLength, one_mul, zero_mul, add_zero] at hs hl hs' hl'
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog₁ : 0 ≤ Real.log (X / 2) := Real.log_nonneg (by linarith)
  have hlog₂ : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hlog₁' : Real.log (X / 2) ≤ Real.log X :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog₂' : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX]
  have hs₁ : (X / 2) ^ a₀ ≤ X ^ a := by simpa only [one_div_mul_eq_div] using hs.1
  have hl₁ : X ^ b ≤ (X / 2) ^ b₀ := by simpa only [one_div_mul_eq_div] using hl.2
  intro u hu
  have hmax : 0 ≤ max u (X ^ a) := hu.1.trans (le_max_left _ _)
  have h₁' := h₁ u ⟨hu.1, hu.2.trans (by nlinarith [hl₁])⟩
  have h₂' := h₂ u ⟨hu.1, hu.2.trans (by nlinarith [hl'.2])⟩
  have hm₁ : max u ((X / 2) ^ a₀) ≤ max u (X ^ a) := max_le_max_left _ hs₁
  have hm₂ : max u ((2 * X) ^ a₀) ≤ max u (X ^ a) := max_le_max_left _ hs'.1
  have hb₁ : (∫ x in (X / 2 / 2)..(4 * (X / 2)), increment E u x ^ 2) ≤
      C * X * max u (X ^ a) * Real.log X := by
    apply h₁'.trans
    exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : X / 2 ≤ X) hC.le)
        hm₁ (by positivity) (by positivity)) hlog₁' hlog₁ (by positivity)
  have hb₂ : (∫ x in (2 * X / 2)..(4 * (2 * X)), increment E u x ^ 2) ≤
      4 * C * X * max u (X ^ a) * Real.log X := by
    apply h₂'.trans
    calc
      _ ≤ C * (2 * X) * max u (X ^ a) * (2 * Real.log X) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm₂ (by positivity))
          hlog₂' hlog₂ (by positivity)
      _ = _ := by ring
  have hi (l r : ℝ) : IntervalIntegrable (fun x => increment E u x ^ 2) volume l r := by
    simpa only [pow_two, id_eq] using (increment_product_comp_integrableOn hE isCompact_uIcc
      continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hm := intervalIntegral.integral_mono_interval
    (show X / 4 ≤ X / 4 from le_rfl) (show X / 4 ≤ X by linarith)
    (show X ≤ 2 * X by linarith) (Eventually.of_forall fun x => sq_nonneg (increment E u x))
    (hi (X / 4) (2 * X))
  have he₁ : X / 2 / 2 = X / 4 := by ring
  have he₂ : 4 * (X / 2) = 2 * X := by ring
  have he₃ : 4 * (2 * X) = 8 * X := by ring
  rw [he₁, he₂] at hb₁
  rw [mul_div_cancel_left₀ X (by norm_num : (2 : ℝ) ≠ 0), he₃] at hb₂
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (X / 4) X) (hi X (8 * X))]
  linarith [hm.trans hb₁]

private lemma common_band_smoothing_bounds
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      intervalL2 (X / 2) (4 * X) (fun x => E x - doubleAverage (X ^ a) E x) ≤
        C * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) ∧
      ∀ R ∈ Icc (X ^ a) (2 * X ^ b),
        intervalL2 (X / 2) (4 * X) (smoothingBlock R E) ≤
          C * Real.sqrt (X * Real.log X) * Real.sqrt R ∧
        intervalL2 (X / 2) (4 * X) (deriv (smoothingBlock R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 2) (4 * X),
          |smoothingBlock R E x| ≤ C * Real.sqrt (X * Real.log X)) ∧
        intervalL2 (X / 2) (4 * X) (deriv (doubleAverage R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 2) (4 * X),
          |deriv (doubleAverage R E) x| ≤ C * Real.sqrt (X * Real.log X) / R) := by
  obtain ⟨D, hD, hbound⟩ := outer_increment_square_bound hE hBa hab hbβ hV
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  -- The sublinear upper scale eventually leaves the required forward margin.
  have hmargin : ∀ᶠ X : ℝ in atTop, X ^ b ≤ X := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX hb1.le
  refine ⟨8 * Real.sqrt D, by positivity, ?_⟩
  filter_upwards [hbound, hmargin, eventually_ge_atTop (2 : ℝ)] with X hb hm hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 _
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hhk : X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hab.le
  let A := Real.sqrt D * Real.sqrt (X * Real.log X)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (8 * X ^ b)) :
      intervalL2 (X / 4) (8 * X) (increment E u) ≤
        A * Real.sqrt (max u (X ^ a)) := by
    have hs := Real.sqrt_le_sqrt (hb u hu)
    change Real.sqrt _ ≤ _
    apply hs.trans_eq
    rw [show D * X * max u (X ^ a) * Real.log X =
      D * (X * Real.log X) * max u (X ^ a) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ D * (X * Real.log X)),
      Real.sqrt_mul hD.le]
  have hiR : ∀ u ∈ Icc (X ^ a) (8 * X ^ b),
      intervalL2 (X / 4) (8 * X) (increment E u) ≤ A * Real.sqrt u := by
    intro u hu
    simpa only [max_eq_left hu.1] using hi u ⟨hh.le.trans hu.1, hu.2⟩
  have hih : ∀ u ∈ Icc (0 : ℝ) (2 * X ^ a),
      intervalL2 (X / 4) (8 * X) (increment E u) ≤ (2 * A) * Real.sqrt (X ^ a) := by
    intro u hu
    have hs : Real.sqrt (max u (X ^ a)) ≤ 2 * Real.sqrt (X ^ a) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt hh.le]
      exact max_le (by linarith [hu.2]) (by linarith)
    exact (hi u ⟨hu.1, by linarith [hu.2]⟩).trans
      ((mul_le_mul_of_nonneg_left hs hA).trans_eq (by ring))
  have hsm := DyadicSmoothingBounds.dyadic_smoothing_bounds_with_residual hE hh hA
    (by positivity : 0 ≤ 2 * A)
    (by linarith : X / 2 ≤ 4 * X) (by linarith : X / 4 ≤ X / 2)
    (by linarith : 4 * X + 4 * X ^ b ≤ 8 * X)
    (by linarith : 4 * X + 2 * X ^ a ≤ 8 * X) hiR hih
  have he : 8 * Real.sqrt D * Real.sqrt (X * Real.log X) = 8 * A := by dsimp [A]; ring
  simp only [he]
  refine ⟨hsm.1.trans ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (X ^ a)]
  intro R hR
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsm.2 R hR
  have hR0 : 0 < R := hh.trans_le hR.1
  refine ⟨h1.trans ?_, h2.trans ?_, fun x hx => (h3 x hx).trans ?_,
    h4.trans ?_, fun x hx => (h5 x hx).trans ?_⟩
  · nlinarith [Real.sqrt_nonneg R]
  · exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg R)
  · linarith
  · exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg R)
  · exact div_le_div_of_nonneg_right (by linarith) hR0.le

/-- One constant and one eventual threshold control the whole dyadic decomposition. -/
theorem common_band_dyadic_decomposition
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ (C : ℝ) (N : ℝ → ℕ), 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      X ^ b ≤ (2 : ℝ) ^ N X * X ^ a ∧
      (2 : ℝ) ^ N X * X ^ a < 2 * X ^ b ∧
      (N X : ℝ) ≤ 1 + (b - a) * Real.log X / Real.log 2 ∧
      (∀ x : ℝ, doubleAverage (X ^ a) E x =
        doubleAverage ((2 : ℝ) ^ N X * X ^ a) E x +
          ∑ j ∈ Finset.range (N X), smoothingBlock ((2 : ℝ) ^ j * X ^ a) E x) ∧
      intervalL2 (X / 2) (4 * X) (fun x => E x - doubleAverage (X ^ a) E x) ≤
        C * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) ∧
      ∀ j ≤ N X,
        let R := (2 : ℝ) ^ j * X ^ a
        intervalL2 (X / 2) (4 * X) (smoothingBlock R E) ≤
          C * Real.sqrt (X * Real.log X) * Real.sqrt R ∧
        intervalL2 (X / 2) (4 * X) (deriv (smoothingBlock R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 2) (4 * X),
          |smoothingBlock R E x| ≤ C * Real.sqrt (X * Real.log X)) ∧
        intervalL2 (X / 2) (4 * X) (deriv (doubleAverage R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 2) (4 * X),
          |deriv (doubleAverage R E) x| ≤ C * Real.sqrt (X * Real.log X) / R) := by
  obtain ⟨C, hC, hbound⟩ := common_band_smoothing_bounds hE hBa hab hbβ hV
  have hchoose (X : ℝ) : ∃ N : ℕ, 1 ≤ X →
      X ^ b ≤ (2 : ℝ) ^ N * X ^ a ∧
      (2 : ℝ) ^ N * X ^ a < 2 * X ^ b ∧
      (N : ℝ) ≤ 1 + (b - a) * Real.log X / Real.log 2 := by
    by_cases hX : 1 ≤ X
    · obtain ⟨N, hN⟩ := exists_dyadic_terminal_scale hX hab
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => (hX h).elim⟩
  choose N hN using hchoose
  refine ⟨C, N, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hb hX
  obtain ⟨hK, hK', hn⟩ := hN X hX
  refine ⟨hK, hK', hn, fun x => doubleAverage_dyadic_decomposition E (X ^ a) x (N X),
    hb.1, ?_⟩
  intro j hj
  apply hb.2
  have hh : 0 ≤ X ^ a := Real.rpow_nonneg (by linarith) _
  exact ⟨by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hh,
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hh).trans hK'.le⟩

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicDecomposition
