/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/TriangleRampZeta
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/TriangleRampZeta
   mirror-E: none(waiver:conditional-rh-consumer)
   anchors: []
   utility: none
   digest: The actual von Mangoldt sum with triangular weight under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp
import D5.S3.Arith.PrimitiveRoot.CharacterSieve
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

/-! The arithmetic sum includes exactly the natural numbers strictly below x. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRamp

namespace D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta

/-- The strict-cutoff triangular Mangoldt sum, also at integer endpoints. -/
def smoothedMangoldt (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈x⌉₊, ArithmeticFunction.vonMangoldt n * (1 - (n : ℝ) / x)

private lemma smoothedMangoldt_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ smoothedMangoldt x := by
  apply Finset.sum_nonneg
  intro n hn
  apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp
  · have hnlt : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    exact sub_nonneg.mpr ((div_le_one hx0).mpr hnlt.le)

private lemma small_range_bound {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 4) :
    x / 2 - Real.sqrt x ≤ smoothedMangoldt x := by
  have hs := Real.sq_sqrt hx
  have hsn := Real.sqrt_nonneg x
  have hsu : Real.sqrt x ≤ 2 := (Real.sqrt_le_iff).mpr
    ⟨by norm_num, by norm_num; exact hx4⟩
  have hl : x / 2 - Real.sqrt x ≤ 0 := by nlinarith
  exact hl.trans (smoothedMangoldt_nonneg hx)

private lemma mangoldtPart_fixed {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    mangoldtPart t = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), mangoldtRamp n t := by
  exact mangoldtPart_eq_range ht (by
    push_cast
    exact htx.trans_lt (Nat.lt_floor_add_one x))

private lemma smoothed_eq_max_sum {x : ℝ} (hx : 0 < x) :
    smoothedMangoldt x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n * max (1 - (n : ℝ) / x) 0 := by
  unfold smoothedMangoldt
  calc
    _ = ∑ n ∈ Finset.range ⌈x⌉₊,
        ArithmeticFunction.vonMangoldt n * max (1 - (n : ℝ) / x) 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [max_eq_left (sub_nonneg.mpr ((div_le_one hx).mpr
        (Nat.lt_ceil.mp (Finset.mem_range.mp hn)).le))]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.ceil_le_floor_add_one x))
      intro n _ hn
      have hxn : x ≤ (n : ℝ) := le_of_not_gt (by
        simpa only [Finset.mem_range, Nat.lt_ceil] using hn)
      rw [max_eq_right (by have := (one_le_div hx).mpr hxn; linarith), mul_zero]

private lemma removeAverage_mangoldt {x : ℝ} (hx : 1 ≤ x) :
    removeAverage mangoldtPart x = smoothedMangoldt x := by
  have hx0 : 0 < x := by linarith
  have hp (t : ℝ) (ht : t ∈ uIcc 1 x) : mangoldtPart t =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), mangoldtRamp n t := by
    rw [uIcc_of_le hx] at ht
    exact mangoldtPart_fixed (by linarith [ht.1]) ht.2
  rw [removeAverage, mangoldtPart_fixed hx0.le le_rfl,
    intervalIntegral.integral_congr hp,
    intervalIntegral.integral_finsetSum (fun n _ =>
      (mangoldtRamp_continuous n).intervalIntegrable 1 x),
    Finset.mul_sum, ← Finset.sum_sub_distrib, smoothed_eq_max_sum hx0]
  apply Finset.sum_congr rfl
  intro n _
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mangoldtRamp]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  change ArithmeticFunction.vonMangoldt n * ramp n x -
    2 / x * (∫ t in (1 : ℝ)..x, ArithmeticFunction.vonMangoldt n * ramp n t) = _
  rw [intervalIntegral.integral_const_mul]
  calc
    _ = ArithmeticFunction.vonMangoldt n * removeAverage (ramp n) x := by
      unfold removeAverage
      ring
    _ = _ := by rw [removeAverage_ramp hn1 hx0]

private lemma mangoldtPart_explicit {x : ℝ} (hx : 1 < x) :
    mangoldtPart x = x * Real.log x - (1 + Real.eulerMascheroniConstant) * x +
      (actualH (Real.log x)).re + Real.log (2 * Real.pi) - trivialT (Real.log x) := by
  have hx0 : 0 < x := by linarith
  have he := congrArg Complex.re (actual_integrated_explicit_formula (Real.log_pos hx))
  simp only [Real.exp_log hx0, Complex.ofReal_re] at he
  rw [U_eq_complete_ramps hx0.le] at he
  linarith

/-- A two-sided bound retaining the actual trivial-zero term and its integral. -/
theorem smoothedMangoldt_explicit_bound {x : ℝ}
    (hRH : 1 < x → RiemannHypothesis) (hx : 1 ≤ x) :
    |smoothedMangoldt x -
      (x / 2 - (3 / 2 + Real.eulerMascheroniConstant) / x - Real.log (2 * Real.pi) +
        2 * Real.log (2 * Real.pi) / x - trivialT (Real.log x) +
        2 / x * (∫ t in (1 : ℝ)..x, trivialT (Real.log t)))| ≤
      7 / 3 * firstLiMass * Real.sqrt x - 4 / 3 * firstLiMass / x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have hT : trivialT 0 = 1 - Real.log 2 := by
      simpa [trivialT] using trivialCoeff_hasSum.tsum_eq
    have hm := firstLiMass_split
    have hp := firstLiMass_pos
    have hs : smoothedMangoldt 1 = 0 := by norm_num [smoothedMangoldt]
    simp only [hs, Real.log_one, Real.sqrt_one,
      intervalIntegral.integral_same, mul_zero, div_one, mul_one, hT]
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
    have he : (1 : ℝ) / 2 - (3 / 2 + Real.eulerMascheroniConstant) -
        (Real.log 2 + Real.log Real.pi) + 2 * (Real.log 2 + Real.log Real.pi) -
        (1 - Real.log 2) = -firstLiMass := by linarith
    rw [he]
    simp only [add_zero, zero_sub, neg_neg, abs_of_pos hp]
    linarith
  have hRH := hRH hx
  have hx0 : 0 < x := by linarith
  let C : ℝ := firstLiMass
  let f : ℝ → ℝ := fun t => t * Real.log t - (1 + Real.eulerMascheroniConstant) * t
  let h : ℝ → ℝ := fun t => (actualH (Real.log t)).re
  let T : ℝ → ℝ := fun t => trivialT (Real.log t)
  let L : ℝ := Real.log (2 * Real.pi)
  have hlog : ContinuousOn Real.log (Icc 1 x) :=
    Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [ht.1]))
  have hfc : ContinuousOn f (Icc 1 x) :=
    (continuousOn_id.mul hlog).sub (continuous_const.mul continuous_id).continuousOn
  have hhc : ContinuousOn h (Icc 1 x) :=
    Complex.continuous_re.comp_continuousOn (actualH_continuous.comp_continuousOn hlog)
  have hTc : ContinuousOn T (Icc 1 x) :=
    trivialT_continuousOn.comp hlog (fun t ht => Real.log_nonneg ht.1)
  have hfi : IntervalIntegrable f volume 1 x :=
    (hfc.mono (by rw [uIcc_of_le hx.le])).intervalIntegrable
  have hhi : IntervalIntegrable h volume 1 x :=
    (hhc.mono (by rw [uIcc_of_le hx.le])).intervalIntegrable
  have hTi : IntervalIntegrable T volume 1 x :=
    (hTc.mono (by rw [uIcc_of_le hx.le])).intervalIntegrable
  have hpoint (t : ℝ) (ht : 1 < t) : mangoldtPart t = f t + h t + L - T t :=
    mangoldtPart_explicit ht
  have hint : (∫ t in (1 : ℝ)..x, mangoldtPart t) =
      (∫ t in (1 : ℝ)..x, f t) + (∫ t in (1 : ℝ)..x, h t) +
        (x - 1) * L - (∫ t in (1 : ℝ)..x, T t) := by
    calc
      _ = ∫ t in (1 : ℝ)..x, (f t + h t + L - T t) :=
        intervalIntegral.integral_congr_Ioo_of_le hx.le (fun t ht => hpoint t ht.1)
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hfi.add hhi).add
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume 1 x)) hTi,
          intervalIntegral.integral_add (hfi.add hhi) intervalIntegrable_const,
          intervalIntegral.integral_add hfi hhi, intervalIntegral.integral_const]
        rfl
  have hkernel : smoothedMangoldt x = removeAverage f x + removeAverage h x - L +
      2 * L / x - T x + 2 / x * (∫ t in (1 : ℝ)..x, T t) := by
    rw [← removeAverage_mangoldt hx.le]
    unfold removeAverage
    rw [hpoint x hx, hint]
    field_simp
    ; ring
  have hbound (t : ℝ) (ht : 1 ≤ t) : |h t| ≤ C * Real.sqrt t := by
    have ht0 : 0 < t := by linarith
    have he := RHSharpActualEnvelope.normalizedH_bound hRH (Real.log t)
    change ‖(Real.exp (-Real.log t / 2) : ℂ) * actualH (Real.log t)‖ ≤ C at he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at he
    have he' := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (Real.log t / 2))
    have hex : Real.exp (Real.log t / 2) * Real.exp (-Real.log t / 2) = 1 := by
      rw [← Real.exp_add, show Real.log t / 2 + -Real.log t / 2 = 0 by ring,
        Real.exp_zero]
    rw [← mul_assoc, hex, one_mul, Real.exp_half, Real.exp_log ht0] at he'
    exact (Complex.abs_re_le_norm _).trans (by simpa [mul_comm] using he')
  have hb : |removeAverage h x| ≤ 7 * C / 3 * Real.sqrt x - 4 * C / (3 * x) := by
    apply removeAverage_sqrt_bound hx.le (hbound x hx.le)
    exact MeasureTheory.ae_of_all _ (fun t ht => hbound t ht.1.le)
  have hm : removeAverage f x = x / 2 -
      (3 / 2 + Real.eulerMascheroniConstant) / x := by
    simpa only [f, show (1 : ℝ) + Real.eulerMascheroniConstant + 1 / 2 =
      3 / 2 + Real.eulerMascheroniConstant by ring] using
      removeAverage_main (1 + Real.eulerMascheroniConstant) hx0.le
  rw [hkernel, hm]
  convert hb using 1 <;> dsimp only [C, L, T] <;> congr 1 <;> ring

private lemma smoothed_explicit_lower_gt_one (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 < x) :
    x / 2 - (7 / 3 * firstLiMass) * Real.sqrt x - (1 + Real.log Real.pi) -
      (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        4 / 3 * firstLiMass) / x ≤ smoothedMangoldt x := by
  have hx0 : 0 < x := by linarith
  let C : ℝ := firstLiMass
  let T : ℝ → ℝ := fun t => trivialT (Real.log t)
  let L : ℝ := Real.log (2 * Real.pi)
  have hb := smoothedMangoldt_explicit_bound (fun _ => hRH) hx.le
  have hTbound : T x ≤ 1 - Real.log 2 := trivialT_le_mass (Real.log_nonneg hx.le)
  have hTnonneg : 0 ≤ 2 / x * (∫ t in (1 : ℝ)..x, T t) := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg hx.le
    intro t ht
    exact trivialT_nonneg (Real.log_nonneg ht.1)
  have hL : L = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have halg : x / 2 - (7 / 3 * firstLiMass) * Real.sqrt x -
      (1 + Real.log Real.pi) -
      (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        4 / 3 * firstLiMass) / x =
      x / 2 - (3 / 2 + Real.eulerMascheroniConstant) / x -
        (7 * C / 3 * Real.sqrt x - 4 * C / (3 * x)) - L +
          2 * L / x - (1 - Real.log 2) := by
    dsimp only [C]
    rw [hL, Real.log_mul (by norm_num) Real.pi_ne_zero]
    field_simp
    ; ring
  rw [halg]
  have hb' := (abs_le.mp hb).1
  dsimp only [C, L, T] at *
  linear_combination hb' + hTbound + hTnonneg

/-- An explicit lower bound retaining the actual zero mass and both boundary gains. -/
theorem smoothedMangoldt_explicit_lower {x : ℝ}
    (hRH : 1 < x → RiemannHypothesis) (hx : 1 ≤ x) :
    x / 2 - (7 / 3 * firstLiMass) * Real.sqrt x - (1 + Real.log Real.pi) -
      (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        4 / 3 * firstLiMass) / x ≤ smoothedMangoldt x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have hL : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
      Real.log_mul (by norm_num) Real.pi_ne_zero
    have hm := firstLiMass_split
    have hp := firstLiMass_pos
    have hn := smoothedMangoldt_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    simp only [Real.sqrt_one, mul_one, div_one]
    rw [hL]
    linarith
  · exact smoothed_explicit_lower_gt_one (hRH hx) hx

private lemma smoothed_lower_of_subset {x : ℝ} (hx : 0 < x) (s : Finset ℕ)
    (w : ℕ → ℝ) (hs : ∀ n ∈ s, (n : ℝ) ≤ x)
    (hw : ∀ n ∈ s, w n ≤ ArithmeticFunction.vonMangoldt n) :
    (∑ n ∈ s, w n * (1 - (n : ℝ) / x)) ≤ smoothedMangoldt x := by
  rw [smoothed_eq_max_sum hx]
  calc
    _ ≤ ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * max (1 - (n : ℝ) / x) 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnonneg : 0 ≤ 1 - (n : ℝ) / x := sub_nonneg.mpr ((div_le_one hx).mpr
        (hs n hn))
      rw [max_eq_left hnonneg]
      exact mul_le_mul_of_nonneg_right (hw n hn) hnonneg
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
          ((Nat.le_floor_iff hx.le).mpr (hs n hn)))
      · intro n _ _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

/-- The triangular lower bound holds at every real argument. -/
theorem smoothedMangoldt_lower {x : ℝ} (hRH : 10 < x → RiemannHypothesis) :
    x / 2 - Real.sqrt x ≤ smoothedMangoldt x := by
  by_cases hx : 0 ≤ x
  swap
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    simp only [smoothedMangoldt, Nat.ceil_eq_zero.mpr hx', Finset.range_zero,
      Finset.sum_empty, Real.sqrt_eq_zero_of_nonpos hx', sub_zero]
    linarith
  by_cases hx4 : x ≤ 4
  · exact small_range_bound hx hx4
  have hx4' : 4 ≤ x := (lt_of_not_ge hx4).le
  have hx0 : 0 < x := by linarith
  have h2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h3 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  by_cases hx10 : 10 < x
  · have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    norm_num only [Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero, ite_false,
      Nat.cast_ofNat] at hg
    rw [he] at hg
    norm_num [harmonic, Finset.sum_range_succ] at hg
    have hp : Real.log 3 < Real.log Real.pi :=
      Real.log_lt_log (by norm_num) Real.pi_gt_three
    have hm : firstLiMass < 1 / 8 := by
      rw [firstLiMass_split]
      linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
    have hpu : Real.log Real.pi < 6 / 5 := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.pi / 3)
      rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
      linarith [Real.pi_lt_d2, Real.log_three_lt_d9]
    have hL : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
      Real.log_mul (by norm_num) Real.pi_ne_zero
    have hc : 3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        4 / 3 * firstLiMass ≤ 0 := by
      rw [hL]
      linarith [Real.eulerMascheroniConstant_lt_two_thirds, firstLiMass_pos]
    have hs : (22 / 7 : ℝ) ≤ Real.sqrt x := by
      apply (Real.le_sqrt (by norm_num) hx).mpr
      nlinarith
    have hmass : (7 / 3 * firstLiMass) * Real.sqrt x ≤
        7 / 24 * Real.sqrt x :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg x)
    have ha := smoothedMangoldt_explicit_lower (fun _ => hRH hx10) (by linarith : 1 ≤ x)
    have hc' := div_nonpos_of_nonpos_of_nonneg hc hx
    linarith
  have hx10' : x ≤ 10 := le_of_not_gt hx10
  have hv2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hv3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have hv4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ (2 : ℕ) by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), hv2]
  have hv5 : ArithmeticFunction.vonMangoldt 5 = Real.log 5 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by decide)
  have h5 : (1 : ℝ) ≤ Real.log 5 :=
    h3.trans (Real.log_le_log (by norm_num) (by norm_num))
  have hs5 : (2 : ℝ) ≤ Real.sqrt 5 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hs10 : (3 : ℝ) ≤ Real.sqrt 10 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  by_cases hx5 : x ≤ 5
  · have hl : 7 / 3 - 7 / x ≤ smoothedMangoldt x := by
      have hh := smoothed_lower_of_subset hx0 {2, 3, 4}
        (fun n => if n = 3 then 1 else 2 / 3)
        (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
            rcases hn with rfl | rfl | rfl <;> norm_num <;> linarith)
        (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
            rcases hn with rfl | rfl | rfl <;> simp [hv2, hv3, hv4, h2, h3])
      norm_num [Finset.sum_insert, Finset.sum_singleton] at hh
      convert hh using 1; ring
    have he := affine_sqrt_ge_endpoints (A := 7 / 3) (B := 7)
      (by norm_num) (by norm_num : (0 : ℝ) < 4)
      (show x ∈ Icc 4 5 from ⟨hx4', hx5⟩)
    have ha : 0 ≤ (7 / 3 : ℝ) - 7 / 4 - 4 / 2 + Real.sqrt 4 := by norm_num
    have hb : 0 ≤ (7 / 3 : ℝ) - 7 / 5 - 5 / 2 + Real.sqrt 5 := by linarith
    have hm := (le_min ha hb).trans he
    linarith
  · have hx5' : 5 ≤ x := (lt_of_not_ge hx5).le
    have hl : 10 / 3 - 12 / x ≤ smoothedMangoldt x := by
      have hh := smoothed_lower_of_subset hx0 {2, 3, 4, 5}
        (fun n => if n = 3 ∨ n = 5 then 1 else 2 / 3)
        (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
            rcases hn with rfl | rfl | rfl | rfl <;> norm_num <;> linarith)
        (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn
            rcases hn with rfl | rfl | rfl | rfl <;> simp [hv2, hv3, hv4, hv5, h2, h3, h5])
      norm_num [Finset.sum_insert, Finset.sum_singleton] at hh
      convert hh using 1; ring
    have he := affine_sqrt_ge_endpoints (A := 10 / 3) (B := 12)
      (by norm_num) (by norm_num : (0 : ℝ) < 5)
      (show x ∈ Icc 5 10 from ⟨hx5', hx10'⟩)
    have ha : 0 ≤ (10 / 3 : ℝ) - 12 / 5 - 5 / 2 + Real.sqrt 5 := by linarith
    have hb : 0 ≤ (10 / 3 : ℝ) - 12 / 10 - 10 / 2 + Real.sqrt 10 := by linarith
    have hm := (le_min ha hb).trans he
    linarith

theorem principal_smoothedCharacterSum_eq {p : ℕ} (hp : p.Prime) :
    (D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p 1).re =
      smoothedMangoldt p := by
  classical
  unfold D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum smoothedMangoldt
  rw [Nat.ceil_natCast, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hu : IsUnit (n : ZMod p) :=
    (ZMod.isUnit_iff_coprime n p).2
      (Nat.coprime_of_lt_prime hn0 (Finset.mem_range.mp hn) hp).symm
  rw [MulChar.one_apply hu, mul_one]
  simp

/-- RH supplies the actual principal-character term used by the sieve. -/
theorem principal_smoothedCharacterSum_lower {p : ℕ} (hp : p.Prime)
    (hRH : 10 ≤ (p : ℝ) → RiemannHypothesis) :
    (p : ℝ) / 2 - Real.sqrt p ≤
      (D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p 1).re := by
  rw [principal_smoothedCharacterSum_eq hp]
  exact smoothedMangoldt_lower (fun ht => hRH ht.le)

end D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
