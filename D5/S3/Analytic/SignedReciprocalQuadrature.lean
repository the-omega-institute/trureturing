/- GID: D5/S3/Analytic/SignedReciprocalQuadrature
   generality: G
   mirror-B: D5/B/S3/Analytic/SignedReciprocalQuadrature
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Infinite signed reciprocal quadrature and Abel bounds from integrable derivative variation. -/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators Interval
namespace D5.S3.Analytic.SignedReciprocalQuadrature

def weight (N : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ := h (N / x) / x ^ 2

def weightDeriv (N : ℝ) (h h' : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(2 * h (N / x) / x ^ 3) - N * h' (N / x) / x ^ 4

def variationDensity (h h' : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * t * |h t| + t ^ 2 * |h' t|

def variation (h h' : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..1, variationDensity h h' t

private lemma reciprocal_mem {N x : ℝ} (hN : 0 < N) (hx : N ≤ x) : N / x ∈ Icc (0 : ℝ) 1 := by
  have hxp : 0 < x := hN.trans_le hx
  exact ⟨(div_pos hN hxp).le, (div_le_one hxp).2 hx⟩

private lemma primitive_deriv {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

private lemma reciprocal_primitive_deriv {N : ℝ} (hN : 0 < N) {g : ℝ → ℝ}
    (hg : Continuous g) {x : ℝ} (hx : N ≤ x) :
    HasDerivAt (fun y => -(∫ t in (0 : ℝ)..N / y, g t) / N)
      (weight N g x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (hN.trans_le hx)
  have hi := (hasDerivAt_const x N).div (hasDerivAt_id x) hx0
  have hp := ((primitive_deriv hg (N / x)).comp x hi).neg.div_const N
  convert hp using 1 <;> dsimp [weight]
  field_simp [hN.ne', hx0]
  <;> ring

private lemma reciprocal_primitive_tendsto {N : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun x => -(∫ t in (0 : ℝ)..N / x, g t) / N) atTop (𝓝 0) := by
  have hp : Continuous (fun u => ∫ t in (0 : ℝ)..u, g t) :=
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous
  have hi : Tendsto (fun x : ℝ => N / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul N
  simpa using ((hp.continuousAt.tendsto.comp hi).neg.div_const N)

/-- Positive reciprocal substitution, including absolute integrability.
The proof uses FTC for the primitive of g. It assumes no monotonicity of g. -/
private lemma reciprocal_nonneg_integral {N : ℝ} (hN : 0 < N) {g : ℝ → ℝ}
    (hg : Continuous g) (hgp : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) :
    IntegrableOn (weight N g) (Ioi N) ∧
      (∫ x in Ioi N, weight N g x) = (∫ t in (0 : ℝ)..1, g t) / N := by
  have hd := fun x (hx : x ∈ Ici N) => reciprocal_primitive_deriv hN hg hx
  have hn (x : ℝ) (hx : x ∈ Ioi N) : 0 ≤ weight N g x :=
    div_nonneg (hgp _ (reciprocal_mem hN hx.le)) (sq_nonneg _)
  have ht := reciprocal_primitive_tendsto (N := N) hg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn ht, ?_⟩
  simpa only [div_self hN.ne', zero_sub, neg_div, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht

private lemma weight_continuousOn {N : ℝ} (hN : 0 < N) {h : ℝ → ℝ}
    (hh : Continuous h) : ContinuousOn (weight N h) (Ici N) := by
  unfold weight
  exact (hh.continuousOn.comp
    (continuousOn_const.div continuousOn_id (fun x hx => (hN.trans_le hx).ne'))
    (fun _ _ => mem_univ _)).div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero _ (hN.trans_le hx).ne')

private lemma reciprocal_integral {N : ℝ} (hN : 0 < N) {h : ℝ → ℝ} (hh : Continuous h) :
    IntegrableOn (weight N h) (Ioi N) ∧
      (∫ x in Ioi N, weight N h x) = (∫ t in (0 : ℝ)..1, h t) / N := by
  have hn := reciprocal_nonneg_integral hN hh.abs (fun _ _ => abs_nonneg _)
  have he (x : ℝ) : weight N (fun t => |h t|) x = ‖weight N h x‖ := by
    simp [weight, Real.norm_eq_abs, abs_div, abs_pow]
  have hint : IntegrableOn (weight N h) (Ioi N) := by
    apply (integrable_norm_iff
      (((weight_continuousOn hN hh).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).1
    have hf : weight N (fun t => |h t|) = (fun x => ‖weight N h x‖) := funext he
    rw [← hf]
    exact hn.1
  refine ⟨hint, ?_⟩
  simpa only [div_self hN.ne', zero_sub, neg_div, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx => reciprocal_primitive_deriv hN hh hx) hint
      (reciprocal_primitive_tendsto (N := N) hh)

private lemma weight_hasDerivAt {N : ℝ} (hN : 0 < N) {h h' : ℝ → ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' t) t)
    {x : ℝ} (hx : N ≤ x) : HasDerivAt (weight N h) (weightDeriv N h h' x) x := by
  have hx0 : x ≠ 0 := (hN.trans_le hx).ne'
  have hi := (hasDerivAt_const x N).div (hasDerivAt_id x) hx0
  have hp := ((hd _ (reciprocal_mem hN hx)).comp x hi).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)
  convert hp using 1
  · rfl
  · dsimp [weightDeriv]
    field_simp [hx0]
    <;> ring

private lemma weightDeriv_continuousOn {N : ℝ} (hN : 0 < N) {h h' : ℝ → ℝ}
    (hh : Continuous h) (hh' : Continuous h') :
    ContinuousOn (weightDeriv N h h') (Ici N) := by
  have hi : ContinuousOn (fun x : ℝ => N / x) (Ici N) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hN.trans_le hx).ne')
  unfold weightDeriv
  exact ((continuousOn_const.mul (hh.comp_continuousOn hi)).div
    (continuousOn_id.pow 3) (fun x hx => pow_ne_zero _ (hN.trans_le hx).ne')).neg.sub
    ((continuousOn_const.mul (hh'.comp_continuousOn hi)).div
      (continuousOn_id.pow 4) (fun x hx => pow_ne_zero _ (hN.trans_le hx).ne'))

/-- The exact derivative-integral variation estimate; no sup norm is used. -/
theorem derivative_integral_bound {N : ℝ} (hN : 0 < N) {h h' : ℝ → ℝ}
    (hh : Continuous h) (hh' : Continuous h') :
    IntegrableOn (weightDeriv N h h') (Ioi N) ∧
      (∫ x in Ioi N, |weightDeriv N h h' x|) ≤ variation h h' / N ^ 2 := by
  have hV : Continuous (variationDensity h h') := by unfold variationDensity; fun_prop
  have hVp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ variationDensity h h' t := by
    unfold variationDensity
    have ht0 : 0 ≤ t := ht.1
    positivity
  have hmajor := reciprocal_nonneg_integral hN hV hVp
  have hm : IntegrableOn (fun x => weight N (variationDensity h h') x / N) (Ioi N) :=
    hmajor.1.div_const N
  have hb (x : ℝ) (hx : x ∈ Ioi N) :
      |weightDeriv N h h' x| ≤ weight N (variationDensity h h') x / N := by
    have hxp := hN.trans hx
    have hx0 := hxp.ne'
    calc
      _ ≤ |2 * h (N / x) / x ^ 3| + |N * h' (N / x) / x ^ 4| := by
        have he : weightDeriv N h h' x =
            -(2 * h (N / x) / x ^ 3 + N * h' (N / x) / x ^ 4) := by
          unfold weightDeriv
          ring
        rw [he, abs_neg]
        exact abs_add_le _ _
      _ = _ := by
        simp only [abs_div, abs_mul, abs_of_pos hN, abs_of_pos hxp,
          abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), weight, variationDensity]
        field_simp [hN.ne', hx0]
        <;> ring
  have hc : ContinuousOn (weightDeriv N h h') (Ioi N) :=
    (weightDeriv_continuousOn hN hh hh').mono Ioi_subset_Ici_self
  have hint : IntegrableOn (weightDeriv N h h') (Ioi N) :=
    hm.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => by
        simpa only [Real.norm_eq_abs] using hb x hx))
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x in Ioi N, weight N (variationDensity h h') x / N :=
      integral_mono_ae hint.abs hm
        ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hb))
    _ = variation h h' / N ^ 2 := by
      rw [integral_div, hmajor.2]
      simp only [variation, div_div, pow_two]

private lemma weight_tendsto_zero {N : ℝ} {h : ℝ → ℝ} (hh : Continuous h) :
    Tendsto (weight N h) atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => N / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul N
  have ht := (hh.continuousAt.tendsto.comp hi).mul (tendsto_inv_atTop_zero.pow 2)
  change Tendsto (fun x : ℝ => h (N / x) / x^2) atTop (𝓝 0)
  simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow,
    zero_pow (by decide : 2 ≠ 0), mul_zero] using ht

lemma sample_summable {N : ℕ} (hN : 0 < N) {h : ℝ → ℝ} (hh : Continuous h) :
    Summable (fun j : ℕ => weight N h (N + j + 1 : ℕ)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hh.continuousOn
  have hCp : 0 ≤ C := (norm_nonneg (h 0)).trans (hC 0 (by norm_num))
  have hs : Summable (fun j : ℕ => 1 / ((N + j + 1 : ℕ) : ℝ) ^ 2) := by
    have hp := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2) :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2))
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).2 hp
  apply (hs.mul_left C).of_norm_bounded
  intro j
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (N : ℝ) ≤ ((N + j + 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N+j+1 by omega)
  simp only [weight, norm_div, Real.norm_eq_abs, abs_pow, sq_abs]
  simpa only [div_eq_mul_inv, mul_one, one_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hC _ (reciprocal_mem hnR hx))
      (inv_nonneg.mpr (sq_nonneg (((N+j+1 : ℕ) : ℝ))))

/-- A signed one-cell right endpoint estimate, proved directly from FTC. -/
private lemma cell_error {a : ℝ} {w v : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a (a+1))) (hv : ContinuousOn v (Icc a (a+1)))
    (hd : ∀ x ∈ Icc a (a+1), HasDerivAt w (v x) x) :
    |w (a+1) - ∫ x in a..a+1, w x| ≤ ∫ x in a..a+1, |v x| := by
  have hi : IntervalIntegrable w volume a (a+1) := hw.intervalIntegrable_of_Icc (by linarith : a ≤ a+1)
  have hvi : IntervalIntegrable v volume a (a+1) := hv.intervalIntegrable_of_Icc (by linarith : a ≤ a+1)
  have hpoint (x : ℝ) (hx : x ∈ Icc a (a+1)) :
      |w (a+1) - w x| ≤ ∫ t in a..a+1, |v t| := by
    have hsmall : IntervalIntegrable v volume x (a+1) :=
      hvi.mono_set (by rw [uIcc_of_le hx.2, uIcc_of_le (by linarith : a ≤ a+1)]; exact Icc_subset_Icc hx.1 le_rfl)
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by rw [uIcc_of_le hx.2] at ht; exact ⟨hx.1.trans ht.1, ht.2⟩)) hsmall]
    exact (intervalIntegral.abs_integral_le_integral_abs hx.2).trans
      (intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
        (ae_of_all _ fun _ => abs_nonneg _) hvi.abs)
  calc
    _ = |∫ x in a..a+1, w (a+1) - w x| := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) hi]
      simp
    _ ≤ ∫ x in a..a+1, |w (a+1)-w x| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ _x in a..a+1, ∫ t in a..a+1, |v t| :=
      intervalIntegral.integral_mono_on (by linarith)
        (((continuousOn_const.sub hw).abs).intervalIntegrable_of_Icc (by linarith))
        intervalIntegrable_const hpoint
    _ = _ := by simp

private lemma local_integrable {a b : ℝ} {v : ℝ → ℝ} (hab : a ≤ b)
    (hv : IntegrableOn v (Ioi a)) : IntervalIntegrable v volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
  exact hv.mono_set (fun _ hx => hx.1)

private lemma local_le_global {a b : ℝ} (hab : a ≤ b) {v : ℝ → ℝ}
    (hv : IntegrableOn v (Ioi a)) :
    (∫ x in a..b, |v x|) ≤ ∫ x in Ioi a, |v x| := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set hv.abs (ae_of_all _ fun _ => abs_nonneg _)
    (Eventually.of_forall fun _ hx => hx.1)

/-- Infinite signed quadrature. No monotonicity premise occurs. -/
theorem right_endpoint_quadrature {N : ℕ} (hN : 0 < N) {h h' : ℝ → ℝ}
    (hh : Continuous h) (hh' : Continuous h')
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' t) t) :
    Summable (fun j : ℕ => weight N h (N+j+1 : ℕ)) ∧
    |(∑' j : ℕ, weight N h (N+j+1 : ℕ)) -
      (∫ t in (0 : ℝ)..1, h t) / N| ≤ variation h h' / (N : ℝ)^2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sample_summable hN hh
  have hw := reciprocal_integral hNR hh
  have hv := derivative_integral_bound hNR hh hh'
  let w := weight (N : ℝ) h
  let v := weightDeriv (N : ℝ) h h'
  have hc : ContinuousOn v (Ici (N : ℝ)) := weightDeriv_continuousOn hNR hh hh' 
  have hfinite (k : ℕ) :
      |(∑ j ∈ Finset.range k, w (N+j+1 : ℕ)) - ∫ x in (N : ℝ)..N+k, w x| ≤
        ∫ x in Ioi (N : ℝ), |v x| := by
    have hi (j : ℕ) : IntervalIntegrable w volume ((N+j : ℕ):ℝ) (N+j+1 : ℕ) :=
      ((weight_continuousOn hNR hh).mono (by
        rw [uIcc_of_le (by exact_mod_cast (show N+j ≤ N+j+1 by omega))]
        exact fun x hx => (show (N : ℝ) ≤ (N+j : ℕ) by exact_mod_cast (show N ≤ N+j by omega)).trans hx.1)).intervalIntegrable
    have hvi (j : ℕ) : IntervalIntegrable v volume ((N+j : ℕ):ℝ) (N+j+1 : ℕ) :=
      (hc.mono (by
        rw [uIcc_of_le (by exact_mod_cast (show N+j ≤ N+j+1 by omega))]
        exact fun x hx => (show (N : ℝ) ≤ (N+j : ℕ) by exact_mod_cast (show N ≤ N+j by omega)).trans hx.1)).intervalIntegrable
    have htel := intervalIntegral.sum_integral_adjacent_intervals (a := fun j => ((N+j : ℕ):ℝ))
      (fun j (_ : j < k) => hi j)
    have htelv := intervalIntegral.sum_integral_adjacent_intervals (a := fun j => ((N+j : ℕ):ℝ))
      (fun j (_ : j < k) => (hvi j).abs)
    simp only [Nat.add_zero, Nat.cast_add, Nat.cast_one] at htel htelv
    rw [← htel, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range k, |w (N+j+1 : ℕ) - ∫ x in (N:ℝ)+j..(N:ℝ)+(j+1), w x| :=
        by simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, add_assoc] using
          norm_sum_le (Finset.range k) (fun j => w (N+j+1 : ℕ) - ∫ x in (N:ℝ)+j..(N:ℝ)+(j+1), w x)
      _ ≤ ∑ j ∈ Finset.range k, ∫ x in (N:ℝ)+j..(N:ℝ)+(j+1), |v x| := by
        apply Finset.sum_le_sum
        intro j _
        have hj : (N:ℝ) ≤ (N:ℝ)+j := le_add_of_nonneg_right (Nat.cast_nonneg j)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          cell_error ((weight_continuousOn hNR hh).mono (fun _ hx => hj.trans hx.1))
            (hc.mono (fun _ hx => hj.trans hx.1))
            (fun x hx => weight_hasDerivAt hNR hd (hj.trans hx.1))
      _ = ∫ x in (N:ℝ)..N+k, |v x| := htelv
      _ ≤ _ := local_le_global (a := (N:ℝ)) (b := (N:ℝ)+k)
        (le_add_of_nonneg_right (Nat.cast_nonneg k)) hv.1
  have ht : Tendsto (fun k : ℕ => (N:ℝ)+k) atTop atTop :=
    tendsto_atTop_add_const_left _ (N:ℝ) tendsto_natCast_atTop_atTop
  have hl := ((hs.hasSum.tendsto_sum_nat.sub
    (intervalIntegral_tendsto_integral_Ioi (N:ℝ) hw.1 ht)).abs)
  rw [hw.2] at hl
  exact ⟨hs, (le_of_tendsto hl (Eventually.of_forall hfinite)).trans hv.2⟩

/-- Bounded prefix sums force bounded individual terms, without deleting signs. -/
private lemma term_bound_of_prefix {x : ℕ → ℝ} {D : ℝ}
    (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D) (j : ℕ) : |x j| ≤ 2*D := by
  have h0 := hb j
  have h1 := hb (j+1)
  rw [Finset.sum_range_succ] at h1
  calc
    |x j| = |((∑ i ∈ Finset.range j, x i)+x j) - ∑ i ∈ Finset.range j, x i| := by congr 1; ring
    _ ≤ |(∑ i ∈ Finset.range j, x i)+x j| + |∑ i ∈ Finset.range j, x i| := abs_sub _ _
    _ ≤ _ := by linarith

/-- Explicit vanishing of the finite Abel boundary, before taking the infinite sum. -/
private lemma abel_boundary_vanishes {x w : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D)
    (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun k => (∑ j ∈ Finset.range (k+1), x j) * w k) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun k => ?_) (by simpa using hw.norm.const_mul D)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb (k+1)) (norm_nonneg _)

/-- Signed Abel estimate with total variation. No |x_j| replaces a block moment. -/
theorem signed_weighted_reciprocal {N : ℕ} (hN : 0 < N) {h h' : ℝ → ℝ}
    (hh : Continuous h) (hh' : Continuous h')
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt h (h' t) t)
    {x : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D) :
    Summable (fun j : ℕ => x j * weight N h (N+j+1 : ℕ)) ∧
      |∑' j : ℕ, x j * weight N h (N+j+1 : ℕ)| ≤ D * variation h h' / (N:ℝ)^2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  let w : ℕ → ℝ := fun j => weight N h (N+j+1 : ℕ)
  let v : ℝ → ℝ := weightDeriv N h h'
  have hs := sample_summable hN hh
  have hsum : Summable (fun j => x j * w j) := by
    apply ((hs.norm).mul_left (2*D)).of_norm_bounded
    intro j
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (term_bound_of_prefix hb j) (abs_nonneg _)
  have hv := derivative_integral_bound hNR hh hh'
  have hc : ContinuousOn v (Ici (N:ℝ)) := weightDeriv_continuousOn hNR hh hh' 
  have hdiff (j : ℕ) : |w (j+1)-w j| ≤
      ∫ t in ((N+j+1 : ℕ):ℝ)..(N+j+2 : ℕ), |v t| := by
    have ha : (N:ℝ) ≤ ((N+j+1 : ℕ):ℝ) := by exact_mod_cast (show N ≤ N+j+1 by omega)
    have hab : ((N+j+1 : ℕ):ℝ) ≤ (N+j+2 : ℕ) := by exact_mod_cast (show N+j+1 ≤ N+j+2 by omega)
    have hi : IntervalIntegrable v volume (N+j+1 : ℕ) (N+j+2 : ℕ) :=
      (hc.mono (by rw [uIcc_of_le hab]; exact fun t ht => ha.trans ht.1)).intervalIntegrable
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => weight_hasDerivAt hNR hd (by rw [uIcc_of_le hab] at ht; exact ha.trans ht.1)) hi
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := v) hab
    rw [hf] at habs
    simpa only [w, show N+(j+1)+1 = N+j+2 by omega] using habs
  have hvar (k : ℕ) : (∑ j ∈ Finset.range k, |w (j+1)-w j|) ≤
      ∫ t in Ioi (N:ℝ), |v t| := by
    have ht := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun j => ((N+j+1 : ℕ):ℝ)) (n := k)
      (fun j _ => ((hc.abs.mono (by
        rw [uIcc_of_le (by exact_mod_cast (show N+j+1 ≤ N+(j+1)+1 by omega))]
        exact fun t ht => (show (N : ℝ) ≤ (N+j+1 : ℕ) by exact_mod_cast (show N ≤ N+j+1 by omega)).trans ht.1)).intervalIntegrable))
    calc
      _ ≤ ∑ j ∈ Finset.range k, ∫ t in (N+j+1 : ℕ)..(N+(j+1)+1 : ℕ), |v t| :=
        Finset.sum_le_sum (fun j _ => by simpa [Nat.add_assoc] using hdiff j)
      _ = ∫ t in (N+1 : ℕ)..(N+k+1 : ℕ), |v t| := by simpa using ht
      _ ≤ ∫ t in (N:ℝ)..(N+k+1 : ℕ), |v t| :=
        intervalIntegral.integral_mono_interval (by exact_mod_cast (show N ≤ N+1 by omega))
          (by exact_mod_cast (show N+1 ≤ N+k+1 by omega)) le_rfl
          (ae_of_all _ fun _ => abs_nonneg _) (local_integrable (a := (N:ℝ)) (b := ((N+k+1:ℕ):ℝ))
            (by exact_mod_cast (show N ≤ N+k+1 by omega)) hv.1).abs
      _ ≤ _ := local_le_global (a := (N:ℝ)) (b := ((N+k+1:ℕ):ℝ))
        (by exact_mod_cast (show N ≤ N+k+1 by omega)) hv.1
  have hfinite (k : ℕ) : |∑ j ∈ Finset.range (k+1), x j*w j| ≤
      |(∑ j ∈ Finset.range (k+1), x j)*w k| + D*(∫ t in Ioi (N:ℝ), |v t|) := by
    have hp := Finset.sum_range_by_parts' x w (k+1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hp
    rw [hp]
    refine (abs_sub _ _).trans (add_le_add_right ?_ _)
    calc
      _ ≤ ∑ j ∈ Finset.range k, |(∑ i ∈ Finset.range (j+1), x i)*(w (j+1)-w j)| :=
        by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (Finset.range k)
              (fun j => (∑ i ∈ Finset.range (j+1), x i)*(w (j+1)-w j)))
      _ ≤ ∑ j ∈ Finset.range k, D*|w (j+1)-w j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hb (j+1)) (abs_nonneg _)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hvar k) hD
  have hwt : Tendsto w atTop (𝓝 0) := (weight_tendsto_zero hh).comp (by
    have ht : Tendsto (fun j : ℕ => (j:ℝ)+((N:ℝ)+1)) atTop atTop :=
      tendsto_atTop_add_const_right _ ((N:ℝ)+1) tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add,Nat.cast_one,add_comm,add_left_comm,add_assoc] using ht)
  have hbdy := (abel_boundary_vanishes hD hb hwt).abs
  have hlim := (hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).abs
  have hbound := le_of_tendsto_of_tendsto hlim
    (by simpa using hbdy.add_const (D*(∫ t in Ioi (N:ℝ), |v t|)))
    (Eventually.of_forall hfinite)
  refine ⟨hsum, hbound.trans ?_⟩
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hv.2 hD

end D5.S3.Analytic.SignedReciprocalQuadrature
