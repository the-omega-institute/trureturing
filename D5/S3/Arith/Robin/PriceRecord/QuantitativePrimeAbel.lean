/- GID: D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Real-endpoint factorial prime-counting expansion from MediumPNT. -/

/-! Native real-endpoint quantitative prime-counting expansion. The only analytic transfer helper retained here is the consumed finite-FTC ratio lemma below. -/
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundaryAbel
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open Real Filter MeasureTheory Asymptotics Set
open scoped Topology
open PrimeBoundaryAbel

/-- Tail integral comparison with an actual differentiable primitive. The
fixed initial segment is paid by constants divided by G(x), not discarded. -/
private lemma integral_ratio_of_derivative_ratio {a : ℝ} {f G G' : ℝ → ℝ}
    (hfi : ∀ x, a ≤ x → IntervalIntegrable f volume a x)
    (hgi : ∀ x, a ≤ x → IntervalIntegrable G' volume a x)
    (hder : ∀ x, a ≤ x → HasDerivAt G (G' x) x)
    (hG : Tendsto G atTop atTop)
    (hpos : ∀ᶠ x : ℝ in atTop, 0 < G' x)
    (hratio : Tendsto (fun x => f x / G' x) atTop (𝓝 1)) :
    Tendsto (fun x => (∫ u in a..x, f u) / G x) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      0 < G' x ∧ |f x / G' x - 1| < η := by
    filter_upwards [hpos, (Metric.tendsto_nhds.mp hratio) η hη] with x hp hx
    exact ⟨hp, by simpa only [Real.dist_eq] using hx⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  let T := max a T₀
  have haT : a ≤ T := le_max_left _ _
  have htail (x : ℝ) (hTx : T ≤ x) :
      (1 - η) * G' x ≤ f x ∧ f x ≤ (1 + η) * G' x := by
    obtain ⟨hxp, hx⟩ := hT₀ x ((le_max_right _ _).trans hTx)
    obtain ⟨hl, hu⟩ := abs_lt.mp hx
    constructor
    · have h : 1 - η ≤ f x / G' x := by linarith only [hl]
      exact (le_div_iff₀ hxp).mp h
    · have h : f x / G' x ≤ 1 + η := by linarith only [hu]
      exact (div_le_iff₀ hxp).mp h
  let C₋ : ℝ := (∫ u in a..T, f u) - (1 - η) * G T
  let C₊ : ℝ := (∫ u in a..T, f u) - (1 + η) * G T
  have hC₋ : Tendsto (fun x => C₋ / G x) atTop (𝓝 0) := hG.const_div_atTop C₋
  have hC₊ : Tendsto (fun x => C₊ / G x) atTop (𝓝 0) := hG.const_div_atTop C₊
  filter_upwards [eventually_ge_atTop T, hG.eventually_gt_atTop 0,
    (Metric.tendsto_nhds.mp hC₋) η hη,
    (Metric.tendsto_nhds.mp hC₊) η hη] with x hTx hGx hCm hCp
  have hax : a ≤ x := haT.trans hTx
  have hfx : IntervalIntegrable f volume T x := (hfi T haT).symm.trans (hfi x hax)
  have hgx : IntervalIntegrable G' volume T x := (hgi T haT).symm.trans (hgi x hax)
  have hFTC : (∫ u in T..x, G' u) = G x - G T := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hgx
    intro u hu
    rw [uIcc_of_le hTx] at hu
    exact hder u (haT.trans hu.1)
  have hlo : (1 - η) * (G x - G T) ≤ ∫ u in T..x, f u := by
    rw [← hFTC, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hTx (hgx.const_mul _) hfx
    intro u hu
    exact (htail u hu.1).1
  have hhi : (∫ u in T..x, f u) ≤ (1 + η) * (G x - G T) := by
    rw [← hFTC, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hTx hfx (hgx.const_mul _)
    intro u hu
    exact (htail u hu.1).2
  have hsplit : (∫ u in a..x, f u) = (∫ u in a..T, f u) + ∫ u in T..x, f u :=
    (intervalIntegral.integral_add_adjacent_intervals (hfi T haT) hfx).symm
  have hlower : (1 - η) + C₋ / G x ≤ (∫ u in a..x, f u) / G x := by
    have hlinear : (1 - η) * G x + C₋ ≤ ∫ u in a..x, f u := by
      rw [hsplit]
      dsimp only [C₋]
      nlinarith only [hlo]
    have h := div_le_div_of_nonneg_right hlinear hGx.le
    convert h using 1 <;> field_simp [hGx.ne'] <;> ring
  have hupper : (∫ u in a..x, f u) / G x ≤ (1 + η) + C₊ / G x := by
    have hlinear : (∫ u in a..x, f u) ≤ (1 + η) * G x + C₊ := by
      rw [hsplit]
      dsimp only [C₊]
      nlinarith only [hhi]
    have h := div_le_div_of_nonneg_right hlinear hGx.le
    convert h using 1 <;> field_simp [hGx.ne'] <;> ring
  have hm : |C₋ / G x| < η := by simpa only [Real.dist_eq, sub_zero] using hCm
  have hp : |C₊ / G x| < η := by simpa only [Real.dist_eq, sub_zero] using hCp
  rw [Real.dist_eq]
  apply abs_lt.mpr
  dsimp only [η] at *
  constructor <;> linarith only [hε, hlower, hupper, (abs_lt.mp hm).1, (abs_lt.mp hp).2]


/-- MediumPNT is a REAL-variable psi estimate with exponent 1/10.
The psi-minus-theta sqrt estimate pays prime powers, for every fixed N. -/
theorem theta_error_log_power (N : ℕ) :
    (fun x : ℝ => Chebyshev.theta x - x) =o[atTop]
      (fun x : ℝ => x / log x ^ N) := by
  obtain ⟨c, hc, hpnt⟩ := _root_.MediumPNT
  have hexp : Tendsto
      (fun x : ℝ => log x ^ N * exp (-c * log x ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (10 * (N : ℝ)) c hc).comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        tendsto_log_atTop)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [Function.comp_def]
    rw [← rpow_mul (log_pos hx).le]
    rw [show (1 / 10 : ℝ) * (10 * (N : ℝ)) = (N : ℝ) by ring,
      rpow_natCast]
  have hmodel :
      (fun x : ℝ => x * exp (-c * log x ^ (1 / 10 : ℝ))) =o[atTop]
        (fun x : ℝ => x / log x ^ N) := by
    apply isLittleO_of_tendsto'
      ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => by
        exact fun h => False.elim
          ((div_ne_zero (by linarith : x ≠ 0)
            (pow_ne_zero N (log_pos hx).ne')) h))
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    field_simp [show x ≠ 0 by linarith, (log_pos hx).ne']
  have hsqrt : sqrt =o[atTop] (fun x : ℝ => x / log x ^ N) := by
    apply isLittleO_of_tendsto'
      ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => by
        exact fun h => False.elim
          ((div_ne_zero (by linarith : x ≠ 0)
            (pow_ne_zero N (log_pos hx).ne')) h))
    have h := (isLittleO_log_rpow_rpow_atTop N
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simp only [rpow_natCast, ← sqrt_eq_rpow] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hs0 := (sqrt_pos.mpr hx0).ne'
    field_simp [hx0.ne', (log_pos hx).ne', hs0]
    rw [sq_sqrt hx0.le]
  have h := (hpnt.trans_isLittleO hmodel).sub
    (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt)
  apply h.congr_left
  intro x
  simp only [Pi.sub_apply, id_eq]
  ring

def countingPolynomial (x : ℝ) : ℝ :=
  x * (1 / log x + 1 / log x ^ 2 + 2 / log x ^ 3 + 6 / log x ^ 4)

private def countPrimitive (x : ℝ) : ℝ :=
  x * (1 / log x ^ 2 + 2 / log x ^ 3 + 6 / log x ^ 4)

private def countPrimitiveDeriv (x : ℝ) : ℝ :=
  1 / log x ^ 2 - 24 / log x ^ 5

private lemma countPrimitive_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt countPrimitive (countPrimitiveDeriv x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hd (k : ℕ) : HasDerivAt (fun u : ℝ => 1 / log u ^ k)
      (-(k : ℝ) * log x ^ (k - 1) * x⁻¹ / (log x ^ k) ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div
      ((hasDerivAt_log hx0).pow k) (pow_ne_zero k hl) using 1 <;> ring
  have h := (hasDerivAt_id x).mul
    (((hd 2).add ((hd 3).const_mul 2)).add ((hd 4).const_mul 6))
  convert h using 1 <;> dsimp only [countPrimitive, countPrimitiveDeriv]
  · funext u; ring
  · norm_num
    field_simp [hx0, hl]
    <;> ring

private lemma log_power_over_id_zero (k : ℕ) :
    Tendsto (fun x : ℝ => log x ^ k / x) atTop (𝓝 0) := by
  simpa only [rpow_natCast, rpow_one] using
    (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero

private lemma model_atTop (k : ℕ) :
    Tendsto (fun x : ℝ => x / log x ^ k) atTop atTop := by
  have hp : ∀ᶠ x : ℝ in atTop, 0 < log x ^ k / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (log_pos hx) k) (by linarith)
  have hw := tendsto_nhdsWithin_iff.mpr ⟨log_power_over_id_zero k, hp⟩
  simpa only [inv_div] using tendsto_inv_nhdsGT_zero.comp hw

/-- Quantified REAL-endpoint expansion, including the fourth factorial
coefficient and the next residual limit 24. Hence the requested O(l^-4)
relative error follows, without an assumed prime-counting asymptotic. -/
theorem prime_counting_four_terms :
    Tendsto (fun x : ℝ =>
      (primeCount x - countingPolynomial x) / (x / log x ^ 5))
      atTop (𝓝 24) := by
  let f : ℝ → ℝ := fun u => Chebyshev.theta u / (u * log u ^ 2)
  let e : ℝ → ℝ := fun u => (f u - countPrimitiveDeriv u) / 24
  let G : ℝ → ℝ := fun u => u / log u ^ 5
  let G' : ℝ → ℝ := fun u => (log u - 5) / log u ^ 6
  have hfi (x : ℝ) (hx : 2 ≤ x) : IntervalIntegrable f volume 2 x := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hc (x : ℝ) (hx : 2 ≤ x) :
      IntervalIntegrable countPrimitiveDeriv volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hx
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    have hl : log u ≠ 0 := (log_pos (by linarith [hu.1] : 1 < u)).ne'
    exact ContinuousAt.continuousWithinAt (by
      dsimp only [countPrimitiveDeriv]; fun_prop)
  have he (x : ℝ) (hx : 2 ≤ x) : IntervalIntegrable e volume 2 x :=
    ((hfi x hx).sub (hc x hx)).div_const 24
  have hgi (x : ℝ) (hx : 2 ≤ x) : IntervalIntegrable G' volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hx
    intro u hu
    have hl : log u ≠ 0 := (log_pos (by linarith [hu.1] : 1 < u)).ne'
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    exact ContinuousAt.continuousWithinAt (by dsimp only [G']; fun_prop)
  have hd (u : ℝ) (hu : 2 ≤ u) : HasDerivAt G (G' u) u := by
    have hu0 : u ≠ 0 := ne_of_gt (by linarith)
    have hl : log u ≠ 0 := (log_pos (by linarith : 1 < u)).ne'
    convert (hasDerivAt_id u).div ((hasDerivAt_log hu0).pow 5)
      (pow_ne_zero 5 hl) using 1 <;> dsimp only [G, G'] <;>
      field_simp [hu0, hl] <;> ring
  have hgp : ∀ᶠ u : ℝ in atTop, 0 < G' u := by
    filter_upwards [tendsto_log_atTop.eventually_gt_atTop 5] with u hu
    exact div_pos (by linarith) (pow_pos (by linarith) 6)
  have hr : Tendsto (fun u => e u / G' u) atTop (𝓝 1) := by
    have hz := (theta_error_log_power 3).tendsto_div_nhds_zero
    have hi := tendsto_log_atTop.const_div_atTop 5
    have h := ((hz.div_const 24).add_const 1).div
      (tendsto_const_nhds.sub hi) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    norm_num only [zero_div, zero_add, sub_zero, div_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      tendsto_log_atTop.eventually_gt_atTop 5] with u hu hlu
    dsimp only [e, f, G', countPrimitiveDeriv]
    field_simp [show u ≠ 0 by linarith, (log_pos hu).ne',
      show log u - 5 ≠ 0 by linarith]
    <;> ring
  have hi := integral_ratio_of_derivative_ratio he hgi hd (model_atTop 5) hgp hr
  have hF : ∀ x : ℝ, 2 ≤ x →
      (∫ u in 2..x, e u) =
        ((∫ u in 2..x, f u) - countPrimitive x + countPrimitive 2) / 24 := by
    intro x hx
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => countPrimitive_deriv (by
        rw [uIcc_of_le hx] at hu; linarith [hu.1])) (hc x hx)
    dsimp only [e]
    rw [intervalIntegral.integral_div_const,
      intervalIntegral.integral_sub (hfi x hx) (hc x hx), hFTC]
    ring
  have hz := (theta_error_log_power 4).tendsto_div_nhds_zero
  have hconst := (model_atTop 5).const_div_atTop (countPrimitive 2)
  have h := hz.add ((hi.const_mul 24).sub hconst)
  norm_num only [zero_add, mul_one, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [hF x hx]
  dsimp only [primeCount]
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx]
  dsimp only [G, countingPolynomial, countPrimitive]
  have hl : log x ≠ 0 := (log_pos (by linarith : 1 < x)).ne'
  field_simp [show x ≠ 0 by linarith, hl]
  <;> ring

/-- A single threshold controls every later real endpoint, including a
moving r and all t in [r,P]. This is consumed by the finite Abel estimate. -/
theorem prime_counting_four_terms_uniform :
    ∃ X : ℝ, 1 < X ∧ ∀ x : ℝ, X ≤ x →
      |primeCount x - countingPolynomial x| ≤ 25 * x / log x ^ 5 := by
  have h := prime_counting_four_terms.eventually
    (Metric.ball_mem_nhds (24 : ℝ) (by norm_num : (0 : ℝ) < 1))
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  refine ⟨max X 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) ((le_max_right X 2).trans hx)
  have hq : |(primeCount x - countingPolynomial x) / (x / log x ^ 5) - 24| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hX x ((le_max_left _ _).trans hx)
  have hm := abs_le.mp (le_of_lt hq)
  have hg : 0 < x / log x ^ 5 := div_pos (by linarith) (pow_pos (log_pos hx1) 5)
  have hnorm : |(primeCount x - countingPolynomial x) / (x / log x ^ 5)| ≤ 25 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_div, abs_of_pos hg] at hnorm
  have hh := (div_le_iff₀ hg).mp hnorm
  convert hh using 1 <;> ring

end D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
