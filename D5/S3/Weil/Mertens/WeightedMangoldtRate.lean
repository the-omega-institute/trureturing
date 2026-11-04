/- GID: D5/S3/Weil/Mertens/WeightedMangoldtRate
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/WeightedMangoldtRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unconditional stretched-exponential rate for the actual inclusive Mangoldt error. -/

import D5.S3.Weil.Mertens.WeightedPrimeLimit

/-!
The arithmetic suppliers are the existing unconditional MediumPNT, the proved
absolute integrability of the actual Chebyshev error kernel, and the complete
Euler-normalized tail identity. No stronger external PNT is imported. The new
estimate extracts half of the exponential decay uniformly over the whole tail;
the other half is integrable after logarithmic substitution.

The conclusion uses the original E₁Λ, not a supplied or abstract error function.
Its sum is over 0 < n <= floorNat(x); it retains every prime power and equality
at integer cutoffs. This endpoint alone proves neither N(D)=o(D) nor RH.
-/

namespace D5.S3.Weil.Mertens.WeightedMangoldtRate

open Real Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

def rate (c x : ℝ) : ℝ :=
  Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

def weight (c u : ℝ) : ℝ := rate c u / u

private lemma rate_pos (c x : ℝ) : 0 < rate c x := Real.exp_pos _

private lemma rate_double (c x : ℝ) :
    rate (2 * c) x = rate c x * rate c x := by
  unfold rate
  rw [← Real.exp_add]
  congr 1
  ring

private lemma rate_antitone {c x u : ℝ} (hc : 0 < c) (hx : 1 ≤ x)
    (hxu : x ≤ u) : rate c u ≤ rate c x := by
  have hpow : (Real.log x) ^ ((1 : ℝ) / 10) ≤
      (Real.log u) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (Real.log_nonneg hx)
      (Real.log_le_log (zero_lt_one.trans_le hx) hxu) (by norm_num)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hpow (by linarith : -c ≤ 0))

private lemma rate_double_le {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    rate (2 * c) x ≤ rate c x := by
  have hpow : 0 ≤ (Real.log x) ^ ((1 : ℝ) / 10) :=
    Real.rpow_nonneg (Real.log_nonneg hx) _
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hc.le hpow]

private lemma weight_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (weight c) (Ioi 1) := by
  change IntegrableOn
    (fun u : ℝ => Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) / u) (Ioi 1)
  have hexp : IntegrableOn
      (fun v : ℝ => Real.exp (-c * v ^ ((1 : ℝ) / 10))) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (0 : ℝ)) (p := (1 : ℝ) / 10) (b := c)
        (by norm_num) (by norm_num) hc)
  simpa only [Real.log_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (integrableOn_comp_log_Ioi
      (fun v : ℝ => Real.exp (-c * v ^ ((1 : ℝ) / 10))) one_pos).mpr
      (by simpa only [Real.log_one] using hexp)

private lemma weight_mass_nonneg (c : ℝ) :
    0 ≤ ∫ u in Ioi 1, weight c u := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact div_nonneg (rate_pos c u).le (zero_lt_one.trans hu).le

private lemma weight_tail_le_mass {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    (∫ u in Ioi x, weight c u) ≤ ∫ u in Ioi 1, weight c u := by
  refine setIntegral_mono_set (weight_integrable hc) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact div_nonneg (rate_pos c u).le (zero_lt_one.trans hu).le
  · exact ae_of_all _ (fun u hu => (Ioi_subset_Ioi hx) hu)

lemma chebyshev_tail_bound {c D X x : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hX : 2 ≤ X) (hx : X ≤ x)
    (hpsi : ∀ u ≥ X,
      |Chebyshev.psi u - u| ≤ D * (u * rate (2 * c) u)) :
    |∫ u in Ioi x, (Chebyshev.psi u - u) / u ^ 2| ≤
      D * (∫ u in Ioi 1, weight c u) * rate c x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hKi : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Ioi x) :=
    WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hx1)
  have hwi : IntegrableOn (weight c) (Ioi x) :=
    (weight_integrable hc).mono_set (Ioi_subset_Ioi hx1)
  have hdom (u : ℝ) (hu : u ∈ Ioi x) :
      |(Chebyshev.psi u - u) / u ^ 2| ≤ (D * rate c x) * weight c u := by
    have hu0 : 0 < u := (zero_lt_one.trans_le hx1).trans hu
    have hfactor : rate (2 * c) u ≤ rate c x * rate c u := by
      rw [rate_double]
      exact mul_le_mul_of_nonneg_right (rate_antitone hc hx1 hu.le) (rate_pos c u).le
    calc
      _ = |Chebyshev.psi u - u| / u ^ 2 := by
        rw [abs_div, abs_of_nonneg (sq_nonneg u)]
      _ ≤ (D * (u * rate (2 * c) u)) / u ^ 2 :=
        div_le_div_of_nonneg_right (hpsi u (hx.trans hu.le)) (sq_nonneg u)
      _ = D * rate (2 * c) u / u := by
        field_simp [hu0.ne']
      _ ≤ D * (rate c x * rate c u) / u :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hD) hu0.le
      _ = (D * rate c x) * weight c u := by unfold weight; ring
  calc
    _ ≤ ∫ u in Ioi x, |(Chebyshev.psi u - u) / u ^ 2| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioi x, (D * rate c x) * weight c u :=
      setIntegral_mono_on hKi.abs (hwi.const_mul _) measurableSet_Ioi hdom
    _ = (D * rate c x) * ∫ u in Ioi x, weight c u := integral_const_mul _ _
    _ ≤ (D * rate c x) * ∫ u in Ioi 1, weight c u :=
      mul_le_mul_of_nonneg_left (weight_tail_le_mass hc hx1)
        (mul_nonneg hD (rate_pos c x).le)
    _ = _ := by ring

/-- Unconditionally, the actual inclusive weighted Mangoldt error has a
stretched-exponential rate with exponent 1/10. All constants are supplied by
the proof; no rate, integrability, zero-location, or RH premise remains. -/
theorem E1Lambda_stretched_exponential :
    ∃ c > 0, ∃ C > 0, ∃ X ≥ (2 : ℝ), ∀ x ≥ X,
      |_root_.Mertens.E₁Λ x + Real.eulerMascheroniConstant| ≤
        C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c₀, hc₀, hO⟩ := MediumPNT
  obtain ⟨D, hD, hbound⟩ := isBigO_iff'.mp hO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hbound
  let X : ℝ := max A 2
  let c : ℝ := c₀ / 2
  let J : ℝ := ∫ u in Ioi 1, weight c u
  have hX : (2 : ℝ) ≤ X := le_max_right _ _
  have hc : 0 < c := by dsimp [c]; positivity
  have hdouble : 2 * c = c₀ := by dsimp [c]; ring
  have hJ : 0 ≤ J := weight_mass_nonneg c
  have hpsi (u : ℝ) (hu : X ≤ u) :
      |Chebyshev.psi u - u| ≤ D * (u * rate (2 * c) u) := by
    have hu0 : 0 < u := by linarith
    have huA : A ≤ u := (le_max_left A 2).trans hu
    simpa only [rate, hdouble, Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul,
      abs_of_pos hu0, abs_of_pos (Real.exp_pos _)] using hA u huA
  refine ⟨c, hc, D * (1 + J), mul_pos hD (by linarith), X, hX, ?_⟩
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := hX.trans hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hpoint : |(Chebyshev.psi x - x) / x| ≤ D * rate c x := by
    rw [abs_div, abs_of_pos hx0]
    calc
      _ ≤ (D * (x * rate (2 * c) x)) / x :=
        div_le_div_of_nonneg_right (hpsi x hx) hx0.le
      _ = D * rate (2 * c) x := by
        field_simp [hx0.ne']
      _ ≤ D * rate c x := mul_le_mul_of_nonneg_left (rate_double_le hc hx1) hD.le
  have htail := chebyshev_tail_bound hc hD.le hX hx hpsi
  have hid : _root_.Mertens.E₁Λ x + Real.eulerMascheroniConstant =
      (Chebyshev.psi x - x) / x - ∫ u in Ioi x, (Chebyshev.psi u - u) / u ^ 2 := by
    have h := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      WeightedPrimeLimit.chebyshev_error_kernel_integrable hx2
    have hdiv : (Chebyshev.psi x - x) / x = Chebyshev.psi x / x - 1 := by
      rw [sub_div, div_self hx0.ne']
    dsimp [_root_.Mertens.E₁Λ]
    rw [hdiv]
    linarith only [h]
  rw [hid]
  calc
    _ ≤ |(Chebyshev.psi x - x) / x| +
        |∫ u in Ioi x, (Chebyshev.psi u - u) / u ^ 2| := abs_sub _ _
    _ ≤ D * rate c x + D * J * rate c x := add_le_add hpoint htail
    _ = _ := by change D * rate c x + D * J * rate c x = D * (1 + J) * rate c x; ring

end
end D5.S3.Weil.Mertens.WeightedMangoldtRate
