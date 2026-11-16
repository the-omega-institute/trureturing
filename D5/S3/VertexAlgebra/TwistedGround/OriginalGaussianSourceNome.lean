/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceNome
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceNome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact original Gaussian source nome on the full open real unit interval. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
import D5.S3.Analytic.OriginalHalfBinomialWronskian
import D5.S3.Analytic.OriginalHalfBinomialEndpoint

/-! The genuine source derivative and the original period endpoint fix the exact real nome. -/

noncomputable section
open scoped Topology
open Filter Set
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome
open OriginalGaussianResolvent OriginalGaussianDifferentiation OriginalGaussianSourceMeans
open OriginalGaussianSourceDerivative OriginalGaussianAllIndexResolvent
open D5.S3.Analytic.OriginalHalfBinomialWronskian

private def derivedNome (r : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (2 * sourceConstant (Real.sqrt r : ℂ)) / 16

private def periodNome (r : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * tau (r : ℂ))

private lemma periodNome_eq (r : ℝ) :
    periodNome r = (Real.exp (-Real.pi * F (1 - r) / F r) : ℂ) := by
  rw [periodNome, Complex.ofReal_exp]
  congr 1
  rw [tau, show 1 - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
    period_ofReal, period_ofReal]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private lemma periodNome_ne_zero (r : ℝ) : periodNome r ≠ 0 :=
  Complex.exp_ne_zero _

private lemma derivedNome_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt derivedNome
      (derivedNome r / ((r : ℂ) * (1 - (r : ℂ)) * (F r : ℂ) ^ 2)) r := by
  have h := ((hasDerivAt_id r).ofReal_comp.mul
    ((hasDerivAt_radial_sourceConstant hr hr1).const_mul 2).cexp).div_const 16
  apply h.congr_deriv
  dsimp only [derivedNome, id]
  push_cast
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : 1 - (r : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hr1).ne'
  have hF0 : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)).ne'
  field_simp [hr0, hc0, hF0]
  <;> ring

private lemma periodNome_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt periodNome
      (periodNome r / ((r : ℂ) * (1 - (r : ℂ)) * (F r : ℂ) ^ 2)) r := by
  have hx : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hr] using hr1
  have hc : ‖1 - (r : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1)]
    linarith
  have h := ((original_tau_hasDerivAt hx hc).2.comp_ofReal.const_mul
    ((Real.pi : ℂ) * Complex.I)).cexp
  apply h.congr_deriv
  rw [period_ofReal]
  dsimp only [periodNome]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : 1 - (r : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hr1).ne'
  have hF0 : (F r : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)).ne'
  field_simp [hpi, hr0, hc0, hF0]
  <;> simp [Complex.I_sq]

private lemma source_tendsto_zero :
    Tendsto (fun r : ℝ => sourceConstant (Real.sqrt r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hz : ‖(0 : ℂ)‖ < 1 := by simp
  have hs : sourceFamily 0 0 = 0 := by
    ext n
    simp [sourceFamily_apply 0 hz]
  have hroot : ContinuousAt (fun r : ℝ => (Real.sqrt r : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt
  have hroot' : Tendsto (fun r : ℝ => (Real.sqrt r : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hroot.tendsto
  have hv := (hasDerivAt_sourceFamily 0 hz).continuousAt.tendsto.comp hroot'
  have hc := (hasDerivAt_columnSeries hz).continuousAt.tendsto.comp hroot'
  have hp := Filter.Tendsto.inner (𝕜 := ℂ) hv.star hc
  have ht : Tendsto (fun r : ℝ =>
      innerSL ℂ (star (sourceFamily 0 (Real.sqrt r : ℂ)))
        (columnSeries (Real.sqrt r : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa [hs] using hp.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hu] with r hr
  exact (source_pairings_explicit (radial_norm_lt_one hr) false 0).2.2.2

private lemma derivedNome_quotient_tendsto :
    Tendsto (fun r : ℝ => derivedNome r / (r : ℂ)) (𝓝[>] 0) (𝓝 (1 / 16)) := by
  have h := (((tendsto_const_nhds (x := (2 : ℂ))).mul source_tendsto_zero).cexp).div_const (16 : ℂ)
  have ht : Tendsto (fun r : ℝ => Complex.exp (2 * sourceConstant (Real.sqrt r : ℂ)) / 16)
      (𝓝[>] 0) (𝓝 (1 / 16 : ℂ)) := by simpa using h
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr : r ≠ 0)
  dsimp only [derivedNome]
  field_simp [hr0]

private lemma ratio_tendsto_one :
    Tendsto (fun r : ℝ => derivedNome r / periodNome r) (𝓝[>] 0) (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => periodNome r / (r : ℂ))
      (𝓝[>] 0) (𝓝 (1 / 16 : ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      D5.S3.Analytic.OriginalHalfBinomialEndpoint.original_nome_quotient
    change Tendsto (fun r : ℝ => ((Real.exp (-Real.pi * F (1 - r) / F r) / r : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((1 / 16 : ℝ) : ℂ)) at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      ← periodNome_eq] using h
  have ht := derivedNome_quotient_tendsto.div hp (by norm_num : (1 / 16 : ℂ) ≠ 0)
  have ht' : Tendsto (fun r : ℝ =>
      (derivedNome r / (r : ℂ)) / (periodNome r / (r : ℂ))) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    convert ht using 1 <;> norm_num
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr : r ≠ 0)
  field_simp [hr0, periodNome_ne_zero r]

private lemma period_nome_range {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < Real.exp (-Real.pi * F (1 - r) / F r) ∧
      Real.exp (-Real.pi * F (1 - r) / F r) < 1 := by
  have hF : 0 < F r := lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1)
  have hFc : 0 < F (1 - r) :=
    lt_of_lt_of_le zero_lt_one (F_ge_one (by linarith) (by linarith))
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr ?_⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hFc) hF

/-- The literal source constant, including its inverse frequency, determines
exactly the complementary-period nome on the entire open real unit interval. -/
theorem original_source_nome {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (r : ℂ) * Complex.exp (2 * sourceConstant (Real.sqrt r : ℂ)) / 16 =
      (Real.exp (-Real.pi * F (1 - r) / F r) : ℂ) ∧
      0 < Real.exp (-Real.pi * F (1 - r) / F r) ∧
      Real.exp (-Real.pi * F (1 - r) / F r) < 1 := by
  refine ⟨?_, period_nome_range hr hr1⟩
  let h : ℝ → ℂ := fun u => derivedNome u / periodNome u
  have hd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt h 0 u := by
    have hh := (derivedNome_hasDerivAt hu.1 hu.2).div
      (periodNome_hasDerivAt hu.1 hu.2) (periodNome_ne_zero u)
    apply hh.congr_deriv
    ring
  have he (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : h u = h r := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) hu ⟨hr, hr1⟩
  have hc : Tendsto h (𝓝[>] 0) (𝓝 (h r)) := by
    apply tendsto_const_nhds.congr'
    have hu : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hu, self_mem_nhdsWithin] with u hu hu0
    exact (he u ⟨hu0, hu⟩).symm
  have hval : h r = 1 := tendsto_nhds_unique hc ratio_tendsto_one
  have hid : derivedNome r = periodNome r := (div_eq_one_iff_eq (periodNome_ne_zero r)).mp hval
  exact hid.trans (periodNome_eq r)


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome
