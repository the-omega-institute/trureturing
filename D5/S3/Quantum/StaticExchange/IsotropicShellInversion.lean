/- GID: D5/S3/Quantum/StaticExchange/IsotropicShellInversion
   generality: G
   mirror-B: D5/B/S3/Quantum/StaticExchange/IsotropicShellInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntegralEqImproper]
   utility: none
   digest: Inversion and mass preservation for the uniform shell projection. -/

module
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! A shell of radius r contributes uniform coordinate density 1/(2r) on (−r,r). -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology
namespace D5.S3.Quantum.StaticExchange.IsotropicShellInversion

/-- The positive-coordinate tail density of a shell mixture. -/
noncomputable def projection (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in Ioi t, h r / (2 * r)

/-- Radial shell density reconstructed from a coordinate-density derivative. -/
def shell (d : ℝ → ℝ) (r : ℝ) : ℝ := -2 * (r * d r)

private theorem weighted_decay {f : ℝ → ℝ} (hm : AntitoneOn f (Ioi 0))
    (hf : IntegrableOn f (Ioi 0)) : Tendsto (fun r => r * f r) atTop (𝓝 0) := by
  have bound {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (h : ∀ x ∈ Icc a b, c ≤ |f x|) :
      (b - a) * c ≤ ∫ x in Ioi a, |f x| := by
    have habs : IntegrableOn (fun x => |f x|) (Ioi 0) := hf.abs
    have hi := habs.mono_set (Ioi_subset_Ioi ha.le)
    have sub := intervalIntegral.integral_Ioi_sub_Ioi hi hab
    have loc : IntervalIntegrable (fun x => |f x|) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hi.mono_set Ioc_subset_Ioi_self)
    have cmp := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := c)) loc h
    rw [intervalIntegral.integral_const, smul_eq_mul] at cmp
    linarith [show 0 ≤ ∫ x in Ioi b, |f x| from integral_nonneg (fun _ => abs_nonneg _)]
  have halfTop : Tendsto (fun r : ℝ => r/2) atTop atTop :=
    by simpa [div_eq_mul_inv, mul_comm] using
        tendsto_id.const_mul_atTop (by norm_num : 0 < (2:ℝ)⁻¹)
  have ht := tendsto_integral_Ioi_zero (f := fun x => |f x|) (μ := volume) halfTop
  have ht' := tendsto_integral_Ioi_zero (f := fun x => |f x|) (μ := volume)
    (tendsto_id (x := atTop))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (show Tendsto
    (fun r : ℝ => -(∫ x in Ioi r, |f x|)) atTop (𝓝 0) by simpa using ht'.neg)
    (show Tendsto (fun r : ℝ => 2 * ∫ x in Ioi (r/2), |f x|) atTop (𝓝 0)
      by simpa using ht.const_mul 2)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    have B := bound hr (by linarith : r ≤ r+r) (c := -f r)
      (fun x hx => le_trans (neg_le_neg (hm hr (hr.trans_le hx.1) hx.1)) (neg_le_abs _))
    nlinarith only [B]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    have hp : 0 < r/2 := by linarith
    have B := bound hp (by linarith : r/2 ≤ r) (c := f r)
      (fun x hx => le_trans (hm (hp.trans_le hx.1) hr hx.2) (le_abs_self _))
    nlinarith only [B]

/-- For a decaying differentiable profile, inversion gives a nonnegative shell density,
recovers the marginal and preserves the mass of its even extension. -/
theorem shell_projection_mass {f d : ℝ → ℝ}
    (hc : ContinuousWithinAt f (Ici 0) 0)
    (hd : ∀ r, 0 < r → HasDerivAt f (d r) r) (hs : ∀ r, 0 < r → d r ≤ 0)
    (hf : IntegrableOn f (Ioi 0)) :
    (∀ r, 0 ≤ r → 0 ≤ shell d r) ∧ (∀ t, 0 ≤ t → projection (shell d) t = f t) ∧
      ∫ r in Ioi (0 : ℝ), shell d r = 2 * ∫ r in Ioi (0 : ℝ), f r := by
  have hm : AntitoneOn f (Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    · intro x hx; rw [interior_Ioi] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx; rw [interior_Ioi] at hx; exact hs x hx
  have hrDecay := weighted_decay hm hf
  have hDecay : Tendsto f atTop (𝓝 0) := by
    apply (hrDecay.div_atTop (tendsto_id (x := atTop))).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    change r * f r / r = f r
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases hr.eq_or_lt with h | h
    · simp [← h, shell]
    · exact mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (mul_nonpos_of_nonneg_of_nonpos hr (hs r h))
  · intro t ht
    have heq : projection (shell d) t = ∫ r in Ioi t, -d r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hp : 0 < r := lt_of_le_of_lt ht hr
      unfold shell
      field_simp
    have hct : ContinuousWithinAt f (Ici t) t := by
      rcases ht.eq_or_lt with h | h
      · simpa [← h] using hc
      · exact (hd t h).continuousAt.continuousWithinAt
    rw [heq, integral_neg, integral_Ioi_of_hasDerivAt_of_nonpos hct
      (fun r hr => hd r (ht.trans_lt hr)) (fun r hr => hs r (ht.trans_lt hr)) hDecay]
    ring
  · have zero : Tendsto (fun r => r * f r) (𝓝[>] 0) (𝓝 0) := by
      have idlim : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa using idlim.mul (hc.mono Ioi_subset_Ici_self).tendsto
    let j := (Ioi (0 : ℝ)).indicator f
    have hj : Integrable j := (integrable_indicator_iff measurableSet_Ioi).mpr hf
    let G := fun t : ℝ => t * f t - ∫ x in (0 : ℝ)..t, j x
    have hgDeriv (t : ℝ) (ht : 0 < t) : HasDerivAt G (t * d t) t := by
      have jeq : j =ᶠ[𝓝 t] f := by
        filter_upwards [Ioi_mem_nhds ht] with x hx
        exact indicator_of_mem hx f
      have hjAt : ContinuousAt j t := (hd t ht).continuousAt.congr_of_eventuallyEq jeq
      have prim := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t) hj.intervalIntegrable
        hj.aestronglyMeasurable.stronglyMeasurableAtFilter hjAt
      convert ((hasDerivAt_id t).mul (hd t ht)).sub prim using 1
      · rfl
      · rw [jeq.eq_of_nhds]
        simp
    have hgCont : ContinuousWithinAt G (Ici 0) 0 :=
      (continuousWithinAt_id.mul hc).sub (hj.continuous_primitive 0).continuousWithinAt
    have hgLimit := hrDecay.sub (intervalIntegral_tendsto_integral_Ioi 0 hj.integrableOn
      (tendsto_id (x := atTop)))
    have hrd : IntegrableOn (fun r => r * d r) (Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonpos hgCont hgDeriv
        (fun r hr => mul_nonpos_of_nonneg_of_nonpos hr.le (hs r hr)) hgLimit
    have ip := integral_Ioi_mul_deriv_eq_deriv_mul (u := id) (u' := fun _ => (1 : ℝ))
      (v := f) (v' := d) (a := 0) (fun r _ => hasDerivAt_id r) (fun r hr => hd r hr)
      hrd (by simpa only [Pi.mul_def, one_mul] using hf) zero hrDecay
    simp only [id_eq, one_mul, sub_self, zero_sub] at ip
    rw [show (∫ r in Ioi (0 : ℝ), shell d r) = -2 * ∫ r in Ioi (0 : ℝ), r * d r
      from integral_const_mul _ _, ip]
    ring

/-- A continuous candidate shell density with the prescribed projection is uniquely
determined at every positive radius. -/
theorem shell_density_unique {h f : ℝ → ℝ}
    (hc : ContinuousOn h (Ioi 0))
    (hi : ∀ t, 0 < t → IntegrableOn (fun r => h r / (2 * r)) (Ioi t))
    (same : ∀ t, 0 < t → projection h t = f t) :
    ∀ r, 0 < r → h r = shell (deriv f) r := by
  intro r hr
  let g := fun x => h x / (2 * x)
  have hg : ContinuousOn g (Ioi 0) :=
    hc.div (continuous_const.mul continuous_id).continuousOn
      (fun x hx => mul_ne_zero (by norm_num) (ne_of_gt hx))
  have loc : StronglyMeasurableAtFilter g (𝓝 r) :=
    ⟨Ioi (r/2), Ioi_mem_nhds (by linarith), (hi (r/2) (by linarith)).aestronglyMeasurable⟩
  have dh := intervalIntegral.integral_hasDerivAt_right (a := r) (b := r) (f := g)
    (IntervalIntegrable.refl) loc (hg.continuousAt (Ioi_mem_nhds hr))
  have eq : (fun t => f r - ∫ x in r..t, g x) =ᶠ[𝓝 r] f := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hi r hr) (hi t ht)]
    change f r - (projection h r - projection h t) = f t
    rw [same r hr, same t ht]; ring
  have deriv_f := ((hasDerivAt_const r (f r)).sub dh).congr_of_eventuallyEq eq.symm
  rw [shell, deriv_f.deriv]
  dsimp [g]
  field_simp
  ring

end D5.S3.Quantum.StaticExchange.IsotropicShellInversion
