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

/-- For a decaying differentiable profile, inversion gives a nonnegative shell density,
recovers the marginal and preserves the mass of its even extension. -/
theorem shell_projection_mass {f d : ℝ → ℝ}
    (hd : ∀ r, 0 ≤ r → HasDerivAt f (d r) r) (hs : ∀ r, 0 < r → d r ≤ 0)
    (h∞ : Tendsto f atTop (𝓝 0)) (hr∞ : Tendsto (fun r => r * f r) atTop (𝓝 0))
    (hf : IntegrableOn f (Ioi 0)) (hrd : IntegrableOn (fun r => r * d r) (Ioi 0)) :
    (∀ r, 0 ≤ r → 0 ≤ shell d r) ∧ (∀ t, 0 ≤ t → projection (shell d) t = f t) ∧
      ∫ r in Ioi (0 : ℝ), shell d r = 2 * ∫ r in Ioi (0 : ℝ), f r := by
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
      <;> ring
    rw [heq, integral_neg, integral_Ioi_of_hasDerivAt_of_nonpos'
      (fun r hr => hd r (ht.trans hr)) (fun r hr => hs r (ht.trans_lt hr)) h∞]
    ring
  · have zero : Tendsto (fun r => r * f r) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuousAt_id (x := (0 : ℝ))).mul
        (hd 0 le_rfl).continuousAt).continuousWithinAt
    have ip := integral_Ioi_mul_deriv_eq_deriv_mul (u := id) (u' := fun _ => (1 : ℝ))
      (v := f) (v' := d) (a := 0) (fun r _ => hasDerivAt_id r) (fun r hr => hd r hr.le)
      hrd (by simpa using hf) zero hr∞
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
  <;> ring

end D5.S3.Quantum.StaticExchange.IsotropicShellInversion
