/- GID: D5/S3/Analysis/RegulatedSeparation
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds for a logarithmic kernel evaluated at a regulated radial separation. -/

import OmegaBuild.Commands
import D5.S3.Analysis.RightHalfPlaneLogIntegral

/-!
Omega original.

Bounds for a logarithmic kernel evaluated at a regulated radial separation.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Omega

def regulatedSeparation (ε u v x : ℝ) : ℂ :=
  ((2 * u * v * (1 - x) + ε ^ 2 : ℝ) : ℂ) +
    Complex.I * ((2 * ε * (u - v) : ℝ) : ℂ)

private theorem regulatedSeparation_norm_bound {ε u v x : ℝ}
    (hε : 0 ≤ ε) (he : ε ≤ 1) (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hx : |x| ≤ 1) :
    2 * u * v * (1 - x) ≤ ‖regulatedSeparation ε u v x‖ ∧
      ‖regulatedSeparation ε u v x‖ ≤ 7 := by
  have hq : 0 ≤ 2 * u * v * (1 - x) := by
    exact mul_nonneg (by positivity [hu.1, hv.1]) (sub_nonneg.mpr (abs_le.mp hx).2)
  constructor
  · have h := Complex.re_le_norm (regulatedSeparation ε u v x)
    change 2 * u * v * (1 - x) + ε ^ 2 + (0 * _ - 1 * 0) ≤ _ at h
    nlinarith [sq_nonneg ε]
  · unfold regulatedSeparation
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ _ + ε ^ 2)]
    have huv : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have h₁ : 2 * u * v * (1 - x) ≤ 4 := calc
      _ ≤ (2 : ℝ) * 1 * 1 * 2 := by gcongr <;> linarith [hu.1, hu.2, hv.1, hv.2, (abs_le.mp hx).1,
        (abs_le.mp hx).2]
      _ = _ := by norm_num
    have h₂ : |2 * ε * (u - v)| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hε)]
      calc
        _ ≤ (2 : ℝ) * 1 * 1 := by gcongr
        _ = _ := by norm_num
    nlinarith [(sq_le_sq₀ hε (by norm_num : (0 : ℝ) ≤ 1)).2 he]

/-- Logarithmic radial majorant for a power-log expression at regulated separations. -/
theorem regulatedSeparation_powerLog_bound {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    {P B : ℂ → ℂ} (hP : Continuous P) (hB : Continuous B) (c₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε u v x : ℝ},
      0 ≤ ε → ε ≤ 1 → u ∈ Ioo (0 : ℝ) 1 → v ∈ Ioo (0 : ℝ) 1 →
      δ ≤ u → δ ≤ v → |x| ≤ 1 → x < 1 →
      ‖c₀ * (Complex.log ((M : ℂ)^2 * regulatedSeparation ε u v x / 4) *
        P ((M : ℂ)^2 * regulatedSeparation ε u v x / 4) -
        B ((M : ℂ)^2 * regulatedSeparation ε u v x / 4))‖ ≤ C * (1 + |Real.log (1 - x)|) := by
  let R : ℝ := M ^ 2 * 7 / 4
  let d : ℝ := M ^ 2 * δ ^ 2 / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  obtain ⟨D, hD⟩ := ((hc.image hP).union
    (hc.image hB)).isBounded.exists_norm_le
  let K := max 0 D
  let L := |Real.log d| + |Real.log R| + Real.pi
  let c := ‖c₀‖
  refine ⟨c * K * (L + 1), by dsimp [c, K, L]; positivity, ?_⟩
  intro ε u v x hε he hu hv hdu hdv hx hx'
  let t := (M : ℂ) ^ 2 * regulatedSeparation ε u v x / 4
  have hn : ‖t‖ = (M ^ 2 / 4) * ‖regulatedSeparation ε u v x‖ := by
    dsimp [t]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_mul_eq_mul_div]
  have hs := regulatedSeparation_norm_bound hε he hu hv hx
  have htR : ‖t‖ ≤ R := by
    rw [hn]
    dsimp [R]
    calc
      _ ≤ M ^ 2 / 4 * 7 := mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = _ := by ring
  have hdt : d * (1 - x) ≤ ‖t‖ := calc
    _ ≤ (M ^ 2 / 4) * (2 * u * v * (1 - x)) := by
      dsimp [d]
      calc
        _ = (M ^ 2 / 4) * (2 * δ * δ * (1 - x)) := by ring
        _ ≤ _ := by
          have hu₀ : 0 ≤ 2 * u := by linarith [hu.1]
          gcongr
    _ ≤ _ := by rw [hn]; exact mul_le_mul_of_nonneg_left hs.1 (by positivity)
  have hbP : ‖P t‖ ≤ K := (hD _ (Or.inl ⟨t, by simpa using htR, rfl⟩)).trans (le_max_right _ _)
  have hbB : ‖B t‖ ≤ K := (hD _ (Or.inr ⟨t, by simpa using htR, rfl⟩)).trans (le_max_right _ _)
  have hlog : ‖Complex.log t‖ ≤ L + |Real.log (1 - x)| := by
    have h := norm_log_le_of_modulus_bounds (mul_pos hd (sub_pos.mpr hx')) hdt htR
    rw [Real.log_mul hd.ne' (sub_pos.mpr hx').ne'] at h
    dsimp [L]
    linarith [abs_add_le (Real.log d) (Real.log (1 - x))]
  change ‖c₀ *
    (Complex.log t * P t - B t)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ c * (‖Complex.log t‖ * ‖P t‖ + ‖B t‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [norm_mul] using norm_sub_le (Complex.log t * P t) (B t)
    _ ≤ c * ((L + |Real.log (1 - x)|) * K + K) := by
      gcongr
    _ ≤ _ := by
      have hn := mul_nonneg (show 0 ≤ c * K * L by dsimp [c, K, L]; positivity)
        (abs_nonneg (Real.log (1 - x)))
      nlinarith

/-- A fixed power-log kernel composed with a complex dilation. -/
def separationPowerLog (M : ℝ) (P B : ℂ → ℂ) (c : ℂ) (q : ℂ) : ℂ :=
  let z := (M : ℂ)^2 * q / 4
  c * (Complex.log z * P z - B z)

private theorem separationPowerLog_continuousAt {M q : ℝ} (hM : 0 < M) (hq : 0 < q)
    {P B : ℂ → ℂ} (hP : Continuous P) (hB : Continuous B) (c : ℂ) :
    ContinuousAt (separationPowerLog M P B c) (q : ℂ) := by
  let scale : ℂ → ℂ := fun z => (M : ℂ) ^ 2 * z / 4
  have hs : Continuous scale := by dsimp [scale]; fun_prop
  have hreal : scale q = ((M ^ 2 * q / 4 : ℝ) : ℂ) := by
    dsimp [scale]
    push_cast
    rfl
  have hslit : scale q ∈ Complex.slitPlane := by
    rw [hreal, Complex.mem_slitPlane_iff]
    exact Or.inl (by rw [Complex.ofReal_re]; positivity)
  exact (((continuousAt_clog hslit).comp hs.continuousAt).mul
    (hP.comp hs).continuousAt |>.sub (hB.comp hs).continuousAt).const_mul c

/-- The principal logarithm of the regulated separation has an integrable
boundary value when tested at compact interior radii. -/
theorem tendsto_integral_separationPowerLog {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v x : X → ℝ} {a : X → ℂ}
    (hu : Measurable u) (hv : Measurable v) (hx : Measurable x) (ha : Measurable a)
    {M δ D : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hD : 0 ≤ D)
    {P B : ℂ → ℂ} (hP : Continuous P) (hB : Continuous B) (c : ℂ)
    (hs : ∀ᵐ q ∂μ, u q ∈ Ioo (0 : ℝ) 1 ∧ v q ∈ Ioo (0 : ℝ) 1 ∧
      |x q| ≤ 1 ∧ x q < 1 ∧ ‖a q‖ ≤ D)
    (hzero : ∀ᵐ q ∂μ, (u q < δ ∨ v q < δ) → a q = 0)
    (hint : Integrable (fun q => 1 + |Real.log (1 - x q)|) μ) :
    Tendsto (fun ε : ℝ => ∫ q, a q *
      separationPowerLog M P B c (regulatedSeparation ε (u q) (v q) (x q)) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ q, a q * separationPowerLog M P B c
        (regulatedSeparation 0 (u q) (v q) (x q)) ∂μ)) ∧
      Integrable (fun q => a q * separationPowerLog M P B c
        (regulatedSeparation 0 (u q) (v q) (x q))) μ := by
  let f (ε : ℝ) (q : X) := a q *
    separationPowerLog M P B c (regulatedSeparation ε (u q) (v q) (x q))
  obtain ⟨K, hK, hk⟩ := regulatedSeparation_powerLog_bound hM hδ hP hB c
  have hmeas (ε : ℝ) : Measurable (f ε) := by
    have hmP := hP.measurable
    have hmB := hB.measurable
    unfold f separationPowerLog regulatedSeparation
    fun_prop
  let majorant (q : X) := (D * K) * (1 + |Real.log (1 - x q)|)
  have hi : Integrable majorant μ := hint.const_mul _
  have hb (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
      ∀ᵐ q ∂μ, ‖f ε q‖ ≤ majorant q := by
    filter_upwards [hs, hzero] with q hq hz
    by_cases hcut : u q < δ ∨ v q < δ
    · simp [f, hz hcut]
      dsimp [majorant]
      positivity
    · push Not at hcut
      dsimp only [f]
      rw [norm_mul]
      exact (mul_le_mul hq.2.2.2.2
        (hk hε₀ hε₁ hq.1 hq.2.1 hcut.1 hcut.2 hq.2.2.1 hq.2.2.2.1)
        (norm_nonneg _) hD).trans_eq (mul_assoc _ _ _).symm
  refine ⟨?_, hi.mono' (hmeas 0).aestronglyMeasurable (hb 0 le_rfl zero_le_one)⟩
  refine tendsto_integral_filter_of_dominated_convergence (F := f) (f := f 0) majorant
    (.of_forall fun ε => (hmeas ε).aestronglyMeasurable) ?_ hi ?_
  · have hf : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    exact hf.mono fun ε he => hb ε he.1.le he.2.le
  · filter_upwards [hs] with q hq
    have hc : Continuous (fun ε => regulatedSeparation ε (u q) (v q) (x q)) := by
      unfold regulatedSeparation
      fun_prop
    have hpos : 0 < 2 * u q * v q * (1 - x q) := by
      have hu' := hq.1.1
      have hv' := hq.2.1.1
      have hx' := hq.2.2.2.1
      positivity
    have he : regulatedSeparation 0 (u q) (v q) (x q) =
        ((2 * u q * v q * (1 - x q) : ℝ) : ℂ) := by simp [regulatedSeparation]
    have ht := (separationPowerLog_continuousAt hM hpos hP hB c).tendsto.comp
      (he ▸ hc.continuousAt.tendsto)
    simpa only [f, he, Function.comp_apply] using
      (ht.const_mul (a q)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- Exact normalization of the reciprocal of the regulated separation at positive radii. -/
theorem regulatedSeparation_inv_cap {ε u v x : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (4 * (u : ℂ) * (v : ℂ)) * (1 / (4 * (Real.pi : ℂ)^2 *
      regulatedSeparation ε u v x)) =
      (1 / (2 * (Real.pi : ℂ)^2)) * (1 - (x : ℂ) + capShift ε u v)⁻¹ := by
  have hscale : (2 * ((u * v : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (mul_pos hu hv).ne')
  have he : regulatedSeparation ε u v (x) =
      (2 * ((u * v : ℝ) : ℂ)) *
        ((1 - (x : ℂ)) + capShift ε u v) := by
    unfold regulatedSeparation
    rw [mul_add]
    change _ = _ + (2 * ((u * v : ℝ) : ℂ)) *
      ((((ε ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * ε * (u - v) : ℝ) : ℂ)) /
        (((2 * u * v : ℝ) : ℂ)))
    rw [show ((2 * u * v : ℝ) : ℂ) = 2 * ((u * v : ℝ) : ℂ) by push_cast; ring,
      mul_div_cancel₀ _ hscale]
    push_cast
    ring
  rw [he]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul]
  have hp : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hq : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero, hp, hq]

end Omega
