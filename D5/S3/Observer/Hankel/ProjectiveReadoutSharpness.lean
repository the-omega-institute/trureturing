/- GID: D5/S3/Observer/Hankel/ProjectiveReadoutSharpness
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ProjectiveReadoutSharpness
   mirror-E: none(waiver:sharp-hilbert-space-bound)
   anchors: []
   digest: Construct a least-energy readout-cancelling perturbation and prove an exact robust nonvanishing criterion. -/

import D5.S3.Observer.Hankel.ProjectiveRayleighReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Hankel.ProjectiveReadoutSharpness

open D5.S3.Observer.Hankel.ProjectiveRayleighReadout
open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Explicit least-energy cancellation within the candidate-orthogonal space.
The witness is -<g,k>/||g0||^2 times g0, with g0 the actual projected readout.
Sharpness concerns the Hilbert error ball; it does not assert that every
perturbation in this ball is an eigenfunction of the arithmetic Weil operator. -/
theorem least_energy_readout_cancellation (k g : H) (hk : ‖k‖ = 1)
    (hg0 : g - ⟪k, g⟫_ℂ • k ≠ 0) :
    ∃ w : H, ⟪k, w⟫_ℂ = 0 ∧ ⟪g, k + w⟫_ℂ = 0 ∧
      ‖w‖ ^ 2 = ‖⟪g, k⟫_ℂ‖ ^ 2 / ‖g - ⟪k, g⟫_ℂ • k‖ ^ 2 ∧
      ∀ v : H, ⟪k, v⟫_ℂ = 0 → ⟪g, k + v⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let g0 := g - ⟪k, g⟫_ℂ • k
  let d : ℝ := ‖g0‖ ^ 2
  let b : ℂ := ⟪g, k⟫_ℂ
  let w : H := (-b / (d : ℂ)) • g0
  have hd : 0 < d := sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd0
  obtain ⟨horth0, hgeom⟩ := readout_orthogonal_geometry k g hk
  change ⟪k, g0⟫_ℂ = 0 at horth0
  change d = ‖g‖ ^ 2 - ‖b‖ ^ 2 at hgeom
  have hdecomp : g = ⟪k, g⟫_ℂ • k + g0 := by
    dsimp only [g0]
    abel
  have hpair : ⟪g, g0⟫_ℂ = (d : ℂ) := by
    conv_lhs => rw [hdecomp, inner_add_left, inner_smul_left]
    rw [horth0, mul_zero, zero_add, inner_self_eq_norm_sq_to_K]
    simp only [d, Complex.ofReal_pow]
  have horth : ⟪k, w⟫_ℂ = 0 := by
    simp only [w, inner_smul_right, horth0, mul_zero]
  have hzero : ⟪g, k + w⟫_ℂ = 0 := by
    simp only [w, inner_add_right, inner_smul_right, hpair]
    change b + (-b / (d : ℂ)) * (d : ℂ) = 0
    field_simp [hdC]
    <;> ring
  have hn : ‖w‖ ^ 2 = ‖b‖ ^ 2 / d := by
    have hnC : ‖(d : ℂ)‖ = d := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    rw [show w = (-b / (d : ℂ)) • g0 from rfl, norm_smul, norm_div,
      norm_neg, hnC, mul_pow]
    change (‖b‖ / d) ^ 2 * d = ‖b‖ ^ 2 / d
    field_simp [hd0]
    <;> ring
  refine ⟨w, horth, hzero, hn, ?_⟩
  intro v hvOrth hvZero
  have h := centered_readout_error_bound k g v (‖v‖ ^ 2) hk hvOrth le_rfl
  rw [hvZero, zero_sub, norm_neg] at h
  change ‖b‖ ^ 2 ≤ (‖g‖ ^ 2 - ‖b‖ ^ 2) * ‖v‖ ^ 2 at h
  rw [← hgeom] at h
  rw [hn]
  apply (div_le_iff₀ hd).mpr
  nlinarith [h]

/-- Exact robust nonvanishing criterion, including the degenerate case in
which the readout has no candidate-orthogonal component. The quantifiers use
one candidate and every perturbation in its closed orthogonal error ball. -/
theorem robust_readout_nonvanishing_iff (k g : H) (delta : ℝ)
    (hk : ‖k‖ = 1) (hdelta : 0 ≤ delta) :
    (∀ w : H, ⟪k, w⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ delta → ⟪g, k + w⟫_ℂ ≠ 0) ↔
      (‖g‖ ^ 2 - ‖⟪g, k⟫_ℂ‖ ^ 2) * delta < ‖⟪g, k⟫_ℂ‖ ^ 2 := by
  constructor
  · intro hrobust
    let g0 := g - ⟪k, g⟫_ℂ • k
    have hgeom := (readout_orthogonal_geometry k g hk).2
    change ‖g0‖ ^ 2 = _ at hgeom
    by_cases hzero : g0 = 0
    · have hb : ⟪g, k⟫_ℂ ≠ 0 := by
        simpa only [add_zero] using hrobust 0 (by simp) (by simpa using hdelta)
      rw [← hgeom, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
      exact sq_pos_of_pos (norm_pos_iff.mpr hb)
    · obtain ⟨w, hwOrth, hwZero, hwNorm, _⟩ := least_energy_readout_cancellation k g hk hzero
      have hd : 0 < ‖g0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
      by_contra! hfail
      rw [← hgeom] at hfail
      have hwBound : ‖w‖ ^ 2 ≤ delta := by
        rw [hwNorm]
        apply (div_le_iff₀ hd).mpr
        nlinarith [hfail]
      exact (hrobust w hwOrth hwBound) hwZero
  · intro hmargin w horth herr
    exact readout_ne_zero_of_margin k g w delta hk horth herr hmargin

/-- Equivalent threshold written as a squared normalized overlap with the
readout representer. This form exposes the direct certificate input. -/
theorem robust_readout_angle_iff (k g : H) (delta : ℝ)
    (hk : ‖k‖ = 1) (hdelta : 0 ≤ delta) :
    (∀ w : H, ⟪k, w⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ delta → ⟪g, k + w⟫_ℂ ≠ 0) ↔
      delta * ‖g‖ ^ 2 < (1 + delta) * ‖⟪g, k⟫_ℂ‖ ^ 2 := by
  rw [robust_readout_nonvanishing_iff k g delta hk hdelta]
  constructor <;> intro h <;> nlinarith

#print axioms least_energy_readout_cancellation
#print axioms robust_readout_nonvanishing_iff

end D5.S3.Observer.Hankel.ProjectiveReadoutSharpness
