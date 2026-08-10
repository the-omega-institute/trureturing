/- GID: D5/S3/QuantumChannels/AmplitudeDampingContraction
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/AmplitudeDampingContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For amplitude damping on the Bloch axis, the SLD coherence contraction ratio is the constant 1−γ, and the RLD ratio is bounded by 1 on (−1,1) and tends to 1 at the pure-state boundary u→1. -/

import Mathlib

namespace D5.S3.QuantumChannels.AmplitudeDampingContraction

/-- Amplitude damping acts on the Bloch axis by `u ↦ (1−γ)u + γ`. -/
def dampedAxis (gamma u : ℝ) : ℝ := (1 - gamma) * u + gamma

/-- The SLD radial profile is constant `1`. -/
def sldRadialProfile (_u : ℝ) : ℝ := 1

/-- The KM radial profile `artanh(u)/u` (value `1` at `u = 0`). -/
noncomputable def kmRadialProfile (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.artanh u / u

/-- The RLD radial profile `1/(1−u²)`. -/
noncomputable def rldRadialProfile (u : ℝ) : ℝ := 1 / (1 - u ^ 2)

/-- The axial coherence contraction ratio `(1−γ)·φ(u′)/φ(u)` with `u′ = dampedAxis γ u`. -/
noncomputable def coherenceRatio (profile : ℝ → ℝ) (gamma u : ℝ) : ℝ :=
  (1 - gamma) * profile (dampedAxis gamma u) / profile u

/-- A ratio has a pure-state boundary endpoint `bound` when it is bounded by `bound` on `(−1,1)` and
tends to `bound` as `u → 1⁻`. -/
def HasPureBoundaryEndpoint (ratio : ℝ → ℝ) (bound : ℝ) : Prop :=
  (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ratio u ≤ bound) ∧
    Filter.Tendsto ratio (nhdsWithin 1 (Set.Iio 1)) (nhds bound)

private theorem rld_ratio_formula {gamma u : ℝ}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hu0 : -1 < u) (hu1 : u < 1) :
    coherenceRatio rldRadialProfile gamma u =
      (1 + u) / (1 + dampedAxis gamma u) := by
  have hu_sq : u ^ 2 < 1 := by nlinarith [sq_nonneg (u + 1), sq_nonneg (1 - u)]
  have hud0 : -1 < dampedAxis gamma u := by
    rw [dampedAxis]
    nlinarith
  have hud1 : dampedAxis gamma u < 1 := by
    rw [dampedAxis]
    nlinarith
  have hud_sq : (dampedAxis gamma u) ^ 2 < 1 := by
    nlinarith [sq_nonneg (dampedAxis gamma u + 1),
      sq_nonneg (1 - dampedAxis gamma u)]
  have hgamma_ne : 1 - gamma ≠ 0 := by linarith
  have hu_ne : 1 - u ^ 2 ≠ 0 := by linarith
  have hud_ne : 1 - (dampedAxis gamma u) ^ 2 ≠ 0 := by linarith
  have hu_plus : 1 + u ≠ 0 := by linarith
  have hud_plus : 1 + dampedAxis gamma u ≠ 0 := by linarith
  simp only [coherenceRatio, rldRadialProfile]
  field_simp [hu_ne, hud_ne, hu_plus, hud_plus, hgamma_ne]
  rw [dampedAxis]
  ring

/-- Amplitude-damping endpoints: the SLD coherence contraction ratio is the constant `1−γ`, and the RLD
ratio has pure-state boundary endpoint `1`. -/
theorem amplitude_damping_sld_rld_endpoints
    (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) :
    (∀ u : ℝ, coherenceRatio sldRadialProfile gamma u = 1 - gamma) ∧
      HasPureBoundaryEndpoint (coherenceRatio rldRadialProfile gamma) 1 := by
  constructor
  · intro u
    simp [coherenceRatio, sldRadialProfile]
  · constructor
    · intro u hu
      have hu_lower : -1 < u := hu.1
      have hu_upper : u < 1 := hu.2
      rw [rld_ratio_formula hgamma0 hgamma1 hu.1 hu.2]
      have hud_ge : u ≤ dampedAxis gamma u := by
        rw [dampedAxis]
        nlinarith [mul_nonneg hgamma0 (by linarith : 0 ≤ 1 - u)]
      have hud_pos : 0 < 1 + dampedAxis gamma u := by
        rw [dampedAxis]
        have hr : 0 < 1 - gamma := by linarith
        have huplus : 0 < u + 1 := by linarith
        nlinarith [mul_pos hr huplus]
      exact (div_le_one hud_pos).2 (by linarith)
    · have hcontinuous :
          ContinuousAt (fun u : ℝ => (1 + u) / (1 + dampedAxis gamma u)) 1 := by
        have hnum : ContinuousAt (fun u : ℝ => 1 + u) 1 := by fun_prop
        have hden : ContinuousAt (fun u : ℝ => 1 + dampedAxis gamma u) 1 := by
          change ContinuousAt (fun u : ℝ => 1 + ((1 - gamma) * u + gamma)) 1
          fun_prop
        exact hnum.div hden (by norm_num [dampedAxis])
      have htend : Filter.Tendsto
          (fun u : ℝ => (1 + u) / (1 + dampedAxis gamma u))
          (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
        have h : Filter.Tendsto
            (fun u : ℝ => (1 + u) / (1 + dampedAxis gamma u))
            (nhdsWithin 1 (Set.Iio 1))
            (nhds ((1 + (1 : ℝ)) / (1 + dampedAxis gamma 1))) :=
          hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
        simpa [dampedAxis] using h
      apply htend.congr'
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num))]
          with u hu1 hu0
      exact (rld_ratio_formula hgamma0 hgamma1 (by simpa using hu0) (by simpa using hu1)).symm

end D5.S3.QuantumChannels.AmplitudeDampingContraction
