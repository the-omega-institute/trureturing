/- GID: D5/S3/QuantumChannels/ContractionSpectrumOrder
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ContractionSpectrumOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For amplitude damping on the Bloch axis, the three coherence contraction ratios are pointwise ordered `η_SLD ≤ η_KM ≤ η_RLD` on `u ∈ (0,1)`, `γ ∈ [0,1)`, reusing the frozen profiles of `AmplitudeDampingContraction` (SLD profile `1`, KM profile `artanh u / u`, RLD profile `1/(1−u²)`). The ordering reduces to two monotonicity facts of the `artanh` profile: `artanh u / u` is increasing (giving `η_SLD ≤ η_KM`) and `(1−u²)·artanh u / u` is decreasing (giving `η_KM ≤ η_RLD`). Each is proved from a locally-supplied derivative of `artanh` (Mathlib has none) together with the frozen enclosing inequalities `u/(1+u²) ≤ artanh u ≤ u/(1−u²)` reused from `DoubleArtanhBounds`. This records the pointwise contraction-ratio ordering (the key lemma "pointwise order ⟹ sup order"); the sup-level statement over all input states follows by monotonicity of the supremum and is not separately formalized. -/

import D5.S3.QuantumChannels.AmplitudeDampingContraction
import D5.S3.Quantum.DoubleArtanhBounds

open Real Set
open D5.S3.QuantumChannels.AmplitudeDampingContraction
open D5.S3.Quantum.DoubleArtanhBounds

namespace D5.S3.QuantumChannels.ContractionSpectrumOrder

/-- Derivative of `artanh` on `(-1,1)`: `d/dx artanh x = 1/(1-x²)`.
Built from `artanh x = ½(log(1+x) − log(1−x))`. Mathlib has no `Real.hasDerivAt_artanh`. -/
private theorem hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have h1mx : (0 : ℝ) < 1 - x := by linarith
  have h1x2 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [mul_pos h1x h1mx]
  have heq : (fun t => (1 : ℝ) / 2 * (Real.log (1 + t) - Real.log (1 - t))) =ᶠ[nhds x]
      Real.artanh := by
    refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx1 hx2) ?_
    intro t ht
    have htI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hne1 : (1 : ℝ) + t ≠ 0 := by have := ht.1; linarith
    have hne2 : (1 : ℝ) - t ≠ 0 := by have := ht.2; linarith
    rw [Real.artanh_eq_half_log htI, Real.log_div hne1 hne2]
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log (ne_of_gt h1x)
    simpa using h
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - x)) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log (ne_of_gt h1mx)
    simpa using h
  have hsum : HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (1 - t))
      (1 / (1 + x) - -1 / (1 - x)) x := hlog1.sub hlog2
  have hhalf : HasDerivAt (fun t : ℝ => (1 : ℝ) / 2 * (Real.log (1 + t) - Real.log (1 - t)))
      ((1 : ℝ) / 2 * (1 / (1 + x) - -1 / (1 - x))) x := hsum.const_mul (1 / 2)
  have hval : (1 : ℝ) / 2 * (1 / (1 + x) - -1 / (1 - x)) = 1 / (1 - x ^ 2) := by
    have hne1 : (1 : ℝ) + x ≠ 0 := ne_of_gt h1x
    have hne2 : (1 : ℝ) - x ≠ 0 := ne_of_gt h1mx
    have hne3 : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt h1x2
    field_simp
    ring
  rw [hval] at hhalf
  exact heq.hasDerivAt_iff.mp hhalf

/-- `artanh` is continuous on `[0,1)` (obtained from its differentiability). -/
private theorem continuousOn_artanh_Ico : ContinuousOn Real.artanh (Ico (0 : ℝ) 1) := by
  intro u hu
  exact ((hasDerivAt_artanh (Set.mem_Ioo.mpr ⟨by linarith [hu.1], hu.2⟩)).differentiableAt).continuousAt.continuousWithinAt

/-- The KM profile `artanh t / t` is monotone increasing on `(0,1)` (engine for `η_SLD ≤ η_KM`).
The nonnegative-derivative step reuses the frozen upper bound `artanh t ≤ t/(1−t²)`
(`DoubleArtanhBounds.double_artanh_bounds`). -/
private theorem km_monotone : MonotoneOn (fun t : ℝ => Real.artanh t / t) (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · apply ContinuousOn.div (continuousOn_artanh_Ico.mono Ioo_subset_Ico_self) continuousOn_id
    intro t ht
    exact ne_of_gt ht.1
  · rw [interior_Ioo]
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr ⟨by linarith [ht.1], ht.2⟩
    exact ((hasDerivAt_artanh ht').div (hasDerivAt_id t) (ne_of_gt ht.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr ⟨by linarith [ht.1], ht.2⟩
    have hderivKM : HasDerivAt (fun s : ℝ => Real.artanh s / s)
        ((1 / (1 - t ^ 2) * t - Real.artanh t * 1) / t ^ 2) t :=
      (hasDerivAt_artanh ht').div (hasDerivAt_id t) (ne_of_gt ht.1)
    rw [hderivKM.deriv]
    have hnum : (0 : ℝ) ≤ 1 / (1 - t ^ 2) * t - Real.artanh t * 1 := by
      have hle := (double_artanh_bounds t ht.1 ht.2).1
      rw [mul_one]
      have heq : 1 / (1 - t ^ 2) * t = t / (1 - t ^ 2) := by ring
      rw [heq]; linarith
    exact div_nonneg hnum (by positivity)

/-- The `ψ` profile `(1−t²)·artanh t / t` is antitone (decreasing) on `(0,1)`
(engine for `η_KM ≤ η_RLD`). The nonpositive-derivative step reuses the frozen lower bound
`t/(1+t²) ≤ artanh t` (`DoubleArtanhBounds.double_artanh_bounds`). -/
private theorem psi_antitone :
    AntitoneOn (fun t : ℝ => (1 - t ^ 2) * Real.artanh t / t) (Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · apply ContinuousOn.div
    · exact ContinuousOn.mul (by fun_prop) (continuousOn_artanh_Ico.mono Ioo_subset_Ico_self)
    · exact continuousOn_id
    · intro t ht; exact ne_of_gt ht.1
  · rw [interior_Ioo]
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr ⟨by linarith [ht.1], ht.2⟩
    have hnsq : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_sub (1 : ℝ); simpa using this
    have hN : HasDerivAt (fun s : ℝ => (1 - s ^ 2) * Real.artanh s)
        (-(2 * t) * Real.artanh t + (1 - t ^ 2) * (1 / (1 - t ^ 2))) t :=
      hnsq.mul (hasDerivAt_artanh ht')
    exact (hN.div (hasDerivAt_id t) (ne_of_gt ht.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr ⟨by linarith [ht.1], ht.2⟩
    have hne : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
    have htne : t ≠ 0 := ne_of_gt ht.1
    have hnsq : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_sub (1 : ℝ); simpa using this
    have hN : HasDerivAt (fun s : ℝ => (1 - s ^ 2) * Real.artanh s)
        (-(2 * t) * Real.artanh t + (1 - t ^ 2) * (1 / (1 - t ^ 2))) t :=
      hnsq.mul (hasDerivAt_artanh ht')
    have hpsi : HasDerivAt (fun s : ℝ => (1 - s ^ 2) * Real.artanh s / s)
        (((-(2 * t) * Real.artanh t + (1 - t ^ 2) * (1 / (1 - t ^ 2))) * t
          - (1 - t ^ 2) * Real.artanh t * 1) / t ^ 2) t :=
      hN.div (hasDerivAt_id t) htne
    have hval : deriv (fun s : ℝ => (1 - s ^ 2) * Real.artanh s / s) t
        = (t - Real.artanh t * (1 + t ^ 2)) / t ^ 2 := by
      rw [hpsi.deriv]; field_simp; ring
    rw [hval]
    have hb := (double_artanh_bounds t ht.1 ht.2).2
    have h1t2 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ h1t2] at hb
    apply div_nonpos_iff.mpr
    right
    exact ⟨by linarith, by positivity⟩

/-- **Contraction-spectrum pointwise ordering.** For `γ ∈ [0,1)` and `u ∈ (0,1)`, the
amplitude-damping coherence contraction ratios of `AmplitudeDampingContraction` satisfy the pointwise
ordering `η_SLD ≤ η_KM ≤ η_RLD`:
`coherenceRatio sldRadialProfile γ u ≤ coherenceRatio kmRadialProfile γ u ≤ coherenceRatio rldRadialProfile γ u`.

Reusing the frozen profiles (SLD `1`, KM `artanh u / u`, RLD `1/(1−u²)`), the ordering reduces to two
`artanh`-monotonicity facts of the damped axis `u ↦ (1−γ)u + γ` (which satisfies `u ≤ u′ < 1`): the KM
profile `artanh u / u` is increasing (giving `η_SLD ≤ η_KM`), and `(1−u²)·artanh u / u` is decreasing
(giving `η_KM ≤ η_RLD`). Each is proved from a locally-supplied derivative of `artanh` (Mathlib has
none) together with the frozen enclosing inequalities `u/(1+u²) ≤ artanh u ≤ u/(1−u²)`, reused from the
`DoubleArtanhBounds` module rather than re-proved here.

This records the pointwise contraction-ratio ordering — the atom's key lemma "pointwise order ⟹ sup
order". The sup-level operational statement (the contraction coefficients `η_g` as suprema over all
input states) follows from this pointwise ordering by monotonicity of the supremum and is not
separately formalized (matching the pointwise `coherenceRatio` framework of `AmplitudeDampingContraction`). -/
theorem contraction_spectrum_order (gamma u : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) (hu0 : 0 < u) (hu1 : u < 1) :
    coherenceRatio sldRadialProfile gamma u ≤ coherenceRatio kmRadialProfile gamma u ∧
      coherenceRatio kmRadialProfile gamma u ≤ coherenceRatio rldRadialProfile gamma u := by
  have hgpos : (0 : ℝ) < 1 - gamma := by linarith
  have hd0 : (0 : ℝ) < dampedAxis gamma u := by rw [dampedAxis]; nlinarith
  have hd1 : dampedAxis gamma u < 1 := by rw [dampedAxis]; nlinarith
  have hdu : u ≤ dampedAxis gamma u := by rw [dampedAxis]; nlinarith
  have hune : u ≠ 0 := ne_of_gt hu0
  have hdne : dampedAxis gamma u ≠ 0 := ne_of_gt hd0
  set d := dampedAxis gamma u with hddef
  have hAu : Real.artanh u > 0 := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hu0, hu1⟩)
  have hAd : Real.artanh d > 0 := Real.artanh_pos (Set.mem_Ioo.mpr ⟨hd0, hd1⟩)
  have hu2 : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu0, hu1]
  have hd2 : (0 : ℝ) < 1 - d ^ 2 := by nlinarith [hd0, hd1]
  have hsld : coherenceRatio sldRadialProfile gamma u = 1 - gamma := by
    simp [coherenceRatio, sldRadialProfile]
  have hkm : coherenceRatio kmRadialProfile gamma u
      = (1 - gamma) * (Real.artanh d * u) / (d * Real.artanh u) := by
    unfold coherenceRatio kmRadialProfile
    rw [← hddef, if_neg hdne, if_neg hune]
    field_simp
  have hrld : coherenceRatio rldRadialProfile gamma u
      = ((1 - gamma) * (1 - u ^ 2)) / (1 - d ^ 2) := by
    unfold coherenceRatio rldRadialProfile
    rw [← hddef]
    field_simp
  constructor
  · rw [hsld, hkm]
    have hAA' : Real.artanh u / u ≤ Real.artanh d / d :=
      km_monotone (Set.mem_Ioo.mpr ⟨hu0, hu1⟩) (Set.mem_Ioo.mpr ⟨hd0, hd1⟩) hdu
    rw [div_le_div_iff₀ hu0 hd0] at hAA'
    rw [le_div_iff₀ (by positivity : (0:ℝ) < d * Real.artanh u)]
    nlinarith [mul_le_mul_of_nonneg_left hAA' (le_of_lt hgpos)]
  · rw [hkm, hrld]
    have hpsi_le : (1 - d ^ 2) * Real.artanh d / d ≤ (1 - u ^ 2) * Real.artanh u / u :=
      psi_antitone (Set.mem_Ioo.mpr ⟨hu0, hu1⟩) (Set.mem_Ioo.mpr ⟨hd0, hd1⟩) hdu
    rw [div_le_div_iff₀ hd0 hu0] at hpsi_le
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < d * Real.artanh u) hd2]
    nlinarith [mul_le_mul_of_nonneg_left hpsi_le (le_of_lt hgpos)]

end D5.S3.QuantumChannels.ContractionSpectrumOrder
