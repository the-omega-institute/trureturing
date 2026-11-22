/- GID: D5/S3/Quantum/Recovery/PetzBinaryProjectiveRadialBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzBinaryProjectiveRadialBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reference-dependent bounds for ordinary binary projective Petz recovery along radial qubit segments. -/

import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.QuantumChannels.ContractionSpectrumOrder
import D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-!
The radial branch of the ordinary binary projective Petz bound. The reference Bloch
vector is `(u, 0, z)` with squared radius `R ^ 2 = u ^ 2 + z ^ 2`. The input is
`(a * u, 0, a * z)`. The loss formula uses the shared spectral coordinates of the input and
reference and the computational basis after measurement. The recovery estimate uses the
real Bloch coordinate formulas for the ordinary Petz output.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound

open Set
open D5.S3.QuantumChannels.ContractionSpectrumOrder (hasDerivAt_artanh)
open D5.S3.Quantum.Information.QubitNormalFormState (qubitState qubit_state_entropy)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)

noncomputable section

/-- The negative binary entropy in the Bloch bias coordinate, in nats. -/
private def negBinaryEntropy (y : ℝ) : ℝ := -Real.binEntropy ((1 + y) / 2)

private def radialPotential (R z s : ℝ) : ℝ :=
  negBinaryEntropy (s * R) - negBinaryEntropy (s * z)

/-- The Bregman divergence of the entropy difference, based at the reference scale `1`. -/
private def radialDefect (R z a : ℝ) : ℝ :=
  radialPotential R z a - radialPotential R z 1 + (1 - a) * deriv (radialPotential R z) 1

private def radialSlope (R z s : ℝ) : ℝ :=
  R * Real.artanh (s * R) - z * Real.artanh (s * z)

private def radialCurvature (R z s : ℝ) : ℝ :=
  (R ^ 2 - z ^ 2) / ((1 - (s * R) ^ 2) * (1 - (s * z) ^ 2))

private theorem negBinaryEntropy_eq (y : ℝ) :
    negBinaryEntropy y =
      (1 + y) / 2 * Real.log ((1 + y) / 2) + (1 - y) / 2 * Real.log ((1 - y) / 2) := by
  simp only [negBinaryEntropy, Real.binEntropy, Real.log_inv,
    show 1 - (1 + y) / 2 = (1 - y) / 2 by ring]
  ring

private theorem hasDerivAt_negBinaryEntropy {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt negBinaryEntropy (Real.artanh y) y := by
  have hp : (1 + y) / 2 ≠ 0 := by linarith [hy.1]
  have hq : (1 + y) / 2 ≠ 1 := by linarith [hy.2]
  have hplus : 1 + y ≠ 0 := by linarith [hy.1]
  have hminus : 1 - y ≠ 0 := by linarith [hy.2]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hd := ((Real.hasDerivAt_binEntropy hp hq).comp y
    (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).div_const 2)).neg
  change HasDerivAt (fun t : ℝ => -Real.binEntropy ((1 + t) / 2)) (Real.artanh y) y
  apply hd.congr_deriv
  change -((Real.log (1 - (1 + y) / 2) - Real.log ((1 + y) / 2)) * ((0 + 1) / 2)) = _
  rw [show 1 - (1 + y) / 2 = (1 - y) / 2 by ring,
    Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩, Real.log_div hplus hminus,
    Real.log_div hplus htwo, Real.log_div hminus htwo]
  ring

private theorem scaled_nonneg_lt_one {x s : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ s * x ∧ s * x < 1 := by
  have hle : s * x ≤ x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hx₀
  exact ⟨mul_nonneg hs.1 hx₀, hle.trans_lt hx₁⟩

private theorem scaled_mem {x s : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : s * x ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨hc₀, hc₁⟩ := scaled_nonneg_lt_one hx₀ hx₁ hs
  exact ⟨by linarith, hc₁⟩

private theorem one_sub_sq_pos {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    0 < 1 - x ^ 2 := by
  have hs := mul_pos (sub_pos.mpr hx₁) (show 0 < 1 + x by linarith)
  nlinarith only [hs]

private theorem hasDerivAt_radialPotential {R z s : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (radialPotential R z) (radialSlope R z s) s := by
  have hR := (hasDerivAt_negBinaryEntropy (scaled_mem (hz₀.trans hzR) hR₁ hs)).comp s
    ((hasDerivAt_id s).mul_const R)
  have hz := (hasDerivAt_negBinaryEntropy (scaled_mem hz₀ (hzR.trans_lt hR₁) hs)).comp s
    ((hasDerivAt_id s).mul_const z)
  change HasDerivAt
    ((fun y => negBinaryEntropy (y * R)) - (fun y => negBinaryEntropy (y * z))) _ s
  simpa only [radialSlope, Function.comp_def, id_eq, one_mul, mul_one, mul_comm] using hR.sub hz

private theorem hasDerivAt_radialSlope {R z s : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (radialSlope R z) (radialCurvature R z s) s := by
  have hR := (hasDerivAt_artanh (scaled_mem (hz₀.trans hzR) hR₁ hs)).comp s
    ((hasDerivAt_id s).mul_const R)
  have hz := (hasDerivAt_artanh (scaled_mem hz₀ (hzR.trans_lt hR₁) hs)).comp s
    ((hasDerivAt_id s).mul_const z)
  have hd := (hR.const_mul R).sub (hz.const_mul z)
  have hRs := scaled_nonneg_lt_one (hz₀.trans hzR) hR₁ hs
  have hzs := scaled_nonneg_lt_one hz₀ (hzR.trans_lt hR₁) hs
  have hRd := (one_sub_sq_pos hRs.1 hRs.2).ne'
  have hzd := (one_sub_sq_pos hzs.1 hzs.2).ne'
  apply hd.congr_deriv
  simp only [radialCurvature, one_mul]
  calc
    _ = R ^ 2 / (1 - (s * R) ^ 2) - z ^ 2 / (1 - (s * z) ^ 2) := by ring
    _ = _ := by
      rw [div_sub_div _ _ hRd hzd]
      congr 1
      ring

private theorem monotoneOn_radialCurvature {R z : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) :
    MonotoneOn (radialCurvature R z) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hR₀ := hz₀.trans hzR
  have hz₁ := hzR.trans_lt hR₁
  have hsR := scaled_nonneg_lt_one hR₀ hR₁ hs
  have htR := scaled_nonneg_lt_one hR₀ hR₁ ht
  have htz := scaled_nonneg_lt_one hz₀ hz₁ ht
  have hden {c : ℝ} (hc : 0 ≤ c) : 1 - (t * c) ^ 2 ≤ 1 - (s * c) ^ 2 :=
    sub_le_sub_left (pow_le_pow_left₀ (mul_nonneg hs.1 hc)
      (mul_le_mul_of_nonneg_right hst hc) 2) 1
  have hnum : 0 ≤ R ^ 2 - z ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hz₀ hzR 2)
  exact div_le_div_of_nonneg_left hnum
    (mul_pos (one_sub_sq_pos htR.1 htR.2) (one_sub_sq_pos htz.1 htz.2))
    (mul_le_mul (hden hR₀) (hden hz₀) (one_sub_sq_pos htz.1 htz.2).le
      (one_sub_sq_pos hsR.1 hsR.2).le)

private theorem negBinaryEntropy_sub_mul_artanh {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    negBinaryEntropy y - y * Real.artanh y = Real.log (1 - y ^ 2) / 2 - Real.log 2 := by
  have hplus : 1 + y ≠ 0 := by linarith [hy.1]
  have hminus : 1 - y ≠ 0 := by linarith [hy.2]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [negBinaryEntropy_eq, Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩,
    Real.log_div hplus hminus, Real.log_div hplus htwo, Real.log_div hminus htwo,
    show 1 - y ^ 2 = (1 + y) * (1 - y) by ring, Real.log_mul hplus hminus]
  ring

private theorem radialDefect_zero {R z : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) :
    radialDefect R z 0 = Real.log ((1 - z ^ 2) / (1 - R ^ 2)) / 2 := by
  have hR₀ := hz₀.trans hzR
  have hz₁ := hzR.trans_lt hR₁
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  rw [radialDefect, (hasDerivAt_radialPotential hz₀ hzR hR₁ h₁).deriv]
  simp only [radialPotential, radialSlope, zero_mul, sub_self, one_mul, sub_zero, zero_sub]
  calc
    _ = (negBinaryEntropy z - z * Real.artanh z) -
        (negBinaryEntropy R - R * Real.artanh R) := by ring
    _ = _ := by
      rw [negBinaryEntropy_sub_mul_artanh (show z ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hz₁⟩),
        negBinaryEntropy_sub_mul_artanh (show R ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hR₁⟩),
        Real.log_div (one_sub_sq_pos hz₀ hz₁).ne' (one_sub_sq_pos hR₀ hR₁).ne']
      ring

private theorem sq_mul_radialDefect_zero_le {R z a : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    (1 - a) ^ 2 * radialDefect R z 0 ≤ radialDefect R z a := by
  let T (y : ℝ) : ℝ := a + (1 - a) * y
  let F (y : ℝ) : ℝ := radialPotential R z (T y) - (1 - a) ^ 2 * radialPotential R z y
  let F' (y : ℝ) : ℝ := radialSlope R z (T y) * (1 - a) - (1 - a) ^ 2 * radialSlope R z y
  let F'' (y : ℝ) : ℝ := (1 - a) ^ 2 * (radialCurvature R z (T y) - radialCurvature R z y)
  have hT_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : T y ∈ Icc (0 : ℝ) 1 := by
    have hfactor : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
    change 0 ≤ a + (1 - a) * y ∧ a + (1 - a) * y ≤ 1
    constructor
    · exact add_nonneg ha.1 (mul_nonneg hfactor hy.1)
    · calc
        a + (1 - a) * y ≤ a + (1 - a) * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hy.2 hfactor)
        _ = 1 := by ring
  have hT_deriv (y : ℝ) : HasDerivAt T (1 - a) y := by
    change HasDerivAt ((fun _ : ℝ => a) + fun t => (1 - a) * t) (1 - a) y
    simpa only [id_eq, mul_one, zero_add] using
      (hasDerivAt_const y a).add ((hasDerivAt_id y).const_mul (1 - a))
  have hF_deriv {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : HasDerivAt F (F' y) y := by
    have hT := (hasDerivAt_radialPotential hz₀ hzR hR₁ (hT_mem hy)).comp y (hT_deriv y)
    have hy' := hasDerivAt_radialPotential hz₀ hzR hR₁ hy
    exact hT.sub (hy'.const_mul ((1 - a) ^ 2))
  have hF'_deriv {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : HasDerivAt F' (F'' y) y := by
    have hT := (hasDerivAt_radialSlope hz₀ hzR hR₁ (hT_mem hy)).comp y (hT_deriv y)
    have hy' := hasDerivAt_radialSlope hz₀ hzR hR₁ hy
    apply ((hT.mul_const (1 - a)).sub (hy'.const_mul ((1 - a) ^ 2))).congr_deriv
    dsimp only [F'']
    ring
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) F := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := F') (f'' := F'') (convex_Icc 0 1)
      (fun _ hy => (hF_deriv hy).continuousAt.continuousWithinAt)
      (fun _ hy => (hF_deriv (interior_subset hy)).hasDerivWithinAt)
      (fun _ hy => (hF'_deriv (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := interior_subset hy
    have hyT : y ≤ T y := by
      have he : T y - y = a * (1 - y) := by dsimp only [T]; ring
      apply sub_nonneg.mp
      rw [he]
      exact mul_nonneg ha.1 (sub_nonneg.mpr hy'.2)
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
      (monotoneOn_radialCurvature hz₀ hzR hR₁ hy' (hT_mem hy') hyT))
  have h₀ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have ht := hconv.slope_le_of_hasDerivAt h₀ h₁ zero_lt_one (hF_deriv h₁)
  rw [slope_def_field, sub_zero, div_one] at ht
  have hT₀ : T 0 = a := by simp [T]
  have hT₁ : T 1 = 1 := by dsimp only [T]; ring
  apply sub_nonneg.mp
  calc
    0 ≤ F' 1 - (F 1 - F 0) := sub_nonneg.mpr ht
    _ = _ := by
      dsimp only [F, F', radialDefect]
      rw [hT₀, hT₁, (hasDerivAt_radialPotential hz₀ hzR hR₁ h₁).deriv]
      ring

/-- The radial Bregman loss bounds the reference logarithm with the exact factor `(1-a)^2/2`. -/
private theorem radial_bregman_ge_log {R z a : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    (1 - a) ^ 2 * Real.log ((1 - z ^ 2) / (1 - R ^ 2)) / 2 ≤ radialDefect R z a := by
  have h := sq_mul_radialDefect_zero_le hz₀ hzR hR₁ ha
  rw [radialDefect_zero hz₀ hzR hR₁] at h
  calc
    _ = (1 - a) ^ 2 * (Real.log ((1 - z ^ 2) / (1 - R ^ 2)) / 2) := by ring
    _ ≤ _ := h

private theorem one_sub_sq_ratio_le_log {R z : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) :
    (R ^ 2 - z ^ 2) / (1 - z ^ 2) ≤ Real.log ((1 - z ^ 2) / (1 - R ^ 2)) := by
  have hz := one_sub_sq_pos hz₀ (hzR.trans_lt hR₁)
  have hR := one_sub_sq_pos (hz₀.trans hzR) hR₁
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hz hR)
  rw [inv_div] at h
  calc
    _ = 1 - (1 - R ^ 2) / (1 - z ^ 2) := by field_simp [hz.ne']; ring
    _ ≤ _ := h

private theorem radial_sq_ratio_le_twice_defect {R z a : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    (1 - a) ^ 2 * (R ^ 2 - z ^ 2) / (1 - z ^ 2) ≤ 2 * radialDefect R z a := by
  have hlog := radial_bregman_ge_log hz₀ hzR hR₁ ha
  calc
    _ = (1 - a) ^ 2 * ((R ^ 2 - z ^ 2) / (1 - z ^ 2)) := by ring
    _ ≤ (1 - a) ^ 2 * Real.log ((1 - z ^ 2) / (1 - R ^ 2)) :=
      mul_le_mul_of_nonneg_left (one_sub_sq_ratio_le_log hz₀ hzR hR₁) (sq_nonneg _)
    _ ≤ radialDefect R z a * 2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlog
    _ = _ := mul_comm _ _

/-- Logarithm pairing `Tr ρ log σ` in a shared binary eigenbasis. -/
private def binaryLogPair (y t : ℝ) : ℝ :=
  (1 + y) / 2 * Real.log ((1 + t) / 2) + (1 - y) / 2 * Real.log ((1 - t) / 2)

private theorem binaryLogPair_eq (y : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    binaryLogPair y t = negBinaryEntropy t + (y - t) * Real.artanh t := by
  have hplus : 1 + t ≠ 0 := by linarith [ht.1]
  have hminus : 1 - t ≠ 0 := by linarith [ht.2]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [binaryLogPair, negBinaryEntropy_eq, Real.artanh_eq_half_log ⟨ht.1.le, ht.2.le⟩,
    Real.log_div hplus hminus]
  simp only [Real.log_div hplus htwo, Real.log_div hminus htwo]
  ring

/-- The loss between the two shared spectral Bernoulli pairs is exactly the radial Bregman loss. -/
private theorem radial_defect_eq_spectral_loss {R z a : ℝ}
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) :
    radialDefect R z a =
      (negBinaryEntropy (a * R) - binaryLogPair (a * R) R) -
      (negBinaryEntropy (a * z) - binaryLogPair (a * z) z) := by
  have h₁ : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hR : R ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hR₁⟩
  have hz : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hzR.trans_lt hR₁⟩
  rw [radialDefect, (hasDerivAt_radialPotential hz₀ hzR hR₁ h₁).deriv,
    binaryLogPair_eq (a * R) hR, binaryLogPair_eq (a * z) hz]
  simp only [radialPotential, radialSlope, one_mul]
  ring

/-- The actual qubit state's negative entropy in radial coordinates. -/
private theorem radial_state_neg_entropy {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hR₀ : 0 ≤ R) (ha₀ : 0 ≤ a) (hDisk : (a * u) ^ 2 + (a * z) ^ 2 ≤ 1) :
    -vonNeumannEntropy (qubitState (a * u) (a * z) hDisk) = negBinaryEntropy (a * R) := by
  have hscale : (a * u) ^ 2 + (a * z) ^ 2 = (a * R) ^ 2 := by
    calc
      _ = a ^ 2 * (u ^ 2 + z ^ 2) := by ring
      _ = _ := by rw [← hR]; ring
  simp only [qubit_state_entropy, hscale, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg ha₀ hR₀), negBinaryEntropy]

/-- The transverse Bloch coordinate of the ordinary Petz output at measured bias `v`. -/
private def recoveredX (u z R v : ℝ) : ℝ :=
  u - (v - z) * Real.sqrt (1 - R ^ 2) * z * u / ((1 + Real.sqrt (1 - R ^ 2)) * (1 - z ^ 2))

/-- The longitudinal Bloch coordinate of the ordinary Petz output at measured bias `v`. -/
private def recoveredZ (u z R v : ℝ) : ℝ :=
  v - (v - z) * u ^ 2 / ((1 + Real.sqrt (1 - R ^ 2)) * (1 - z ^ 2))

/-- Squared Euclidean displacement at the radial input, using the ordinary recovery coordinates. -/
private theorem radial_recovered_error_eq {u z R a : ℝ}
    (hR : R ^ 2 = u ^ 2 + z ^ 2) (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) :
    (recoveredX u z R (a * z) - a * u) ^ 2 + (recoveredZ u z R (a * z) - a * z) ^ 2 =
      (1 - a) ^ 2 * (R ^ 2 - z ^ 2) / (1 - z ^ 2) := by
  let κ := Real.sqrt (1 - R ^ 2)
  let d := 1 - z ^ 2
  have hd : 0 < d := one_sub_sq_pos hz₀ (hzR.trans_lt hR₁)
  have hκ : 0 < 1 + κ := add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)
  have hκsq : κ ^ 2 = 1 - R ^ 2 := Real.sq_sqrt (one_sub_sq_pos (hz₀.trans hzR) hR₁).le
  have hκd : κ ^ 2 = d - u ^ 2 := by
    dsimp only [d]
    linarith only [hκsq, hR]
  have hx : recoveredX u z R (a * z) - a * u = (1 - a) * u * (κ + d) / ((1 + κ) * d) := by
    change u - (a * z - z) * κ * z * u / ((1 + κ) * d) - a * u = _
    field_simp [hκ.ne', hd.ne']
    dsimp only [d]
    ring
  have hz : recoveredZ u z R (a * z) - a * z = (1 - a) * z * u ^ 2 / ((1 + κ) * d) := by
    change a * z - (a * z - z) * u ^ 2 / ((1 + κ) * d) - a * z = _
    ring
  have hgeom : (κ + d) ^ 2 + z ^ 2 * u ^ 2 = d * (1 + κ) ^ 2 := by
    calc
      _ = d * (1 + κ) ^ 2 + (1 - d) * (κ ^ 2 - d + u ^ 2)
          + (z ^ 2 - (1 - d)) * u ^ 2 := by ring
      _ = _ := by rw [hκd]; dsimp only [d]; ring
  rw [hx, hz]
  calc
    _ = ((1 - a) ^ 2 * u ^ 2 * ((κ + d) ^ 2 + z ^ 2 * u ^ 2)) / ((1 + κ) * d) ^ 2 := by
      simp only [div_pow, ← add_div]
      congr 1
      ring
    _ = _ := by
      rw [hgeom, show R ^ 2 - z ^ 2 = u ^ 2 by linarith only [hR]]
      change _ = (1 - a) ^ 2 * u ^ 2 / d
      field_simp [hκ.ne', hd.ne']

/-- On the radial Bloch segment the squared Euclidean Petz error is at most twice the loss. -/
private theorem radial_recovered_error_le_twice_defect {u z R a : ℝ}
    (hR : R ^ 2 = u ^ 2 + z ^ 2) (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    (recoveredX u z R (a * z) - a * u) ^ 2 + (recoveredZ u z R (a * z) - a * z) ^ 2 ≤
      2 * radialDefect R z a := by
  rw [radial_recovered_error_eq hR hz₀ hzR hR₁]
  exact radial_sq_ratio_le_twice_defect hz₀ hzR hR₁ ha

/-- The reference-dependent radial bound, in a form that also applies when `z = R`. -/
private theorem log_mul_radial_recovered_error_le {u z R a : ℝ}
    (hR : R ^ 2 = u ^ 2 + z ^ 2) (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    Real.log ((1 - z ^ 2) / (1 - R ^ 2)) *
        ((recoveredX u z R (a * z) - a * u) ^ 2 + (recoveredZ u z R (a * z) - a * z) ^ 2) ≤
      2 * ((R ^ 2 - z ^ 2) / (1 - z ^ 2)) * radialDefect R z a := by
  rw [radial_recovered_error_eq hR hz₀ hzR hR₁]
  let ξ := (R ^ 2 - z ^ 2) / (1 - z ^ 2)
  let L := Real.log ((1 - z ^ 2) / (1 - R ^ 2))
  have hξ : 0 ≤ ξ := div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hz₀ hzR 2))
    (one_sub_sq_pos hz₀ (hzR.trans_lt hR₁)).le
  have h := mul_le_mul_of_nonneg_left (radial_bregman_ge_log hz₀ hzR hR₁ ha) hξ
  calc
    _ = (ξ * ((1 - a) ^ 2 * L / 2)) * 2 := by dsimp only [ξ, L]; ring
    _ ≤ (ξ * radialDefect R z a) * 2 := mul_le_mul_of_nonneg_right h (by norm_num)
    _ = _ := by change ξ * radialDefect R z a * 2 = 2 * ξ * radialDefect R z a; ring

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.QubitNormalFormState (qubitMatrix qubit_det)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)
open D5.S3.Quantum.Recovery.PetzBinaryProjectiveOverFive
  (measurement measurement_action trace_log_split ordinaryAction probability loss errorSq
    symmetric symmetric_sandwich symmetric_sub traceless_symmetric_normSq)

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℂ
local notation "Qubit" => DensityState (Fin 2)

private abbrev raw (ρ : Qubit) : M₂ := CStarMatrix.ofMatrix.symm ρ.1
private abbrev realDiagonal (b : Fin 2 → ℝ) : M₂ := Matrix.diagonal fun i => (b i : ℂ)

private theorem radial_disk {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hR₀ : 0 ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    (a * u) ^ 2 + (a * z) ^ 2 ≤ 1 := by
  have hs := scaled_nonneg_lt_one hR₀ hR₁ ha
  calc
    _ = (a * R) ^ 2 := by simp only [mul_pow, hR]; ring
    _ ≤ 1 := sub_nonneg.mp (one_sub_sq_pos hs.1 hs.2).le

private theorem qubit_reference_disk {u z R : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hR₀ : 0 ≤ R) (hR₁ : R < 1) : u ^ 2 + z ^ 2 ≤ 1 := by
  rw [← hR]
  exact sub_nonneg.mp (one_sub_sq_pos hR₀ hR₁).le

private theorem measured_qubit_raw (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) :
    raw (measurement.mapState (qubitState x z h)) =
      realDiagonal ![(1 + z) / 2, (1 - z) / 2] := by
  change CStarMatrix.ofMatrix.symm
    (measurement.toCompletelyPositiveMap (CStarMatrix.ofMatrix (qubitMatrix x z))) = _
  refine (measurement_action (qubitMatrix x z)).trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [qubitMatrix, Matrix.diag_apply, Complex.ofReal_div]

private theorem measured_qubit (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) :
    measurement.mapState (qubitState x z h) =
      qubitState 0 z (by nlinarith [sq_nonneg x]) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change raw (measurement.mapState (qubitState x z h)) = qubitMatrix 0 z
  rw [measured_qubit_raw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitMatrix, Complex.ofReal_div]

private theorem qubit_eigenvalues {u z R : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (h : u ^ 2 + z ^ 2 ≤ 1) (H : (qubitMatrix u z).IsHermitian) :
    (H.eigenvalues 0 = (1 + R) / 2 ∧ H.eigenvalues 1 = (1 - R) / 2) ∨
    (H.eigenvalues 0 = (1 - R) / 2 ∧ H.eigenvalues 1 = (1 + R) / 2) := by
  have ht : (qubitMatrix u z).trace = 1 := (qubitState u z h).2.2
  have hsum : 1 = H.eigenvalues 0 + H.eigenvalues 1 := by
    simpa [ht, Fin.sum_univ_two] using congrArg Complex.re H.trace_eq_sum_eigenvalues
  have hprod : (1 - u ^ 2 - z ^ 2) / 4 = H.eigenvalues 0 * H.eigenvalues 1 := by
    simpa [qubit_det, Fin.prod_univ_two, Complex.mul_re] using
      congrArg Complex.re H.det_eq_prod_eigenvalues
  have hd : (H.eigenvalues 0 - H.eigenvalues 1) ^ 2 = R ^ 2 := by
    have hsum_sq := congrArg (· ^ 2) hsum
    nlinarith only [hsum_sq, hR, hprod]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hd with he | he
  · left
    constructor <;> linarith only [hsum, he]
  · right
    constructor <;> linarith only [hsum, he]

private theorem radial_matrix_affine (u z a : ℝ) :
    qubitMatrix (a * u) (a * z) =
      (a : ℂ) • qubitMatrix u z + (((1 - a) / 2 : ℝ) : ℂ) • (1 : M₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitMatrix, Complex.ofReal_div] <;> ring

private theorem radial_pair_log {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (h : u ^ 2 + z ^ 2 ≤ 1) :
    (qubitMatrix (a * u) (a * z) * cfc Real.log (qubitMatrix u z)).trace.re =
      binaryLogPair (a * R) R := by
  have hp : (qubitMatrix u z).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (qubitState u z h).2.1)
  let H := hp.isHermitian
  let U := Unitary.conjStarAlgAut ℂ M₂ H.eigenvectorUnitary
  let eig := H.eigenvalues
  have href : qubitMatrix u z = U (realDiagonal eig) := H.spectral_theorem
  have hlog : cfc Real.log (qubitMatrix u z) = U (realDiagonal fun i => Real.log (eig i)) :=
    H.cfc_eq _
  have hinput : qubitMatrix (a * u) (a * z) =
      U (realDiagonal fun i => a * eig i + (1 - a) / 2) := by
    have hd : realDiagonal (fun i => a * eig i + (1 - a) / 2) =
        (a : ℂ) • realDiagonal eig + (↑((1 - a) / 2) : ℂ) • (1 : M₂) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Complex.ofReal_add, Complex.ofReal_mul]
      · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    rw [hd, map_add, map_smul, map_smul, map_one, ← href, ← radial_matrix_affine]
  rw [hinput, hlog, ← map_mul, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
  rcases qubit_eigenvalues hR h H with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, eig, h₀, h₁, binaryLogPair] <;> ring

private theorem measured_pair_log (u z a : ℝ) (h : u ^ 2 + z ^ 2 ≤ 1)
    (ha : (a * u) ^ 2 + (a * z) ^ 2 ≤ 1) :
    (raw (measurement.mapState (qubitState (a * u) (a * z) ha)) *
      cfc Real.log (raw (measurement.mapState (qubitState u z h)))).trace.re =
        binaryLogPair (a * z) z := by
  rw [measured_qubit_raw, measured_qubit_raw, cfc_diagonal,
    diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
  simp [binaryLogPair, Complex.mul_re]

private theorem radial_loss_eq {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (h : u ^ 2 + z ^ 2 ≤ 1) (h' : (a * u) ^ 2 + (a * z) ^ 2 ≤ 1) :
    loss (qubitState (a * u) (a * z) h') (qubitState u z h) = radialDefect R z a := by
  have hm : -vonNeumannEntropy (measurement.mapState (qubitState (a * u) (a * z) h')) =
      negBinaryEntropy (a * z) := by
    rw [measured_qubit, qubit_state_entropy]
    simp [negBinaryEntropy, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg ha.1 hz₀)]
  unfold loss
  rw [trace_log_split (qubitState (a * u) (a * z) h') (qubitState u z h),
    trace_log_split (measurement.mapState (qubitState (a * u) (a * z) h'))
      (measurement.mapState (qubitState u z h)),
    radial_state_neg_entropy hR (hz₀.trans hzR) ha.1 h', hm,
    radial_defect_eq_spectral_loss hz₀ hzR hR₁, measured_pair_log]
  change _ - (qubitMatrix (a * u) (a * z) * cfc Real.log (qubitMatrix u z)).trace.re - _ = _
  rw [radial_pair_log hR h]

private theorem qubit_as_symmetric (u z : ℝ) :
    qubitMatrix u z = symmetric ((1 + z) / 2) (u / 2) ((1 - z) / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitMatrix, symmetric, Complex.ofReal_div]

private theorem qubit_root {u z R : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hR₀ : 0 ≤ R) (hR₁ : R < 1) (h : u ^ 2 + z ^ 2 ≤ 1) :
    let κ := Real.sqrt (1 - R ^ 2)
    let t := Real.sqrt (1 + κ)
    CFC.sqrt (qubitMatrix u z) =
      symmetric ((1 + κ + z) / (2 * t)) (u / (2 * t)) ((1 + κ - z) / (2 * t)) := by
  dsimp only
  let κ := Real.sqrt (1 - R ^ 2)
  let t := Real.sqrt (1 + κ)
  let p := (1 + R) / 2
  let q := (1 - R) / 2
  have hp₀ : 0 ≤ p := by dsimp [p]; positivity
  have hq₀ : 0 ≤ q := by dsimp [q]; linarith
  have hκ₀ : 0 ≤ κ := Real.sqrt_nonneg _
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hpq : Real.sqrt p * Real.sqrt q = κ / 2 := by
    rw [← Real.sqrt_mul hp₀, show p * q = (1 - R ^ 2) / 4 by dsimp [p, q]; ring,
      Real.sqrt_div (one_sub_sq_pos hR₀ hR₁).le]
    norm_num [κ]
  have ht' : Real.sqrt p + Real.sqrt q = t := by
    have hs : (Real.sqrt p + Real.sqrt q) ^ 2 = 1 + κ := by
      nlinarith only [Real.sq_sqrt hp₀, Real.sq_sqrt hq₀, hpq,
        show p + q = 1 by dsimp [p, q]; ring]
    change Real.sqrt p + Real.sqrt q = Real.sqrt (1 + κ)
    rw [← hs, Real.sqrt_sq (by positivity)]
  have hscalar (x : ℝ) (hx : x = p ∨ x = q) : Real.sqrt x = (x + κ / 2) / t := by
    apply (eq_div_iff ht.ne').2
    rw [← ht']
    rcases hx with rfl | rfl <;>
      nlinarith only [Real.sq_sqrt hp₀, Real.sq_sqrt hq₀, hpq]
  have hp : (qubitMatrix u z).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (qubitState u z h).2.1)
  let H := hp.isHermitian
  let U := Unitary.conjStarAlgAut ℂ M₂ H.eigenvectorUnitary
  let eig := H.eigenvalues
  have heig (i : Fin 2) : eig i = p ∨ eig i = q := by
    rcases qubit_eigenvalues hR h H with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
      fin_cases i <;> first | exact Or.inl h₀ | exact Or.inr h₀ | exact Or.inl h₁ | exact Or.inr h₁
  have href : qubitMatrix u z = U (realDiagonal eig) := H.spectral_theorem
  rw [CFC.sqrt_eq_real_sqrt _ hp.nonneg, cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), H.cfc_eq]
  change U (realDiagonal fun i => Real.sqrt (eig i)) =
    symmetric ((1 + κ + z) / (2 * t)) (u / (2 * t)) ((1 + κ - z) / (2 * t))
  calc
    _ = U ((↑t⁻¹ : ℂ) • (realDiagonal eig + (↑(κ / 2) : ℂ) • (1 : M₂))) := by
      apply congrArg U
      ext i j
      by_cases hij : i = j
      · subst j
        simp [hscalar (eig i) (heig i), Complex.ofReal_div, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    _ = (↑t⁻¹ : ℂ) • (qubitMatrix u z + (↑(κ / 2) : ℂ) • (1 : M₂)) := by
      rw [map_smul, map_add, map_smul, map_one, ← href]
    _ = _ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [qubit_as_symmetric, symmetric, div_eq_mul_inv] <;> ring

private theorem recovery_weights (u z v x : ℝ)
    (h : u ^ 2 + z ^ 2 ≤ 1) (h' : x ^ 2 + v ^ 2 ≤ 1) :
    Matrix.diagonal (fun i => raw (measurement.mapState (qubitState x v h')) i i /
      (probability (qubitState u z h) i : ℂ)) =
      realDiagonal ![(1 + v) / (1 + z), (1 - v) / (1 - z)] := by
  rw [measured_qubit_raw]
  congr 1
  funext i
  fin_cases i <;>
    simp [probability, qubitState, qubitMatrix, Complex.ofReal_div,
      div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0)]

private theorem recovery_sandwich_value {u z v κ t : ℝ}
    (hzplus : 1 + z ≠ 0) (hzminus : 1 - z ≠ 0) (hd : 1 - z ^ 2 ≠ 0)
    (ht : t ^ 2 = 1 + κ) (hP : 1 + κ ≠ 0)
    (hκ : κ ^ 2 = 1 - u ^ 2 - z ^ 2) :
    let A := (1 + κ + z) / (2 * t)
    let B := u / (2 * t)
    let C := (1 + κ - z) / (2 * t)
    let wplus := (1 + v) / (1 + z)
    let wminus := (1 - v) / (1 - z)
    symmetric (wplus * A * A + wminus * B * B) (wplus * A * B + wminus * B * C)
        (wplus * B * B + wminus * C * C) =
      qubitMatrix (u - (v - z) * κ * z * u / ((1 + κ) * (1 - z ^ 2)))
        (v - (v - z) * u ^ 2 / ((1 + κ) * (1 - z ^ 2))) := by
  have hquad (b c : ℝ) :
      (b / (2 * t)) * (c / (2 * t)) = (b * c) / (4 * (1 + κ)) := by
    rw [div_mul_div_comm, show (2 * t) * (2 * t) = 4 * (1 + κ) by nlinarith only [ht]]
  dsimp only
  rw [qubit_as_symmetric]
  simp_rw [mul_assoc, hquad]
  congr 1
  · field_simp [hzplus, hzminus, hd, hP]
    linear_combination
      (1 + v) * (1 - z) * (1 - z ^ 2) * 2 * hκ
  · field_simp [hzplus, hzminus, hd, hP]
    ring
  · field_simp [hzplus, hzminus, hd, hP]
    linear_combination
      (1 - v) * (1 + z) * (1 - z ^ 2) * 2 * hκ

private theorem ordinaryAction_radial {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1)
    (h : u ^ 2 + z ^ 2 ≤ 1) (ha : (a * u) ^ 2 + (a * z) ^ 2 ≤ 1) :
    ordinaryAction (qubitState u z h) (raw (measurement.mapState (qubitState (a * u) (a * z) ha))) =
      qubitMatrix (recoveredX u z R (a * z)) (recoveredZ u z R (a * z)) := by
  let κ := Real.sqrt (1 - R ^ 2)
  let t := Real.sqrt (1 + κ)
  have hκ₀ : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ : κ ^ 2 = 1 - u ^ 2 - z ^ 2 := by
    have hs := Real.sq_sqrt (one_sub_sq_pos (hz₀.trans hzR) hR₁).le
    dsimp only [κ]
    linarith only [hs, hR]
  have ht : t ^ 2 = 1 + κ := Real.sq_sqrt (by positivity)
  have hP : 1 + κ ≠ 0 := by positivity
  have hz₁ := hzR.trans_lt hR₁
  have hzplus : 1 + z ≠ 0 := by linarith
  have hzminus : 1 - z ≠ 0 := by linarith
  unfold ordinaryAction
  rw [recovery_weights]
  change CFC.sqrt (qubitMatrix u z) * _ * CFC.sqrt (qubitMatrix u z) = _
  rw [qubit_root hR (hz₀.trans hzR) hR₁ h, symmetric_sandwich]
  exact recovery_sandwich_value hzplus hzminus (one_sub_sq_pos hz₀ hz₁).ne' ht hP hκ

private theorem radial_error_eq {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1)
    (h : u ^ 2 + z ^ 2 ≤ 1) (ha : (a * u) ^ 2 + (a * z) ^ 2 ≤ 1) :
    errorSq (qubitState (a * u) (a * z) ha) (qubitState u z h) =
      (recoveredX u z R (a * z) - a * u) ^ 2 + (recoveredZ u z R (a * z) - a * z) ^ 2 := by
  unfold errorSq
  rw [ordinaryAction_radial hR hz₀ hzR hR₁ h ha]
  change D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
      (qubitMatrix (a * u) (a * z) - qubitMatrix _ _) ^ 2 = _
  rw [qubit_as_symmetric, qubit_as_symmetric, symmetric_sub,
    show (1 - a * z) / 2 - (1 - recoveredZ u z R (a * z)) / 2 =
      -((1 + a * z) / 2 - (1 + recoveredZ u z R (a * z)) / 2) by ring,
    traceless_symmetric_normSq]
  ring

/-- Along the closed radial segment, ordinary projective Petz recovery obeys the
coefficient-two bound and the reference-dependent logarithmic estimates. -/
theorem radial_bounds {u z R a : ℝ} (hR : R ^ 2 = u ^ 2 + z ^ 2)
    (hz₀ : 0 ≤ z) (hzR : z ≤ R) (hR₁ : R < 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    let ρ := qubitState (a * u) (a * z) (radial_disk hR (hz₀.trans hzR) hR₁ ha)
    let σ := qubitState u z (qubit_reference_disk hR (hz₀.trans hzR) hR₁)
    errorSq ρ σ ≤ 2 * loss ρ σ ∧
    (1 - a) ^ 2 * Real.log ((1 - z ^ 2) / (1 - R ^ 2)) / 2 ≤ loss ρ σ ∧
    Real.log ((1 - z ^ 2) / (1 - R ^ 2)) * errorSq ρ σ ≤
      2 * ((R ^ 2 - z ^ 2) / (1 - z ^ 2)) * loss ρ σ := by
  dsimp only
  rw [radial_loss_eq hR hz₀ hzR hR₁ ha, radial_error_eq hR hz₀ hzR hR₁]
  exact ⟨radial_recovered_error_le_twice_defect hR hz₀ hzR hR₁ ha,
    radial_bregman_ge_log hz₀ hzR hR₁ ha, log_mul_radial_recovered_error_le hR hz₀ hzR hR₁ ha⟩

#print axioms radial_bounds

end

end D5.S3.Quantum.Recovery.PetzBinaryProjectiveRadialBound
