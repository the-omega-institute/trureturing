/- GID: D5/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PauliFunding/PureYAxisFunding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-order pure-Y Pauli resolvent funding coefficients and their exact equality cases. -/

import D5.S3.Quantum.Subentropy.UniformIntegrals
import D5.S3.Quantum.Matrix.PauliFunding.PureYAxisResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.PauliFunding

open MeasureTheory Set Filter
open scoped Topology

private theorem baseline_integral (j : ℕ) (hj : 1 ≤ j) :
    IntegrableOn (fun s : ℝ => 1 / (1 + 2 * s) ^ (2 * j)) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), 1 / (1 + 2 * s) ^ (2 * j)) =
        1 / (2 * (2 * (j : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨hi, hv⟩ :=
    D5.S3.Quantum.Subentropy.UniformIntegrals.inverse_power 1 (by norm_num) (2 * k)
  have he : 2 * k + 2 = 2 * (k + 1) := by omega
  rw [he] at hi hv
  have hi' := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => 1 / (t + 1) ^ (2 * (k + 1))) 0 (a := 2) (by norm_num)).2
      (by simpa using hi)
  refine ⟨by simpa [add_comm] using hi', ?_⟩
  have hs := integral_comp_mul_left_Ioi
    (fun t : ℝ => 1 / (t + 1) ^ (2 * (k + 1))) 0 (b := 2) (by norm_num)
  simp only [mul_zero, smul_eq_mul] at hs
  rw [hv] at hs
  convert hs using 1 <;> simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    one_pow, mul_one, add_comm] <;> ring

private theorem strict_integral_of_strict_on {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (hfg : ∀ s ∈ Ioi (0 : ℝ), g s < f s) :
    (∫ s in Ioi (0 : ℝ), g s) < ∫ s in Ioi (0 : ℝ), f s := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => f s - g s :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => (sub_pos.mpr (hfg s hs)).le
  have hp := (setIntegral_pos_iff_support_of_nonneg_ae hn (hf.sub hg)).2
    (show 0 < volume (Function.support (fun s => f s - g s) ∩ Ioi (0 : ℝ)) from by
      have he : Function.support (fun s => f s - g s) ∩ Ioi (0 : ℝ) = Ioi 0 := by
        ext s
        simp only [mem_inter_iff, Function.mem_support]
        exact ⟨fun hs => hs.2, fun hs => ⟨(sub_pos.mpr (hfg s hs)).ne', hs⟩⟩
      rw [he, Real.volume_Ioi]
      exact ENNReal.zero_lt_top)
  rw [integral_sub hf hg] at hp
  exact sub_pos.mp hp

private theorem evenMoment_upper {α β c : ℝ} (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hαc : α ≤ c) (hp : 0 ≤ c ^ 2 - 2 * α * c - β) (j : ℕ) :
    evenMoment α β j ≤ 2 * c ^ (2 * j) := by
  have hs : Real.sqrt (α ^ 2 + β) ≤ c - α :=
    Real.sqrt_le_iff.mpr ⟨sub_nonneg.mpr hαc, by nlinarith⟩
  have hroot : α + Real.sqrt (α ^ 2 + β) ≤ c := by linarith
  have hroot0 : 0 ≤ α + Real.sqrt (α ^ 2 + β) := by positivity
  have hm : |α - Real.sqrt (α ^ 2 + β)| ≤ c := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg (α ^ 2 + β)]
  unfold evenMoment
  have hplus := pow_le_pow_left₀ hroot0 hroot (2 * j)
  have hminus := pow_le_pow_left₀ (abs_nonneg (α - Real.sqrt (α ^ 2 + β))) hm (2 * j)
  rw [(even_two_mul j).pow_abs] at hminus
  linarith

private theorem resolvent_evenMoment_upper {a h s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hh0 : 0 ≤ h) (hh : h ≤ 1 - a ^ 2) (hs : 0 < s) (j : ℕ) :
    evenMoment (4 * s * a / (8 * s * (1 + 2 * s) + h))
      (h / (8 * s * (1 + 2 * s) + h)) j ≤ 2 / (1 + 2 * s) ^ (2 * j) := by
  let q : ℝ := 1 + 2 * s
  let R : ℝ := 8 * s * q + h
  have hq : 0 < q := by dsimp [q]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hα : 0 ≤ 4 * s * a / R := by positivity
  have hc : 0 ≤ 1 / q := by positivity
  have hαc : 4 * s * a / R ≤ 1 / q := by
    rw [div_le_div_iff₀ hR hq]
    have hm : 4 * s * a * q ≤ 4 * s * q := by
      calc
        _ ≤ 4 * s * 1 * q := by gcongr
        _ = _ := by ring
    dsimp [R]
    nlinarith [mul_nonneg hs.le hq.le]
  have hh' : h ≤ 2 * (1 - a) := by nlinarith [sq_nonneg (1 - a)]
  have hnum : 0 ≤ 2 * q * (1 - a) - h * (1 + s) := by
    have hm : h * (1 + s) ≤ 2 * (1 - a) * (1 + s) := by gcongr
    have hm' : 2 * (1 - a) * (1 + s) ≤ 2 * q * (1 - a) := by
      dsimp [q]
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ha1)]
    linarith
  have hid : (1 / q) ^ 2 - 2 * (4 * s * a / R) * (1 / q) - h / R =
      4 * s * (2 * q * (1 - a) - h * (1 + s)) / (R * q ^ 2) := by
    field_simp [ne_of_gt hq, ne_of_gt hR]
    dsimp [R, q]
    ring
  have hp : 0 ≤ (1 / q) ^ 2 - 2 * (4 * s * a / R) * (1 / q) - h / R := by
    rw [hid]
    positivity
  have hb := evenMoment_upper hα hc hαc hp j
  simpa only [one_div_pow, mul_one_div] using hb

private theorem semidisk_integrable {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (j : ℕ) (hj : 1 ≤ j) :
    IntegrableOn (moment a t j) (Ioi 0) := by
  have hh0 : 0 ≤ h a t := by dsimp [h]; linarith
  have hh : h a t ≤ 1 - a ^ 2 := by dsimp [h]; nlinarith [sq_nonneg t]
  have hd : ∀ s ∈ Ioi (0 : ℝ), denom a t s ≠ 0 := by
    intro s hs
    exact ne_of_gt (resolvent_spectral_data ha0 ha1 ht hs).1
  have hα : ContinuousOn (alpha a t) (Ioi 0) := by
    unfold alpha
    exact ContinuousOn.div (by fun_prop) (by unfold denom; fun_prop) hd
  have hβ : ContinuousOn (beta a t) (Ioi 0) := by
    unfold beta
    exact ContinuousOn.div continuousOn_const (by unfold denom; fun_prop) hd
  have hC : ContinuousOn (fun s => evenMoment (alpha a t s) (beta a t s) j) (Ioi 0) := by
    unfold evenMoment
    fun_prop
  have hi := ((baseline_integral j hj).1.const_mul 2).mono_nonneg
    (hC.aestronglyMeasurable measurableSet_Ioi)
    (ae_of_all _ fun s => add_nonneg
      ((even_two_mul j).pow_nonneg (alpha a t s + Real.sqrt (alpha a t s ^ 2 + beta a t s)))
      ((even_two_mul j).pow_nonneg (alpha a t s - Real.sqrt (alpha a t s ^ 2 + beta a t s))))
    ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => by
      simpa [alpha, beta, denom, mul_div_assoc] using
        resolvent_evenMoment_upper ha0 ha1 hh0 hh hs j)
  exact hi.congr_fun (fun s hs => (moment_eq_evenMoment ha0 ha1 ht hs j).symm)
    measurableSet_Ioi

/-- The section-20 matrix integral coefficient of the two actual control blocks. -/
def resolventCoefficient (a t : ℝ) (j : ℕ) : ℝ :=
  (1 / (j : ℝ)) * ∫ s in Ioi (0 : ℝ), complexMoment a t j s

/-- The section-20 funding coefficient in the pure-Y family. The last two summands
are respectively the local coefficient and the marginal coefficient. -/
def fundingCoefficient (a t : ℝ) (j : ℕ) : ℝ :=
  resolventCoefficient a t j +
    (1 - a ^ (2 * j)) / (2 * (j : ℝ) * (2 * (j : ℝ) - 1)) -
    1 / (2 * (j : ℝ) * (2 * (j : ℝ) - 1))

private theorem reference_integral (a : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    IntegrableOn (fun s : ℝ => a ^ (2 * j) / (1 + 2 * s) ^ (2 * j)) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), a ^ (2 * j) / (1 + 2 * s) ^ (2 * j)) =
        a ^ (2 * j) / (2 * (2 * (j : ℝ) - 1)) := by
  have he : (fun s : ℝ => a ^ (2 * j) / (1 + 2 * s) ^ (2 * j)) =
      (fun s : ℝ => a ^ (2 * j) * (1 / (1 + 2 * s) ^ (2 * j))) := by
    funext s
    ring
  rw [he]
  obtain ⟨hi, hv⟩ := baseline_integral j hj
  exact ⟨hi.const_mul _, by rw [integral_const_mul, hv]; ring⟩

private theorem semidisk_funding {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (j : ℕ) (hj : 1 ≤ j) :
    IntegrableOn (complexMoment a t j) (Ioi 0) ∧ 0 ≤ fundingCoefficient a t j ∧
      (0 < h a t → 0 < fundingCoefficient a t j) ∧
      (h a t = 0 → fundingCoefficient a t j = 0) := by
  have hiR := semidisk_integrable ha0 ha1 ht j hj
  have hi := hiR.congr_fun
    (fun s hs => (complex_moment_eq_real ha0 ha1 ht hs j).symm) measurableSet_Ioi
  obtain ⟨hb, hv⟩ := reference_integral a j hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hf : fundingCoefficient a t j =
      (1 / (j : ℝ)) *
        ((∫ s in Ioi (0 : ℝ), complexMoment a t j s) -
          a ^ (2 * j) / (2 * (2 * (j : ℝ) - 1))) := by
    unfold fundingCoefficient resolventCoefficient
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hmono : a ^ (2 * j) / (2 * (2 * (j : ℝ) - 1)) ≤
      ∫ s in Ioi (0 : ℝ), complexMoment a t j s := by
    rw [← hv]
    exact setIntegral_mono_on hb hi measurableSet_Ioi
      (fun s hs => (moment_comparison ha0 ha1 ht hs j).trans_eq
        (complex_moment_eq_real ha0 ha1 ht hs j).symm)
  refine ⟨hi, ?_, ?_, ?_⟩
  · rw [hf]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hmono)
  · intro hh
    have hstrict := strict_integral_of_strict_on hi hb
      (fun s hs => (moment_strict ha0 ha1 ht hh hs j hj).trans_eq
        (complex_moment_eq_real ha0 ha1 ht hs j).symm)
    rw [hv] at hstrict
    rw [hf]
    exact mul_pos (by positivity) (sub_pos.mpr hstrict)
  · intro hh
    have heq : (∫ s in Ioi (0 : ℝ), complexMoment a t j s) =
        a ^ (2 * j) / (2 * (2 * (j : ℝ) - 1)) := by
      rw [← hv]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun s hs => (complex_moment_eq_real ha0 ha1 ht hs j).trans
          (moment_boundary ha0 ha1 ht hh hs j hj))
    rw [hf, heq, sub_self, mul_zero]

/-- Every actual pure-Y source has nonnegative funding coefficients at every positive
order. Strictness and equality retain the complete bias and partner-axis boundary. -/
theorem pure_y_axis_funding (a y X Y Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hy : y ^ 2 = 1) (hD : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) (j : ℕ) (hj : 1 ≤ j) :
    let t := (-y * Y) * Real.sqrt (1 - a ^ 2)
    IntegrableOn (complexMoment a t j) (Ioi 0) ∧ 0 ≤ fundingCoefficient a t j ∧
      (0 < fundingCoefficient a t j ↔ a < 1 ∧ |Y| < 1) ∧
      (fundingCoefficient a t j = 0 ↔ a = 1 ∨ |Y| = 1) := by
  let t := (-y * Y) * Real.sqrt (1 - a ^ 2)
  have hu : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr ((sq_le_one_iff₀ ha0).mpr ha1)
  have hY2 : Y ^ 2 ≤ 1 := by nlinarith [sq_nonneg X, sq_nonneg Z]
  have hYa : |Y| ≤ 1 := (sq_le_one_iff_abs_le_one Y).mp hY2
  have ht2 : t ^ 2 = Y ^ 2 * (1 - a ^ 2) := by
    dsimp [t]
    simp only [mul_pow, neg_sq, hy, one_mul, Real.sq_sqrt hu]
  have ht : t ^ 2 ≤ 1 - a ^ 2 := by
    rw [ht2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hY2) hu]
  have hh : h a t = (1 - a ^ 2) * (1 - Y ^ 2) := by
    unfold h
    rw [ht2]
    ring
  obtain ⟨hi, hn, hp, hz⟩ := semidisk_funding ha0 ha1 ht j hj
  change IntegrableOn (complexMoment a t j) (Ioi 0) ∧ _
  refine ⟨hi, hn, ?_, ?_⟩
  · constructor
    · intro hd
      constructor
      · by_contra hn'
        have ha : a = 1 := by linarith
        have hb : h a t = 0 := by rw [hh, ha]; norm_num
        rw [hz hb] at hd
        exact (lt_irrefl (0 : ℝ)) hd
      · by_contra hn'
        have hY : |Y| = 1 := by linarith
        have hY' : Y ^ 2 = 1 := by rw [← sq_abs, hY]; norm_num
        have hb : h a t = 0 := by rw [hh, hY']; ring
        rw [hz hb] at hd
        exact (lt_irrefl (0 : ℝ)) hd
    · rintro ⟨ha, hY⟩
      apply hp
      rw [hh]
      exact mul_pos (sub_pos.mpr ((sq_lt_one_iff₀ ha0).mpr ha))
        (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one Y).mpr hY))
  · constructor
    · intro hd
      by_contra hn'
      have ha : a < 1 := lt_of_le_of_ne ha1 (by tauto)
      have hY : |Y| < 1 := lt_of_le_of_ne hYa (by tauto)
      have hb : 0 < h a t := by
        rw [hh]
        exact mul_pos (sub_pos.mpr ((sq_lt_one_iff₀ ha0).mpr ha))
          (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one Y).mpr hY))
      have hd' := hp hb
      rw [hd] at hd'
      exact (lt_irrefl (0 : ℝ)) hd'
    · rintro (ha | hY)
      · apply hz
        rw [hh, ha]
        norm_num
      · apply hz
        have hY' : Y ^ 2 = 1 := by rw [← sq_abs, hY]; norm_num
        rw [hh, hY']
        ring

#print axioms pure_y_axis_funding

end D5.S3.Quantum.Matrix.PauliFunding
