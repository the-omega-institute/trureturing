module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar likelihood separation for the Petz mixture path

The rational kernel has squared `L²` norm equal to its likelihood parameter.
The change of variables `v = u / (1 - u)` transports the weighted squared
mixture-score difference to the squared distance between two such kernels.
-/

set_option autoImplicit false

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace LikelihoodRationalTailSeparation

private def g (a v : ℝ) : ℝ := a / (1 + a * v)

private theorem g_sq_integral {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun v => g a v ^ 2) (Ici 0) ∧
      (∫ v in Ici (0 : ℝ), g a v ^ 2) = a := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [g]
  let F : ℝ → ℝ := fun v => -a / (1 + a * v)
  have hderiv (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) : HasDerivAt F (g a v ^ 2) v := by
    have hden : 0 < 1 + a * v := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha'.le hv)
    have h := (hasDerivAt_const v (-a)).fun_div
      (((hasDerivAt_id v).const_mul a).const_add 1) hden.ne'
    simpa only [F, g, id_eq, zero_mul, mul_one, zero_sub, neg_mul, neg_neg, div_pow, pow_two a]
      using h
  have hden : Tendsto (fun v : ℝ => 1 + a * v) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 ((tendsto_const_mul_atTop_of_pos ha').2 tendsto_id)
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul (-a)
  have hnonneg (v : ℝ) (_hv : v ∈ Ioi (0 : ℝ)) : 0 ≤ g a v ^ 2 := sq_nonneg _
  constructor
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg hlim
  · rw [integral_Ici_eq_integral_Ioi]
    simpa only [F, mul_zero, add_zero, div_one, zero_sub, neg_neg] using
      integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hlim

private theorem memLp_g {a : ℝ} (ha : 0 ≤ a) :
    MemLp (g a) 2 (volume.restrict (Ici (0 : ℝ))) := by
  have hm : Measurable (g a) := by
    unfold g
    exact measurable_const.div (measurable_const.add (measurable_id.const_mul a))
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 (g_sq_integral ha).1

private theorem norm_toLp_sq {f : ℝ → ℝ} {μ : Measure ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ v, f v ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with v hv
  simp only [hv, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem norm_toLp_g {a : ℝ} (ha : 0 ≤ a) :
    ‖(memLp_g ha).toLp (g a)‖ = Real.sqrt a := by
  have hs : ‖(memLp_g ha).toLp (g a)‖ ^ 2 = a :=
    (norm_toLp_sq (memLp_g ha)).trans (g_sq_integral ha).2
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hs)

private theorem sq_sqrt_sub_le_integral_g_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt b - Real.sqrt a) ^ 2 ≤ ∫ v in Ici (0 : ℝ), (g b v - g a v) ^ 2 := by
  let A := (memLp_g ha).toLp (g a)
  let B := (memLp_g hb).toLp (g b)
  have hA : ‖A‖ = Real.sqrt a := norm_toLp_g ha
  have hB : ‖B‖ = Real.sqrt b := norm_toLp_g hb
  have h := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg (B - A))).2 (abs_norm_sub_norm_le B A)
  rw [sq_abs, hB, hA] at h
  have hdist : ‖B - A‖ ^ 2 = ∫ v in Ici (0 : ℝ), (g b v - g a v) ^ 2 := by
    dsimp only [A, B]
    rw [← MemLp.toLp_sub (memLp_g hb) (memLp_g ha)]
    exact norm_toLp_sq (f := g b - g a) ((memLp_g hb).sub (memLp_g ha))
  exact h.trans_eq hdist

/-- The score of a likelihood along the affine mixture from the reference. -/
@[expose] def mixtureScore (a u : ℝ) : ℝ := (a - 1) / (1 - u + u * a)

private def toTail (u : ℝ) : ℝ := u / (1 - u)

private theorem image_toTail : toTail '' Ico (0 : ℝ) 1 = Ici 0 := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_nonneg hu.1 (sub_pos.mpr hu.2).le
  · intro hv
    have hv0 : 0 ≤ v := hv
    have hden : 0 < 1 + v := add_pos_of_pos_of_nonneg zero_lt_one hv0
    have hlt : v / (1 + v) < 1 := (div_lt_one hden).2 (by linarith)
    refine ⟨v / (1 + v), ⟨div_nonneg hv0 hden.le, hlt⟩, ?_⟩
    change (v / (1 + v)) / (1 - v / (1 + v)) = v
    apply (div_eq_iff (sub_pos.mpr hlt).ne').2
    field_simp [hden.ne']
    ring

private theorem injOn_toTail : InjOn toTail (Ico (0 : ℝ) 1) := by
  intro u hu w hw heq
  change u / (1 - u) = w / (1 - w) at heq
  have h := (div_eq_div_iff (sub_pos.mpr hu.2).ne' (sub_pos.mpr hw.2).ne').mp heq
  nlinarith only [h]

private theorem hasDerivWithinAt_toTail (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt toTail (1 / (1 - u) ^ 2) (Ico 0 1) u := by
  have h := (hasDerivAt_id u).fun_div ((hasDerivAt_id u).const_sub 1) (sub_pos.mpr hu.2).ne'
  have hnum : 1 * (1 - u) - u * (-1) = 1 := by ring
  change HasDerivWithinAt (fun y : ℝ => y / (1 - y)) (1 / (1 - u) ^ 2) (Ico 0 1) u
  simpa only [id_eq, hnum] using h.hasDerivWithinAt (s := Ico (0 : ℝ) 1)

private theorem g_toTail {a u : ℝ} (ha : 0 ≤ a) (hu : u ∈ Ico (0 : ℝ) 1) :
    g a (toTail u) = (1 - u) + (1 - u) ^ 2 * mixtureScore a u := by
  have hs : 0 < 1 - u := sub_pos.mpr hu.2
  have hden : 0 < 1 - u + u * a := add_pos_of_pos_of_nonneg hs (mul_nonneg hu.1 ha)
  have hscale : 1 + a * (u / (1 - u)) = (1 - u + u * a) / (1 - u) := by
    field_simp [hs.ne'] <;> ring
  unfold g toTail mixtureScore
  rw [hscale, div_div_eq_mul_div]
  apply (div_eq_iff hden.ne').2
  rw [add_mul, mul_assoc ((1 - u) ^ 2), div_mul_cancel₀ _ hden.ne']
  ring

private theorem weighted_score_sub_sq_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntegrableOn (fun u => (1 - u) ^ 2 * (mixtureScore b u - mixtureScore a u) ^ 2) (Ico 0 1) ∧
      (∫ u in Ico (0 : ℝ) 1, (1 - u) ^ 2 * (mixtureScore b u - mixtureScore a u) ^ 2) =
        ∫ v in Ici (0 : ℝ), (g b v - g a v) ^ 2 := by
  let kernel : ℝ → ℝ := fun v => (g b v - g a v) ^ 2
  have hpoint (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
      |1 / (1 - u) ^ 2| • kernel (toTail u) =
        (1 - u) ^ 2 * (mixtureScore b u - mixtureScore a u) ^ 2 := by
    dsimp only [kernel]
    rw [abs_of_nonneg (div_nonneg zero_le_one (sq_nonneg (1 - u))), smul_eq_mul,
      g_toTail hb hu, g_toTail ha hu]
    field_simp [(sub_pos.mpr hu.2).ne']
    ring
  have hint : IntegrableOn kernel (toTail '' Ico (0 : ℝ) 1) := by
    rw [image_toTail]
    exact ((memLp_g hb).sub (memLp_g ha)).integrable_sq
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ico
      hasDerivWithinAt_toTail injOn_toTail kernel).1 hint).congr_fun hpoint measurableSet_Ico
  · have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ico
      hasDerivWithinAt_toTail injOn_toTail kernel
    rw [image_toTail] at hchange
    exact (hchange.trans (setIntegral_congr_fun measurableSet_Ico hpoint)).symm

/-- The weighted square of the score difference is integrable over the mixture path. -/
theorem integrableOn_weighted_score_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntegrableOn (fun u => (1 - u) ^ 2 * (mixtureScore b u - mixtureScore a u) ^ 2) (Ico 0 1) :=
  (weighted_score_sub_sq_integral ha hb).1

/-- The weighted mixture-score separation controls the squared difference of
the square roots, including when either likelihood is zero. -/
theorem sq_sqrt_sub_le_integral_weighted_score_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt b - Real.sqrt a) ^ 2 ≤
      ∫ u in Ico (0 : ℝ) 1, (1 - u) ^ 2 * (mixtureScore b u - mixtureScore a u) ^ 2 := by
  rw [(weighted_score_sub_sq_integral ha hb).2]
  exact sq_sqrt_sub_le_integral_g_sub_sq ha hb

end LikelihoodRationalTailSeparation
