/- GID: D5/S3/Quantum/ProcessReconstruction/RobustDiamond
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/RobustDiamond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/huang2024learning, lit/johnston2009computing]
   utility: none
   digest: Dimension-independent diamond bounds from complete single-output marginals. -/

import D5.S3.Quantum.ProcessReconstruction.PureDistance
import D5.S3.Quantum.ProcessReconstruction.SpectrumGeometry
import D5.S3.Quantum.ProcessReconstruction.UnitarySpectrum

/-! Dimension-independent diamond bounds from complete single-output marginals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
  Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance

namespace UnitaryReconstruction

universe u
variable {a : Type u} [Fintype a] [DecidableEq a] [Nonempty a]

local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

omit [Nonempty a] in
theorem diamondDistance_le_two (C D : QuantumChannel a a) : diamondDistance C D ≤ 2 :=
  diamondDistance_le C D (by norm_num) fun _ => referenceError_le_two C D

omit [Nonempty a] in
theorem overlap_eq {r : Type*} [Fintype r] [DecidableEq r]
    (U V : unitaryGroup a ℂ) (v : ℓ² (r × a)) :
    ⟪L (referenceUnitary r V).val v, L (referenceUnitary r U).val v⟫_ℂ =
      ⟪v, L (referenceUnitary r (relativeUnitary U V)).val v⟫_ℂ := by
  have h : (referenceUnitary r V).valᴴ * (referenceUnitary r U).val =
      (referenceUnitary r (relativeUnitary U V)).val := by
    change ((1 : Matrix r r ℂ) ⊗ₖ V.val)ᴴ * ((1 : Matrix r r ℂ) ⊗ₖ U.val) =
      (1 : Matrix r r ℂ) ⊗ₖ (V.valᴴ * U.val)
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    simp
  let X := (referenceUnitary r V).val
  let Y := (referenceUnitary r U).val
  have h' : (L X).adjoint = L Xᴴ := by
    exact (map_star L X).symm
  change ⟪L X v, L Y v⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right, h', ← h]
  congr 1
  rw [map_mul]
  rfl

theorem diamond_le_of_spectral_halfPlane (U V : unitaryGroup a ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ z ∈ spectrum ℂ (relativeUnitary U V).val, t ≤ (c * z).re) :
    diamondDistance (conjugation U) (conjugation V) ≤ 2 * Real.sqrt (1 - t ^ 2) := by
  apply diamondDistance_le _ _ (by positivity)
  intro n ρ
  obtain ⟨σ, hσ, hdom⟩ :=
    (D5.S3.Quantum.Foundation.FiniteDiamondDistance.result (conjugation U) (conjugation V)).2.1 ρ
  obtain ⟨v, hv, herror⟩ := pure_referenceError_le U V σ hσ
  rw [overlap_eq] at herror
  let r := Fin (Fintype.card a)
  have : Nonempty r := Fin.pos_iff_nonempty.mp Fintype.card_pos
  let W := referenceUnitary r (relativeUnitary U V)
  have hreal := re_inner_ge_of_spectrum W c t
    (fun z hz => h z (reference_spectrum_subset _ hz)) v hv
  have hmod : t ≤ ‖⟪v, L W.val v⟫_ℂ‖ := by
    refine hreal.trans ?_
    simpa only [norm_mul, hc, one_mul] using Complex.re_le_norm (c * ⟪v, L W.val v⟫_ℂ)
  exact hdom.trans (herror.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (sub_le_sub_left
      ((sq_le_sq₀ ht (norm_nonneg _)).mpr hmod) _)) (by norm_num)))

theorem spectral_diameter_attained (W : unitaryGroup a ℂ) :
    ∃ p ∈ spectrum ℂ W.val, ∃ q ∈ spectrum ℂ W.val,
      ∀ z ∈ spectrum ℂ W.val, ∀ w ∈ spectrum ℂ W.val, ‖z - w‖ ≤ ‖p - q‖ := by
  let S := spectrum ℂ W.val
  have hs : IsCompact S := ContinuousFunctionalCalculus.isCompact_spectrum W.val
  have hn : S.Nonempty := spectrum.nonempty W.val
  obtain ⟨⟨p,q⟩, hpq, hh⟩ := (hs.prod hs).exists_isMaxOn (hn.prod hn)
    (f := fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖) (by fun_prop)
  exact ⟨p, hpq.1, q, hpq.2, fun z hz w hw => hh (show (z,w) ∈ S ×ˢ S from ⟨hz,hw⟩)⟩

theorem diamond_le_sewing_of_lt_sqrt_three (U V : unitaryGroup a ℂ) {δ : ℝ}
    (hsew : opNorm (U.valᴴ ⊗ₖ U.val - V.valᴴ ⊗ₖ V.val) ≤ δ)
    (hδ : δ < Real.sqrt 3) : diamondDistance (conjugation U) (conjugation V) ≤ δ := by
  let W := relativeUnitary U V
  obtain ⟨p, hp, q, hq, hmax⟩ := spectral_diameter_attained W
  have hdiam : ‖p - q‖ ≤ δ := (spectrum_chord_le W p q hp hq).trans
    ((relative_kron_norm U V).le.trans hsew)
  obtain ⟨c, hc, t, ht, heq, h⟩ := circle_diameter_halfPlane
    (spectrum.norm_eq_one_of_unitary W.prop hp) (spectrum.norm_eq_one_of_unitary W.prop hq)
    (hdiam.trans_lt hδ)
  have hspec : ∀ z ∈ spectrum ℂ W.val, t ≤ (c * z).re :=
    fun z hz => h z (spectrum.norm_eq_one_of_unitary W.prop hz) (hmax z hz p hp) (hmax z hz q hq)
  have hpos : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_nonneg ‖p - q‖]
  have hroot : 2 * Real.sqrt (1 - t ^ 2) = ‖p - q‖ := by
    apply (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hpos]
    nlinarith
  exact (diamond_le_of_spectral_halfPlane U V c hc t ht.le hspec).trans
    (by rw [hroot]; exact hdiam)

section Sites

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → Type u)
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] [∀ i, Nonempty (d i)]

theorem diamond_le_sum_localError_of_lt_sqrt_three (U V : unitaryGroup (System d) ℂ)
    (h : (∑ i, localError d i U V) < Real.sqrt 3) :
    diamondDistance (conjugation U) (conjugation V) ≤ ∑ i, localError d i U V :=
  diamond_le_sewing_of_lt_sqrt_three U V (swap_sewing_opNorm_le d U V) h

theorem diamond_le_min_scaled_sum_localError (U V : unitaryGroup (System d) ℂ) :
    diamondDistance (conjugation U) (conjugation V) ≤
      min 2 ((2 / Real.sqrt 3) * ∑ i, localError d i U V) := by
  have hn : 0 ≤ ∑ i, localError d i U V :=
    Finset.sum_nonneg fun _ _ => diamondDistance_nonneg' _ _
  have ht : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have ht2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have htwo := diamondDistance_le_two (conjugation U) (conjugation V)
  apply le_min htwo
  by_cases h : (∑ i, localError d i U V) < Real.sqrt 3
  · apply (diamond_le_sum_localError_of_lt_sqrt_three d U V h).trans
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        ((le_div_iff₀ ht).mpr (by nlinarith : 1 * Real.sqrt 3 ≤ 2)) hn
  · apply htwo.trans
    calc
      2 = (2 / Real.sqrt 3) * Real.sqrt 3 := (div_mul_cancel₀ _ ht.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity)

theorem diamond_le_two_min_one_sum_localError (U V : unitaryGroup (System d) ℂ) :
    diamondDistance (conjugation U) (conjugation V) ≤
      2 * min 1 (∑ i, localError d i U V) := by
  have hn : 0 ≤ ∑ i, localError d i U V :=
    Finset.sum_nonneg fun _ _ => diamondDistance_nonneg' _ _
  by_cases h : 1 ≤ ∑ i, localError d i U V
  · simpa only [min_eq_left h, mul_one] using diamondDistance_le_two (conjugation U) (conjugation V)
  · have h' : (∑ i, localError d i U V) ≤ 1 := le_of_not_ge h
    have hroot : 1 < Real.sqrt 3 := by
      apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    rw [min_eq_right h']
    exact (diamond_le_sum_localError_of_lt_sqrt_three d U V (h'.trans_lt hroot)).trans (by linarith)

end Sites

end UnitaryReconstruction
