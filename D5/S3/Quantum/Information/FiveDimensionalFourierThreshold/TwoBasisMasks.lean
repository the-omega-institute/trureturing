/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/TwoBasisMasks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Synthesis Gram bounds give mass gaps for measurements in two orthonormal bases. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.HarmonicThreshold
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Transfer of block Gram bounds to finite-measurement mask gaps. -/

open scoped BigOperators InnerProductSpace
open InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- Squared moduli of the coefficients in the two measurement bases. -/
def basisLaw (b f : OrthonormalBasis ι ℂ H) (z : H) : ι ⊕ ι → ℝ :=
  Sum.elim (fun i => ‖⟪b i, z⟫_ℂ‖ ^ 2) (fun j => ‖⟪f j, z⟫_ℂ‖ ^ 2)

omit [DecidableEq ι] [FiniteDimensional ℂ H] in
theorem basisLaw_sum (b f : OrthonormalBasis ι ℂ H) (z : H) :
    ∑ i, basisLaw b f z i = 2 * ‖z‖ ^ 2 := by
  rw [Fintype.sum_sum_type]
  change (∑ i, ‖⟪b i, z⟫_ℂ‖ ^ 2) + (∑ j, ‖⟪f j, z⟫_ℂ‖ ^ 2) = _
  rw [b.sum_sq_norm_inner_right, f.sum_sq_norm_inner_right]
  ring

/-- Synthesis from the columns selected by a mask of both bases. -/
def maskSynthesis (b f : OrthonormalBasis ι ℂ H) (s : Finset (ι ⊕ ι)) :
    EuclideanSpace ℂ s →ₗ[ℂ] H where
  toFun w := ∑ i : s, w i • Sum.elim (fun j => b j) (fun j => f j) i.val
  map_add' x y := by simp [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [PiLp.smul_apply, mul_smul, Finset.smul_sum]

omit [FiniteDimensional ℂ H] in
private theorem maskSynthesis_basisFun (b f : OrthonormalBasis ι ℂ H)
    (s : Finset (ι ⊕ ι)) (i : s) :
    maskSynthesis b f s (EuclideanSpace.basisFun s ℂ i) =
      Sum.elim (fun j => b j) (fun j => f j) i.val := by
  change (∑ j : s, EuclideanSpace.basisFun s ℂ i j • _) = _
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, Finset.sum_ite_eq']

private theorem maskMass_eq_norm_adjoint (b f : OrthonormalBasis ι ℂ H)
    (s : Finset (ι ⊕ ι)) (z : H) :
    maskMass (basisLaw b f z) s = ‖(LinearMap.adjoint (maskSynthesis b f s)) z‖ ^ 2 := by
  rw [← (EuclideanSpace.basisFun s ℂ).sum_sq_norm_inner_right]
  simp_rw [LinearMap.adjoint_inner_right, maskSynthesis_basisFun]
  unfold maskMass
  rw [Finset.sum_coe_sort s (fun i => ‖⟪Sum.elim (fun j => b j) (fun j => f j) i, z⟫_ℂ‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> rfl

private theorem adjoint_upper_of_sq_bound {κ : Type*} [Fintype κ]
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] H)
    {K : ℝ} (hK : 0 ≤ K) (hB : ∀ w, ‖B w‖ ^ 2 ≤ K * ‖w‖ ^ 2)
    (z : H) (hz : ‖z‖ = 1) : ‖(LinearMap.adjoint B) z‖ ^ 2 ≤ K := by
  let w := (LinearMap.adjoint B) z
  have h : ‖w‖ ^ 2 ≤ ‖B w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (B w) z
    rw [← LinearMap.adjoint_inner_right, hz, mul_one] at h
    change ‖⟪w, w⟫_ℂ‖ ≤ _ at h
    simpa using h
  by_cases hw : ‖w‖ = 0
  · simpa [w, hw] using hK
  have hsq := (sq_le_sq₀ (sq_nonneg ‖w‖) (norm_nonneg _)).2 h
  have hmul : ‖w‖ ^ 2 * ‖w‖ ^ 2 ≤ K * ‖w‖ ^ 2 := by
    calc
      _ = (‖w‖ ^ 2) ^ 2 := by ring
      _ ≤ _ := hsq.trans (hB w)
  exact le_of_mul_le_mul_right hmul (sq_pos_of_ne_zero hw)

private theorem adjoint_lower_of_sq_bound {κ : Type*} [Fintype κ]
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] H)
    {K : ℝ} (hK : 0 < K) (hB : ∀ w, K * ‖w‖ ^ 2 ≤ ‖B w‖ ^ 2)
    (hrank : Fintype.card κ = Module.finrank ℂ H)
    (z : H) (hz : ‖z‖ = 1) : K ≤ ‖(LinearMap.adjoint B) z‖ ^ 2 := by
  have hzero (w : EuclideanSpace ℂ κ) (hw : B w = 0) : w = 0 := by
    have h := hB w
    rw [hw, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    have hsq : ‖w‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right h hK
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  have hinj : Function.Injective B := by
    intro a b hab
    exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ κ) = Module.finrank ℂ H := by
    rwa [finrank_euclideanSpace]
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj z
  have hc : 1 ≤ ‖w‖ * ‖(LinearMap.adjoint B) z‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) w ((LinearMap.adjoint B) z)
    rw [LinearMap.adjoint_inner_right, hw] at h
    simpa [hz] using h
  have hc' := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hc
  have hd := hB w
  rw [hw, hz, one_pow] at hd
  have hmul := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖(LinearMap.adjoint B) z‖)
  rw [mul_pow, one_pow] at hc'
  have hchain := mul_le_mul_of_nonneg_left hc' hK.le
  rw [mul_one, ← mul_assoc] at hchain
  simpa only [one_mul] using hchain.trans hmul

/-- Upper block-Gram bounds on small masks and lower block-Gram bounds on balanced masks
give the exact Rayleigh inputs for the harmonic threshold proof. -/
theorem spectralMaskGaps_of_synthesis (b f : OrthonormalBasis ι ℂ H)
    {A E : ℝ} (hA : 0 ≤ 2 - A) (hE : 0 < E)
    (hsmall : ∀ (s : Finset (ι ⊕ ι)), s.card < Fintype.card ι →
      ∀ w, ‖maskSynthesis b f s w‖ ^ 2 ≤ (2 - A) * ‖w‖ ^ 2)
    (hbalanced : ∀ (s : Finset (ι ⊕ ι)), s.card = Fintype.card ι →
      ∀ w, E * ‖w‖ ^ 2 ≤ ‖maskSynthesis b f s w‖ ^ 2)
    (z : H) (hz : ‖z‖ = 1) :
    SpectralMaskGaps (basisLaw b f z) (Fintype.card ι) A E := by
  have hrank : Module.finrank ℂ H = Fintype.card ι := (Module.finrank_eq_card_basis b.toBasis)
  constructor
  · intro s hs
    have hcard := Finset.card_compl_add_card s
    rw [Fintype.card_sum] at hcard
    have hc : sᶜ.card < Fintype.card ι := by omega
    have hu : maskMass (basisLaw b f z) sᶜ ≤ 2 - A := by
      rw [maskMass_eq_norm_adjoint]
      exact adjoint_upper_of_sq_bound _ hA (hsmall sᶜ hc) z hz
    have htotal : maskMass (basisLaw b f z) sᶜ + maskMass (basisLaw b f z) s = 2 := by
      unfold maskMass
      rw [Finset.sum_compl_add_sum, basisLaw_sum, hz]
      norm_num
    linarith only [hu, htotal]
  · intro s hs
    rw [maskMass_eq_norm_adjoint]
    apply adjoint_lower_of_sq_bound _ hE (hbalanced s hs) _ z hz
    simpa [hrank] using hs

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
