/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Covariance square-root converse and divergent harmonic cutoffs. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondDimensionThreshold
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Algebra.InfiniteSum.Real

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The Hilbert–Schmidt converse for Eq. (11) and its positive-degree trace bounds. -/

noncomputable section

open scoped ComplexOrder Ring
open ContinuousLinearMap HilbertSchmidt Filter
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt

namespace NullConeGravity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "Op" => H →L[ℂ] H

/-- Inverse square root of the positive normalization operator. -/
def covarianceNormalizer (N : Op) : Op := (CFC.sqrt N)⁻¹ʳ

/-- The difference of covariance roots in the inner product given by the normalizer. -/
def covarianceRootDiff (N A T : Op) : Op :=
  CFC.sqrt (adjointCongr (covarianceNormalizer N) (A + T)) -
    CFC.sqrt (adjointCongr (covarianceNormalizer N) A)

private theorem strictlyPositive_of_coercive {N : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ N) : IsStrictlyPositive N :=
  (isStrictlyPositive_algebraMap (A := Op) hc).of_le (by simpa [Algebra.algebraMap_eq_smul_one] using hN)

private theorem normalizer_selfAdjoint (N : Op) : IsSelfAdjoint (covarianceNormalizer N) := by
  rw [covarianceNormalizer, ← CFC.sqrt_ringInverse]
  exact (CFC.sqrt_nonneg _).isSelfAdjoint

private theorem congr_eq_mul (N X : Op) :
    adjointCongr (covarianceNormalizer N) X = covarianceNormalizer N * X * covarianceNormalizer N := by
  change star (covarianceNormalizer N) * (X * covarianceNormalizer N) = _
  rw [(normalizer_selfAdjoint N).star_eq, mul_assoc]

private theorem normalizer_congr_self {N : Op} (hN : IsStrictlyPositive N) :
    adjointCongr (covarianceNormalizer N) N = 1 := by
  rw [congr_eq_mul, covarianceNormalizer, ← CFC.sqrt_ringInverse]
  exact CFC.conjSqrt_ringInverse_self N hN

private theorem congr_nonneg (N : Op) {X : Op} (hX : 0 ≤ X) :
    0 ≤ adjointCongr (covarianceNormalizer N) X := by
  simpa only [congr_eq_mul, (normalizer_selfAdjoint N).star_eq] using
    star_left_conjugate_nonneg hX (covarianceNormalizer N)

private theorem congr_norm_le {N X : Op} {r : ℝ} (hN : IsStrictlyPositive N)
    (hr : 0 ≤ r) (hX : 0 ≤ X) (hbound : X ≤ r • N) :
    ‖adjointCongr (covarianceNormalizer N) X‖ ≤ r := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hr (congr_nonneg N hX)).2
  let C := covarianceNormalizer N
  have h := star_left_conjugate_le_conjugate hbound C
  have hC : star C = C := (normalizer_selfAdjoint N).star_eq
  change star C * X * C ≤ star C * (r • N) * C at h
  rw [hC, mul_smul_comm, smul_mul_assoc] at h
  change C * X * C ≤ r • (C * N * C) at h
  change covarianceNormalizer N * X * covarianceNormalizer N ≤
    r • (covarianceNormalizer N * N * covarianceNormalizer N) at h
  rw [← congr_eq_mul, ← congr_eq_mul, normalizer_congr_self hN] at h
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The physical normalization bounds the perturbed covariance by two in operator norm. -/
theorem norm_B_prime_le_two {A T : Op} {c : ℝ} (hc : 0 < c) (hN : c • (1 : Op) ≤ 1 + T)
    (hB : 0 ≤ A + T) (hBupper : 0 ≤ (1 + T) - (A - 1)) :
    ‖adjointCongr (covarianceNormalizer (1 + T)) (A + T)‖ ≤ 2 := by
  apply congr_norm_le (strictlyPositive_of_coercive hc hN) (by norm_num) hB
  apply sub_nonneg.mp
  convert hBupper using 1
  simp only [two_smul]
  abel

/-- Coercivity transfers the unperturbed covariance bound to the normalized inner product. -/
theorem norm_A_prime_le_two_div_c {N A : Op} {c : ℝ} (hc : 0 < c) (hN : c • (1 : Op) ≤ N)
    (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op)) :
    ‖adjointCongr (covarianceNormalizer N) A‖ ≤ 2 / c := by
  apply congr_norm_le (strictlyPositive_of_coercive hc hN) (by positivity) hA
  refine hAupper.trans ?_
  have h := smul_le_smul_of_nonneg_left hN (show 0 ≤ 2 / c by positivity)
  rwa [smul_smul, div_mul_cancel₀ _ hc.ne'] at h

/-- The difference-of-squares identity with the factors kept in their operator order. -/
theorem congruence_diff_eq {N A T : Op} (hA : 0 ≤ A) (hB : 0 ≤ A + T) :
    let C := covarianceNormalizer N
    let Δ := covarianceRootDiff N A T
    C * T * C = CFC.sqrt (adjointCongr C (A + T)) * Δ + Δ * CFC.sqrt (adjointCongr C A) := by
  dsimp only
  unfold covarianceRootDiff
  rw [mul_sub, sub_mul]
  rw [CFC.sqrt_mul_sqrt_self _ (congr_nonneg N hB),
    CFC.sqrt_mul_sqrt_self _ (congr_nonneg N hA)]
  simp only [congr_eq_mul]
  noncomm_ring

private theorem hs_left_le {X : Op} (S : Op) (hX : IsHilbertSchmidt X) :
    Real.sqrt (hsSq (S * X) (isHilbertSchmidt_mul_left hX)) ≤
      ‖S‖ * Real.sqrt (hsSq X hX) := by
  have hb := summable_norm_sq_apply_of_hilbertBasis _ (exists_hilbertBasis ℂ H).choose_spec.choose hX
  have h : hsSq (S * X) (isHilbertSchmidt_mul_left hX) ≤ ‖S‖ ^ 2 * hsSq X hX := by
    unfold hsSq
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum ?_ (summable_norm_sq_apply_of_hilbertBasis _ _
      (isHilbertSchmidt_mul_left hX)) (hb.mul_left _)
    intro i
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm _) _
  calc
    _ ≤ Real.sqrt (‖S‖ ^ 2 * hsSq X hX) := Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private theorem hs_adjoint (X : Op) (hX : IsHilbertSchmidt X) :
    hsSq X.adjoint (isHilbertSchmidt_star hX) = hsSq X hX := by
  unfold hsSq
  exact (hasSum_norm_sq_apply_eq_adjoint _ _
    (summable_norm_sq_apply_of_hilbertBasis _ _ hX)).tsum_eq

private theorem hs_right_le {X : Op} (S : Op) (hX : IsHilbertSchmidt X) :
    Real.sqrt (hsSq (X * S) (isHilbertSchmidt_mul_right hX)) ≤
      ‖S‖ * Real.sqrt (hsSq X hX) := by
  have h := hs_left_le S.adjoint (isHilbertSchmidt_star hX)
  change Real.sqrt (hsSq (S.adjoint * X.adjoint) _) ≤ ‖S.adjoint‖ * Real.sqrt (hsSq X.adjoint _) at h
  have he : S.adjoint * X.adjoint = (X * S).adjoint := (adjoint_comp X S).symm
  simp only [hsSq, he, adjoint.norm_map] at h
  have h' : Real.sqrt (hsSq (X * S).adjoint (isHilbertSchmidt_star
    (isHilbertSchmidt_mul_right hX))) ≤
      ‖S‖ * Real.sqrt (hsSq X.adjoint (isHilbertSchmidt_star hX)) := h
  rw [hs_adjoint (X * S), hs_adjoint X] at h'
  exact h'

private theorem hs_add_le {X Y : Op} (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    Real.sqrt (hsSq (X + Y) (isHilbertSchmidt_add hX hY)) ≤
      Real.sqrt (hsSq X hX) + Real.sqrt (hsSq Y hY) := by
  let b := (exists_hilbertBasis ℂ H).choose_spec.choose
  have hx := summable_norm_sq_apply_of_hilbertBasis _ b hX
  have hy := summable_norm_sq_apply_of_hilbertBasis _ b hY
  have hm := Real.Lp_add_le_tsum_of_nonneg (p := 2) (by norm_num)
    (fun i => norm_nonneg (X (b i))) (fun i => norm_nonneg (Y (b i)))
    (by simpa using hx)
    (by simpa using hy)
  have hbound : hsSq (X + Y) (isHilbertSchmidt_add hX hY) ≤
      ∑' i, (‖X (b i)‖ + ‖Y (b i)‖) ^ 2 := by
    unfold hsSq
    refine Summable.tsum_le_tsum (fun i => ?_)
      (summable_norm_sq_apply_of_hilbertBasis _ _ (isHilbertSchmidt_add hX hY))
      (by simpa using hm.1)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
  refine (Real.sqrt_le_sqrt hbound).trans ?_
  simpa [hsSq, b, Real.sqrt_eq_rpow] using hm.2

private theorem hs_normalized_lower_bound {N A T : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ N) (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op))
    (hB : 0 ≤ A + T) (hBupper : A + T ≤ (2 : ℝ) • N)
    (hΔ : IsHilbertSchmidt (covarianceRootDiff N A T)) :
    ∃ hT : IsHilbertSchmidt T, Real.sqrt (hsSq T hT) ≤
      ‖N‖ * (Real.sqrt 2 + Real.sqrt (2 / c)) * Real.sqrt (hsSq _ hΔ) := by
  let C := covarianceNormalizer N
  let Δ := covarianceRootDiff N A T
  let X := CFC.sqrt (adjointCongr C (A + T))
  let Y := CFC.sqrt (adjointCongr C A)
  have hX : ‖X‖ ≤ Real.sqrt 2 := by
    rw [show X = CFC.sqrt (adjointCongr C (A + T)) from rfl,
      CFC.norm_sqrt _ (congr_nonneg N hB)]
    exact Real.sqrt_le_sqrt (congr_norm_le (strictlyPositive_of_coercive hc hN) (by norm_num) hB hBupper)
  have hY : ‖Y‖ ≤ Real.sqrt (2 / c) := by
    rw [show Y = CFC.sqrt (adjointCongr C A) from rfl, CFC.norm_sqrt _ (congr_nonneg N hA)]
    exact Real.sqrt_le_sqrt (norm_A_prime_le_two_div_c hc hN hA hAupper)
  have hid : adjointCongr C T = X * Δ + Δ * Y := (congr_eq_mul N T).trans (congruence_diff_eq hA hB)
  have hS : IsHilbertSchmidt (adjointCongr C T) :=
    hid ▸ isHilbertSchmidt_add (isHilbertSchmidt_mul_left hΔ) (isHilbertSchmidt_mul_right hΔ)
  have hSbound : Real.sqrt (hsSq _ hS) ≤
      (Real.sqrt 2 + Real.sqrt (2 / c)) * Real.sqrt (hsSq _ hΔ) := by
    have hrewrite : hsSq _ hS = hsSq (X * Δ + Δ * Y)
        (isHilbertSchmidt_add (isHilbertSchmidt_mul_left hΔ) (isHilbertSchmidt_mul_right hΔ)) := by
      simp only [hsSq, hid]
    rw [hrewrite]
    refine (hs_add_le (isHilbertSchmidt_mul_left hΔ) (isHilbertSchmidt_mul_right hΔ)).trans ?_
    rw [add_mul]
    exact add_le_add ((hs_left_le X hΔ).trans (mul_le_mul_of_nonneg_right hX (Real.sqrt_nonneg _)))
      ((hs_right_le Y hΔ).trans (mul_le_mul_of_nonneg_right hY (Real.sqrt_nonneg _)))
  let R := CFC.sqrt N
  have hR := (strictlyPositive_of_coercive hc hN).sqrt
  have hrecon : adjointCongr R (adjointCongr C T) = T := by
    rw [congr_eq_mul]
    change star R * (C * T * C * R) = T
    rw [hR.nonneg.isSelfAdjoint.star_eq]
    change R * (R⁻¹ʳ * T * R⁻¹ʳ * R) = T
    calc
      _ = (R * R⁻¹ʳ) * T * (R⁻¹ʳ * R) := by noncomm_ring
      _ = T := by rw [Ring.inverse_mul_cancel R hR.isUnit, Ring.mul_inverse_cancel R hR.isUnit,
        one_mul, mul_one]
  obtain ⟨hrec, hrecBound⟩ := adjointCongr_hsSq_le R hS
  have hT : IsHilbertSchmidt T := hrecon ▸ hrec
  refine ⟨hT, ?_⟩
  have h := Real.sqrt_le_sqrt hrecBound
  simp only [hsSq, hrecon] at h
  rw [Real.sqrt_mul (by positivity), show ‖R‖ ^ 4 = (‖R‖ ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg _), show ‖R‖ ^ 2 = ‖N‖ by
      simp [R, CFC.norm_sqrt _ (strictlyPositive_of_coercive hc hN).nonneg] ] at h
  exact h.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hSbound (norm_nonneg _))

/-- Eq. (11) in the physical covariance norm. No quarter-power factor is needed for the converse. -/
theorem hs_congruence_lower_bound {A T : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ 1 + T) (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op))
    (hB : 0 ≤ A + T) (hBupper : 0 ≤ (1 + T) - (A - 1))
    (hΔ : IsHilbertSchmidt (covarianceRootDiff (1 + T) A T)) :
    ∃ hT : IsHilbertSchmidt T, Real.sqrt (hsSq T hT) ≤
      ‖(1 : Op) + T‖ * (Real.sqrt 2 + Real.sqrt (2 / c)) * Real.sqrt (hsSq _ hΔ) := by
  have hBt : A + T ≤ (2 : ℝ) • ((1 : Op) + T) := by
    apply sub_nonneg.mp
    convert hBupper using 1
    simp only [two_smul]
    abel
  exact hs_normalized_lower_bound hc hN hA hAupper hB hBt hΔ

/-- The Araki–Yamagami common sum norm gives coercivity constant one plus the original constant. -/
theorem hs_sum_norm_converse {A T : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ 1 + T) (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op))
    (hB : 0 ≤ A + T) (hBupper : 0 ≤ (1 + T) - (A - 1))
    (hΔ : IsHilbertSchmidt (covarianceRootDiff (1 + (1 + T)) A T)) :
    ∃ hT : IsHilbertSchmidt T, Real.sqrt (hsSq T hT) ≤
      ‖(1 : Op) + (1 + T)‖ * (Real.sqrt 2 + Real.sqrt (2 / (1 + c))) * Real.sqrt (hsSq _ hΔ) := by
  have hNs : (1 + c) • (1 : Op) ≤ 1 + (1 + T) := by
    simpa only [add_smul, one_smul] using add_le_add_right hN (1 : Op)
  have hBt : A + T ≤ (2 : ℝ) • ((1 : Op) + T) := by
    apply sub_nonneg.mp
    convert hBupper using 1
    simp only [two_smul]
    abel
  have hBs : A + T ≤ (2 : ℝ) • ((1 : Op) + (1 + T)) :=
    hBt.trans (smul_le_smul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by norm_num))
  exact hs_normalized_lower_bound (by positivity) hNs hA hAupper hB hBs hΔ

/-- A non-Hilbert–Schmidt perturbation rules out a Hilbert–Schmidt difference of physical roots. -/
theorem not_hs_sqrt_diff_of_not_hs_T {A T : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ 1 + T) (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op))
    (hB : 0 ≤ A + T) (hBupper : 0 ≤ (1 + T) - (A - 1)) (hT : ¬ IsHilbertSchmidt T) :
    ¬ IsHilbertSchmidt (covarianceRootDiff (1 + T) A T) :=
  fun hΔ => hT (hs_congruence_lower_bound hc hN hA hAupper hB hBupper hΔ).choose

/-- The quarter-power factor and the converse give two-sided bounds for a radial block. -/
theorem quarterPower_block_comparison {A T W : Op} {c : ℝ} (hc : 0 < c)
    (hN : c • (1 : Op) ≤ 1 + T) (hA : 0 ≤ A) (hAupper : A ≤ (2 : ℝ) • (1 : Op))
    (hB : 0 ≤ A + T) (hBupper : 0 ≤ (1 + T) - (A - 1))
    (hW : IsHilbertSchmidt W) (hfactor : T = quarterRoot A * W * quarterRoot A) :
    ∃ (hΔ : IsHilbertSchmidt (covarianceRootDiff (1 + T) A T)) (hT : IsHilbertSchmidt T),
      hsSq _ hΔ ≤ ‖covarianceNormalizer (1 + T)‖ ^ 2 * hsSq W hW ∧
      Real.sqrt (hsSq T hT) ≤ ‖(1 : Op) + T‖ * (Real.sqrt 2 + Real.sqrt (2 / c)) *
        Real.sqrt (hsSq _ hΔ) := by
  have hf : A + T - A = quarterRoot A * W * quarterRoot A := by
    rw [add_sub_cancel_left, hfactor]
  obtain ⟨hΔ, hu⟩ := quarterPower_congruence_sqrt_hsSq_le hA hB hW hf (covarianceNormalizer (1 + T))
  obtain ⟨hT, hl⟩ := hs_congruence_lower_bound hc hN hA hAupper hB hBupper hΔ
  exact ⟨hΔ, hT, hu, hl⟩

section EmbeddedBlocks

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Orthogonal embedded copies of radial blocks give a summable weighted sequence
whenever the ambient operator is Hilbert--Schmidt. -/
private theorem block_hs_summable {w : Set H} (b : HilbertBasis w ℂ H) (m : ℕ → ℕ)
    (Δ : ℕ → H →L[ℂ] H) (U : K →L[ℂ] K)
    (J : ∀ n, Fin (m n) → H →ₗᵢ[ℂ] K)
    (hJ : Orthonormal ℂ (fun p : Σ n, Fin (m n) × w => J p.1 p.2.1 (b p.2.2)))
    (hU : ∀ n j x, U (J n j x) = J n j (Δ n x))
    (h : IsHilbertSchmidt U) :
    (∀ n, 0 < m n → IsHilbertSchmidt (Δ n)) ∧
      Summable (fun n => (m n : ℝ) * ∑' i : w, ‖Δ n (b i)‖ ^ 2) := by
  let v : (Σ n, Fin (m n) × w) → K := fun p => J p.1 p.2.1 (b p.2.2)
  obtain ⟨z, B, hsub, hB⟩ := hJ.toSubtypeRange.exists_hilbertBasis_extension
  let e (p : Σ n, Fin (m n) × w) : z := ⟨v p, hsub ⟨p, rfl⟩⟩
  have he : Function.Injective e := fun _ _ hp => hJ.linearIndependent.injective (congrArg Subtype.val hp)
  have hambient := (summable_norm_sq_apply_of_hilbertBasis z B h).comp_injective he
  have hEq (p : Σ n, Fin (m n) × w) : ‖U (B (e p))‖ ^ 2 = ‖Δ p.1 (b p.2.2)‖ ^ 2 := by
    rw [congrFun hB (e p)]
    change ‖U (J p.1 p.2.1 (b p.2.2))‖ ^ 2 = _
    rw [hU, LinearIsometry.norm_map]
  have hradial : Summable (fun p : Σ n, Fin (m n) × w => ‖Δ p.1 (b p.2.2)‖ ^ 2) :=
    hambient.congr hEq
  obtain ⟨hfibers, hblocks⟩ := (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).1 hradial
  have hcopy (n : ℕ) := (summable_prod_of_nonneg
    (f := fun p : Fin (m n) × w => ‖Δ n (b p.2)‖ ^ 2) (fun _ => sq_nonneg _)).1 (hfibers n)
  refine ⟨fun n hn => ⟨w, b, (hcopy n).1 ⟨0, hn⟩⟩, hblocks.congr (fun n => ?_)⟩
  rw [Summable.tsum_prod (hfibers n)]
  change (∑' _j : Fin (m n), ∑' i : w, ‖Δ n (b i)‖ ^ 2) = _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end EmbeddedBlocks

/-- Uniform covariance and lower-amplitude hypotheses for the positive harmonic degrees. -/
structure ConverseBlockBounds (D : ℕ) (A T : ℕ → Op) (c M c₀ : ℝ) : Prop where
  coercivity_pos : 0 < c
  amplitude_pos : 0 < c₀
  coercive : ∀ n, c • (1 : Op) ≤ 1 + T (n + 1)
  normalizer_upper : ∀ n, ‖(1 : Op) + T (n + 1)‖ ≤ M
  reference_nonneg : ∀ n, 0 ≤ A (n + 1)
  reference_upper : ∀ n, A (n + 1) ≤ (2 : ℝ) • (1 : Op)
  perturbed_nonneg : ∀ n, 0 ≤ A (n + 1) + T (n + 1)
  perturbed_upper : ∀ n, 0 ≤ (1 + T (n + 1)) - (A (n + 1) - 1)
  amplitude_lower : ∀ n, ∃ hT : IsHilbertSchmidt (T (n + 1)),
    c₀ / ((((n + 1 : ℕ) : ℝ) + ((D : ℝ) - 2) / 2 - 1) *
      (((n + 1 : ℕ) : ℝ) + ((D : ℝ) - 2) / 2)) ≤ Real.sqrt (hsSq _ hT)

/-- The harmonic multiplicity times the radial basis-square sum in degree `ℓ`.
The cutoff theorems supply Hilbert–Schmidt hypotheses for the real-valued sums. -/
def converseModeWeight (D : ℕ) (A T : ℕ → Op) (ℓ : ℕ) : ℝ :=
  let b := (exists_hilbertBasis ℂ H).choose_spec.choose
  let Δ := covarianceRootDiff (1 + T ℓ) (A ℓ) (T ℓ)
  (harmonicMult D ℓ : ℝ) * ∑' i, ‖Δ (b i)‖ ^ 2

section Angular

set_option maxHeartbeats 180000

private theorem converse_weight_lower {D : ℕ} {A T : ℕ → Op} {c M c₀ : ℝ}
    (bounds : ConverseBlockBounds (H := H) D A T c M c₀)
    (hΔ : ∀ n : ℕ, IsHilbertSchmidt (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1))))
    (hD : 6 ≤ D) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, a * leadingModeWeight D (n + 1) ≤ converseModeWeight (H := H) D A T (n + 1) := by
  let K := Real.sqrt 2 + Real.sqrt (2 / c)
  have hK : 0 < K := add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (by norm_num)) (Real.sqrt_nonneg _)
  have hM : 0 ≤ M := (norm_nonneg _).trans (bounds.normalizer_upper 0)
  let m := (M + 1) * K
  have hm : 0 < m := mul_pos (add_pos_of_nonneg_of_pos hM zero_lt_one) hK
  have hc₀ := bounds.amplitude_pos
  refine ⟨(c₀ / m) ^ 2, pow_pos (div_pos hc₀ hm) _, ?_⟩
  intro n
  let q := (((n + 1 : ℕ) : ℝ) + ((D : ℝ) - 2) / 2 - 1) *
    (((n + 1 : ℕ) : ℝ) + ((D : ℝ) - 2) / 2)
  have hD' : (6 : ℝ) ≤ D := by exact_mod_cast hD
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hq : 0 < q := mul_pos (by linarith) (by linarith)
  obtain ⟨ht, htLower⟩ := bounds.amplitude_lower n
  have hqLower : c₀ / q ≤ Real.sqrt (hsSq (T (n + 1)) ht) := htLower
  obtain ⟨_, hroot⟩ := hs_congruence_lower_bound bounds.coercivity_pos (bounds.coercive n)
    (bounds.reference_nonneg n) (bounds.reference_upper n) (bounds.perturbed_nonneg n)
    (bounds.perturbed_upper n) (hΔ n)
  let S := hsSq _ (hΔ n)
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hnorm : ‖(1 : Op) + T (n + 1)‖ ≤ M + 1 :=
    (bounds.normalizer_upper n).trans (le_add_of_nonneg_right zero_le_one)
  have hscaled : c₀ / q ≤ m * Real.sqrt S := by
    exact hqLower.trans (hroot.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnorm hK.le) (Real.sqrt_nonneg S)))
  have hdiv : c₀ / m / q ≤ Real.sqrt S := by
    rw [div_right_comm]
    exact (div_le_iff₀ hm).2 (by simpa only [mul_comm] using hscaled)
  have hsq := pow_le_pow_left₀ (div_nonneg (div_nonneg hc₀.le hm.le) hq.le) hdiv 2
  rw [Real.sq_sqrt hS, div_pow] at hsq
  let mult : ℝ := harmonicMult D (n + 1)
  change (c₀ / m) ^ 2 * (mult / q ^ 2) ≤ mult * S
  rw [← mul_div_assoc, mul_comm ((c₀ / m) ^ 2), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)

private theorem converse_sum_lower {D : ℕ} {A T : ℕ → Op} {c M c₀ : ℝ}
    (bounds : ConverseBlockBounds (H := H) D A T c M c₀)
    (hΔ : ∀ n : ℕ, IsHilbertSchmidt (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1))))
    (hD : 6 ≤ D) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℕ,
      a * (∑ n ∈ Finset.range L, leadingModeWeight D (n + 1)) ≤
        ∑ n ∈ Finset.range L, converseModeWeight (H := H) D A T (n + 1) := by
  obtain ⟨a, ha, h⟩ := converse_weight_lower bounds hΔ hD
  refine ⟨a, ha, fun L => ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ => h n

/-- The six-dimensional partial trace grows at least logarithmically. -/
theorem converse_partial_trace_bounds_D6 {A T : ℕ → Op} {c M c₀ : ℝ}
    (bounds : ConverseBlockBounds (H := H) 6 A T c M c₀)
    (hΔ : ∀ n : ℕ, IsHilbertSchmidt (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1)))) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℕ, 2 ≤ L →
      a * Real.log L ≤ ∑ n ∈ Finset.range L, converseModeWeight (H := H) 6 A T (n + 1) := by
  obtain ⟨a, ha, h⟩ := converse_sum_lower bounds hΔ (by norm_num)
  obtain ⟨b, _, hb, _, hg⟩ := leadingModeWeight_sum_six_bounds
  refine ⟨a * b, mul_pos ha hb, fun L hL => ?_⟩
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hg L hL).1 ha.le).trans (h L)

/-- In higher dimensions the partial trace grows at least as the indicated power of the cutoff. -/
theorem converse_partial_trace_bounds_D_ge_7 {D : ℕ} {A T : ℕ → Op} {c M c₀ : ℝ}
    (hD : 7 ≤ D)
    (bounds : ConverseBlockBounds (H := H) D A T c M c₀)
    (hΔ : ∀ n : ℕ, IsHilbertSchmidt (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1)))) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℕ, 1 ≤ L →
      a * (L : ℝ) ^ (D - 6) ≤ ∑ n ∈ Finset.range L, converseModeWeight (H := H) D A T (n + 1) := by
  obtain ⟨a, ha, h⟩ := converse_sum_lower bounds hΔ (by omega)
  obtain ⟨b, _, hb, _, hg⟩ := leadingModeWeight_sum_ge_seven_bounds D hD
  refine ⟨a * b, mul_pos ha hb, fun L hL => ?_⟩
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hg L hL).1 ha.le).trans (h L)

/-- Positive-degree cutoffs tend to infinity in every spacetime dimension at least six. -/
theorem converse_eq71_diverges_of_D_ge_6 {D : ℕ} {A T : ℕ → Op} {c M c₀ : ℝ}
    (hD : 6 ≤ D)
    (bounds : ConverseBlockBounds (H := H) D A T c M c₀)
    (hΔ : ∀ n : ℕ, IsHilbertSchmidt (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1)))) :
    Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L, converseModeWeight (H := H) D A T (n + 1)) atTop atTop ∧
      ¬ Summable (converseModeWeight (H := H) D A T) := by
  have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlimit : Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L, converseModeWeight (H := H) D A T (n + 1))
      atTop atTop := by
    rcases eq_or_lt_of_le hD with h | h
    · subst D
      obtain ⟨a, ha, hl⟩ := converse_partial_trace_bounds_D6 bounds hΔ
      apply tendsto_atTop_mono' _ (eventually_atTop.2 ⟨2, hl⟩)
      exact (tendsto_const_mul_atTop_of_pos ha).2 (Real.tendsto_log_atTop.comp hcast)
    · obtain ⟨a, ha, hl⟩ := converse_partial_trace_bounds_D_ge_7 (by omega) bounds hΔ
      apply tendsto_atTop_mono' _ (eventually_atTop.2 ⟨1, hl⟩)
      exact (tendsto_const_mul_pow_atTop (show D - 6 ≠ 0 by omega) ha).comp hcast
  refine ⟨hlimit, fun hs => ?_⟩
  have hn := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n =>
    mul_nonneg (Nat.cast_nonneg (harmonicMult D (n + 1))) (tsum_nonneg fun _ => sq_nonneg _))).2 hlimit
  exact hn ((summable_nat_add_iff 1).2 hs)

/-- A bounded operator with these orthogonal harmonic blocks fails the Hilbert–Schmidt condition.
The positive-degree family alone suffices, even when some radial root differences are not HS. -/
theorem not_hs_eq71_operator_of_D_ge_6 {D : ℕ} {A T : ℕ → Op} {c M c₀ : ℝ} {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (hD : 6 ≤ D) (bounds : ConverseBlockBounds (H := H) D A T c M c₀)
    (U : K →L[ℂ] K) (J : ∀ n, Fin (harmonicMult D (n + 1)) → H →ₗᵢ[ℂ] K)
    (hJ : Orthonormal ℂ (fun p : Σ n, Fin (harmonicMult D (n + 1)) ×
        (exists_hilbertBasis ℂ H).choose => J p.1 p.2.1 ((exists_hilbertBasis ℂ H).choose_spec.choose p.2.2)))
    (hU : ∀ (n) (j : Fin (harmonicMult D (n + 1))) x,
      U (J n j x) = J n j (covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1)) x)) :
    ¬ IsHilbertSchmidt U := by
  intro h
  let b := (exists_hilbertBasis ℂ H).choose_spec.choose
  let m (n : ℕ) := harmonicMult D (n + 1)
  let Δ (n : ℕ) := covarianceRootDiff (H := H) (1 + T (n + 1)) (A (n + 1)) (T (n + 1))
  obtain ⟨a, _, ha, _, haBound⟩ := harmonicMult_bounds D (by omega)
  have hm (n : ℕ) : 0 < m n := by
    have hpos : 0 < a * ((n + 1 : ℕ) : ℝ) ^ (D - 3) := by positivity
    exact_mod_cast (hpos.trans_le (haBound (n + 1) (by omega)).1)
  have hΔ : ∀ n, IsHilbertSchmidt (Δ n) :=
    fun n => (block_hs_summable b m Δ U J hJ hU h).1 n (hm n)
  apply (converse_eq71_diverges_of_D_ge_6 hD bounds hΔ).2
  exact (summable_nat_add_iff 1).1 (block_hs_summable b m Δ U J hJ hU h).2

end Angular

end NullConeGravity
