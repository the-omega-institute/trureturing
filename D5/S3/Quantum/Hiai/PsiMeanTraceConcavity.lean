/- GID: D5/S3/Quantum/Hiai/PsiMeanTraceConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/PsiMeanTraceConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Hiai mean-trace concavity on the true HS space with attained endpoint optimizers. -/

import D5.S3.Quantum.Hiai.GeometricMeanOrder
import D5.S3.Quantum.Hiai.InverseMeanVariational
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

noncomputable section
namespace HiaiHSPower
open LownerHeinzTheorem GeneralizedPerspectiveFunction HilbertSchmidtOperatorSpace
  OperatorGeometricMean LiebAndoTrace
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [FiniteDimensional ℂ H]

/-- The public scalar bridge for every vector determines the full HS operator. -/
theorem perspective_lr_eq (s : ℝ) {A B : L H}
    (hA : A ∈ pdSet) (hB : B ∈ pdSet) :
    operatorPowerMean (ℋ := HSOp H) s 1 (leftMulHS A) (rightMulHS B) =
      leftMulHS (A ^ s) * rightMulHS (B ^ (1 - s)) := by
  let T := operatorPowerMean (ℋ := HSOp H) s 1 (leftMulHS A) (rightMulHS B)
  let S := leftMulHS (A ^ s) * rightMulHS (B ^ (1 - s))
  have hT : IsSelfAdjoint T := by
    dsimp [T, operatorPowerMean, GeneralizedPerspective]
    apply IsSelfAdjoint.conjugate_self
    · exact IsSelfAdjoint.cfc
    · exact IsSelfAdjoint.cfc
  have hL : IsSelfAdjoint (leftMulHS (A ^ s)) := by
    have hs : IsSelfAdjoint (A ^ s) := .of_nonneg CFC.rpow_nonneg
    change star (leftMulHS (A ^ s)) = _
    simp only [leftMulHS_star, hs.star_eq]
  have hR : IsSelfAdjoint (rightMulHS (B ^ (1 - s))) := by
    have hs : IsSelfAdjoint (B ^ (1 - s)) := .of_nonneg CFC.rpow_nonneg
    change star (rightMulHS (B ^ (1 - s))) = _
    simp only [rightMulHS_star, hs.star_eq]
  have hS : IsSelfAdjoint S :=
    (hL.commute_iff hR).mp (leftMulHS_rightMulHS_commute _ _)
  have hdiag (V : HSOp H) : (inner ℂ V (T V)).re = (inner ℂ V (S V)).re := by
    have hp := phiK_operatorPowerMean_eq_liebTraceMap (ℋ := H) (s := s)
      (star (toOp V)) A B hA hB
    change phiK (star (toOp V)) T = _ at hp
    simp only [phiK, star_star] at hp
    rw [hp]
    simp only [liebTraceMap, star_star]
    change traceRe (A ^ s * toOp V * B ^ (1 - s) * star (toOp V)) = _
    change _ = (inner ℂ (ofOp (toOp V))
      (ofOp (A ^ s * (toOp V * B ^ (1 - s))))).re
    rw [re_hsInner_eq_traceRe]
    unfold traceRe
    congr 1
    have hc := LinearMap.trace_mul_comm (R := ℂ) (M := H)
      (A ^ s * toOp V * B ^ (1 - s)).toLinearMap (star (toOp V)).toLinearMap
    simpa only [ContinuousLinearMap.toLinearMap_mul, mul_assoc] using hc
  have heq : T.toLinearMap = S.toLinearMap :=
    (ext_inner_map T.toLinearMap S.toLinearMap).mp (by
      intro V
      have hd : (inner ℂ (T V) V).re = (inner ℂ (S V) V).re := by
        calc
          _ = (inner ℂ V (T V)).re := inner_re_symm (𝕜 := ℂ) _ _
          _ = (inner ℂ V (S V)).re := hdiag V
          _ = _ := inner_re_symm (𝕜 := ℂ) _ _
      calc
        inner ℂ (T V) V = ((inner ℂ (T V) V).re : ℂ) :=
          (hT.isSymmetric.coe_re_inner_apply_self V).symm
        _ = ((inner ℂ (S V) V).re : ℂ) := congrArg Complex.ofReal hd
        _ = inner ℂ (S V) V := hS.isSymmetric.coe_re_inner_apply_self V)
  exact ContinuousLinearMap.coe_injective heq

end HiaiHSPower

namespace HiaiHSPower
open LownerHeinzTheorem GeneralizedPerspectiveFunction HilbertSchmidtOperatorSpace
  OperatorGeometricMean LiebAndoTrace HiaiGeometricMean
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [FiniteDimensional ℂ H]

local instance : Nontrivial (HSOp H) := by
  delta HSOp
  infer_instance

/-- Product of the left and right actions on the true Hilbert-Schmidt space. -/
noncomputable def lr (X D : L H) : L (HSOp H) := leftMulHS X * rightMulHS D

private lemma pd_strict {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [Nontrivial K] {X : L K} (hX : X ∈ pdSet) :
    IsStrictlyPositive X :=
  (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos X (ha := hX.1)).2 hX.2

private lemma strict_pd {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [Nontrivial K] {X : L K} (hX : IsStrictlyPositive X) : X ∈ pdSet :=
  ⟨hX.isSelfAdjoint, fun _ hx ↦ hX.spectrum_pos hx⟩

private lemma pd_power (s : ℝ) {X : L H} (hX : X ∈ pdSet) : X ^ s ∈ pdSet :=
  strict_pd ((pd_strict hX).rpow X s)

/-- Positivity comes from the commuting actions, without commuting `X` and `D`. -/
theorem lr_pd {X D : L H} (hX : X ∈ pdSet) (hD : D ∈ pdSet) : lr X D ∈ pdSet := by
  exact strict_pd (((pd_strict (leftMulHS_pdSet hX)).commute_iff
    (pd_strict (rightMulHS_pdSet hD))).1 (leftMulHS_rightMulHS_commute X D))

private lemma power_cont (s : ℝ) {X : L H} (hX : X ∈ pdSet) :
    ContinuousOn (fun t : ℝ ↦ t ^ s) (spectrum ℝ X) := by
  intro t ht
  exact (Real.continuousAt_rpow_const t s (Or.inl (hX.2 ht).ne')).continuousWithinAt

private lemma left_power (s : ℝ) {X : L H} (hX : X ∈ pdSet) :
    (leftMulHS X) ^ s = leftMulHS (X ^ s) := by
  have hm := leftMulHS_cfcR (ℋ := H) (fun t : ℝ ↦ t ^ s) X hX.1 (power_cont s hX)
  simpa only [cfcR, LownerHeinzCore.cfcR,
    ← CFC.rpow_eq_cfc_real (pd_strict hX).nonneg,
    ← CFC.rpow_eq_cfc_real (pd_strict (leftMulHS_pdSet hX)).nonneg] using hm.symm

private lemma right_power (s : ℝ) {X : L H} (hX : X ∈ pdSet) :
    (rightMulHS X) ^ s = rightMulHS (X ^ s) := by
  have hm := rightMulHS_cfcR (ℋ := H) (fun t : ℝ ↦ t ^ s) X hX.1 (power_cont s hX)
  simpa only [cfcR, LownerHeinzCore.cfcR,
    ← CFC.rpow_eq_cfc_real (pd_strict hX).nonneg,
    ← CFC.rpow_eq_cfc_real (pd_strict (rightMulHS_pdSet hX)).nonneg] using hm.symm

private lemma inverse_sqrt {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {X : L K} (hX : IsStrictlyPositive X) :
    CFC.sqrt (Ring.inverse X) = X ^ (-1 / 2 : ℝ) := by
  rw [CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one hX,
    CFC.rpow_rpow X (-1) (1 / 2) (by norm_num) hX]
  norm_num

private lemma normalized_power (s : ℝ) {A B : L H} (hA : A ∈ pdSet) (hB : B ∈ pdSet) :
    (lr A (B ^ (-1 : ℝ))) ^ s = lr (A ^ s) (B ^ (-s)) := by
  let R := rightMulHS (B ^ (1 / 2 : ℝ))
  let I := rightMulHS (B ^ (-1 / 2 : ℝ))
  have hmid : I * leftMulHS A * I = lr A (B ^ (-1 : ℝ)) := by
    ext V
    change A * (toOp V * B ^ (-1 / 2 : ℝ)) * B ^ (-1 / 2 : ℝ) =
      A * (toOp V * B ^ (-1 : ℝ))
    rw [mul_assoc, mul_assoc, ← CFC.rpow_add (pd_strict hB).isUnit]
    norm_num
  have h := (mean_eq_operatorPowerMean s (rightMulHS_pdSet hB)
    (pd_strict (leftMulHS_pdSet hA)).nonneg).trans (perspective_lr_eq s hA hB)
  unfold mean at h
  simp only [CFC.conjSqrt_apply] at h
  rw [inverse_sqrt (pd_strict (rightMulHS_pdSet hB)), CFC.sqrt_eq_rpow,
    right_power (1 / 2) hB, right_power (-1 / 2) hB] at h
  change R * (I * leftMulHS A * I) ^ s * R = lr (A ^ s) (B ^ (1 - s)) at h
  rw [hmid] at h
  have hfactor : lr (A ^ s) (B ^ (1 - s)) = R * lr (A ^ s) (B ^ (-s)) * R := by
    ext V
    change A ^ s * (toOp V * B ^ (1 - s)) =
      (A ^ s * (toOp V * B ^ (1 / 2 : ℝ)) * B ^ (-s)) * B ^ (1 / 2 : ℝ)
    simp only [mul_assoc]
    rw [← CFC.rpow_add (pd_strict hB).isUnit, ← CFC.rpow_add (pd_strict hB).isUnit]
    congr 3
    ring
  rw [hfactor] at h
  have hRunit : IsUnit R := (pd_strict (rightMulHS_pdSet (pd_power (1 / 2) hB))).isUnit
  exact hRunit.mul_left_inj.mp (hRunit.mul_right_inj.mp (by simpa only [mul_assoc] using h))

/-- Every real spectral power factors across the commuting HS actions. -/
theorem lr_power (s : ℝ) {X D : L H} (hX : X ∈ pdSet) (hD : D ∈ pdSet) :
    (lr X D) ^ s = lr (X ^ s) (D ^ s) := by
  have h := normalized_power s hX (pd_power (-1) hD)
  have h1 : (D ^ (-1 : ℝ)) ^ (-1 : ℝ) = D := by
    rw [CFC.rpow_rpow D (-1) (-1) (by norm_num) (pd_strict hD)]
    norm_num [CFC.rpow_one D (pd_strict hD).nonneg]
  have hs : (D ^ (-1 : ℝ)) ^ (-s) = D ^ s := by
    rw [CFC.rpow_rpow D (-1) (-s) (by norm_num) (pd_strict hD)]
    ring_nf
  simpa only [h1, hs] using h

/-- The common right factor survives the genuine geometric mean. -/
theorem mean_lr_common (θ : ℝ) {X Y D : L H}
    (hX : X ∈ pdSet) (hY : Y ∈ pdSet) (hD : D ∈ pdSet) :
    mean θ (lr X D) (lr Y D) = lr (mean θ X Y) D := by
  let U := X ^ (-1 / 2 : ℝ)
  let V := D ^ (-1 / 2 : ℝ)
  let S := X ^ (1 / 2 : ℝ)
  let T := D ^ (1 / 2 : ℝ)
  let M := U * Y * U
  have hsX := pd_strict hX
  have hsD := pd_strict hD
  have hM : M ∈ pdSet := by
    exact strict_pd (((hsX.rpow X (-1 / 2)).isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
      Y U (CFC.rpow_nonneg (a := X) (y := (-1 / 2 : ℝ))).isSelfAdjoint).2 (pd_strict hY))
  have hcancel : V * D * V = 1 := by
    dsimp [V]
    conv_lhs => arg 1; arg 2; rw [← CFC.rpow_one D hsD.nonneg]
    rw [← CFC.rpow_add hsD.isUnit, ← CFC.rpow_add hsD.isUnit]
    norm_num [CFC.rpow_zero D hsD.nonneg]
  have hmid : lr U V * lr Y D * lr U V = leftMulHS M := by
    ext K
    change U * (Y * (U * toOp K * V) * D) * V = M * toOp K
    calc
      _ = (U * Y * U) * toOp K * (V * D * V) := by noncomm_ring
      _ = _ := by rw [hcancel]; simp [M]
  have hhalf : T * T = D := by
    dsimp [T]
    rw [← CFC.rpow_add hsD.isUnit]
    norm_num [CFC.rpow_one D hsD.nonneg]
  have hout : lr S T * leftMulHS (M ^ θ) * lr S T = lr (S * M ^ θ * S) D := by
    ext K
    change S * (M ^ θ * (S * toOp K * T)) * T = (S * M ^ θ * S) * (toOp K * D)
    calc
      _ = (S * M ^ θ * S) * toOp K * (T * T) := by noncomm_ring
      _ = _ := by rw [hhalf]; simp only [mul_assoc]
  unfold mean
  simp only [CFC.conjSqrt_apply]
  rw [inverse_sqrt (pd_strict (lr_pd hX hD)), inverse_sqrt hsX,
    CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow, lr_power (1 / 2) hX hD,
    lr_power (-1 / 2) hX hD]
  change lr S T * (lr U V * lr Y D * lr U V) ^ θ * lr S T = lr (S * M ^ θ * S) D
  rw [hmid, left_power θ hM, hout]

end HiaiHSPower

namespace HiaiHSMeanTrace
open LownerHeinzTheorem GeneralizedPerspectiveFunction HilbertSchmidtOperatorSpace
  OperatorGeometricMean LiebAndoTrace HiaiGeometricMean HiaiHSPower
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [FiniteDimensional ℂ H]

local instance : Nontrivial (HSOp H) := by
  delta HSOp
  infer_instance

private lemma pd_strict {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [Nontrivial K] {X : L K} (hX : X ∈ pdSet) :
    IsStrictlyPositive X :=
  (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos X (ha := hX.1)).2 hX.2

private lemma pd_power (s : ℝ) {X : L H} (hX : X ∈ pdSet) : X ^ s ∈ pdSet :=
  ⟨((pd_strict hX).rpow X s).isSelfAdjoint, fun _ hx ↦ ((pd_strict hX).rpow X s).spectrum_pos hx⟩

/-- The jointly concave Lieb lift, using the genuine HS inner product. -/
noncomputable def powerProduct (p : ℝ) (A W : L H) : L (HSOp H) :=
  lr (A ^ p) (W ^ (1 - p))

private lemma product_pd (p : ℝ) {A W : L H} (hA : A ∈ pdSet) (hW : W ∈ pdSet) :
    powerProduct p A W ∈ pdSet := lr_pd (pd_power p hA) (pd_power (1 - p) hW)

private lemma product_concave {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConcaveOn (pdSet (ℋ := H)) (pdSet (ℋ := H)) (powerProduct p) := by
  intro A₀ A₁ W₀ W₁ t hA₀ hA₁ hW₀ hW₁ ht0 ht1
  have hAm := pdSet_convexCombo hA₀ hA₁ ht0 ht1
  have hWm := pdSet_convexCombo hW₀ hW₁ ht0 ht1
  have hc := operatorPowerMean_jointlyConcaveOn_pdSet (ℋ := HSOp H) (α := p) (β := 1)
    hp ⟨by norm_num, by norm_num⟩ (leftMulHS_pdSet hA₀) (leftMulHS_pdSet hA₁)
    (rightMulHS_pdSet hW₀) (rightMulHS_pdSet hW₁) ht0 ht1
  have hleft : (1 - t) • leftMulHS A₀ + t • leftMulHS A₁ =
      leftMulHS ((1 - t) • A₀ + t • A₁) := by
    ext V
    change (1 - t) • (A₀ * toOp V) + t • (A₁ * toOp V) =
      ((1 - t) • A₀ + t • A₁) * toOp V
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright : (1 - t) • rightMulHS W₀ + t • rightMulHS W₁ =
      rightMulHS ((1 - t) • W₀ + t • W₁) := by
    ext V
    change (1 - t) • (toOp V * W₀) + t • (toOp V * W₁) =
      toOp V * ((1 - t) • W₀ + t • W₁)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  rw [hleft, hright, perspective_lr_eq p hA₀ hW₀, perspective_lr_eq p hA₁ hW₁,
    perspective_lr_eq p hAm hWm] at hc
  exact hc

/-- The two Lieb lifts are mixed together before evaluating at a vector. -/
theorem meanProduct_triple_concave {p θ t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    {A₀ A₁ B₀ B₁ W₀ W₁ : L H}
    (hA₀ : A₀ ∈ pdSet) (hA₁ : A₁ ∈ pdSet)
    (hB₀ : B₀ ∈ pdSet) (hB₁ : B₁ ∈ pdSet)
    (hW₀ : W₀ ∈ pdSet) (hW₁ : W₁ ∈ pdSet) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • mean θ (powerProduct p B₀ W₀) (powerProduct p A₀ W₀) +
      t • mean θ (powerProduct p B₁ W₁) (powerProduct p A₁ W₁) ≤
      mean θ (powerProduct p ((1 - t) • B₀ + t • B₁) ((1 - t) • W₀ + t • W₁))
        (powerProduct p ((1 - t) • A₀ + t • A₁) ((1 - t) • W₀ + t • W₁)) := by
  have hPA₀ := product_pd p hA₀ hW₀
  have hPA₁ := product_pd p hA₁ hW₁
  have hPB₀ := product_pd p hB₀ hW₀
  have hPB₁ := product_pd p hB₁ hW₁
  have hPBm := product_pd p (pdSet_convexCombo hB₀ hB₁ ht0 ht1)
    (pdSet_convexCombo hW₀ hW₁ ht0 ht1)
  exact (mean_jointlyConcave hθ hPB₀ hPB₁ hPA₀ hPA₁ ht0 ht1).trans
    (mean_mono hθ (pdSet_convexCombo hPB₀ hPB₁ ht0 ht1) hPBm
      (pd_strict (pdSet_convexCombo hPA₀ hPA₁ ht0 ht1)).nonneg
      (product_concave hp hB₀ hB₁ hW₀ hW₁ ht0 ht1)
      (product_concave hp hA₀ hA₁ hW₀ hW₁ ht0 ht1))

/-- The triple pairing permits arbitrary `Z`, including singular and zero operators. -/
noncomputable def gamma (p θ : ℝ) (Z A B W : L H) : ℝ :=
  traceRe (star Z * mean θ (B ^ p) (A ^ p) * Z * W ^ (1 - p))

private lemma phi_lr (Z M D : L H) : phiK (star Z) (lr M D) = traceRe (star Z * M * Z * D) := by
  unfold phiK lr traceRe
  simp only [star_star]
  change (inner ℂ (ofOp Z) (ofOp (M * (Z * D)))).re = _
  simpa only [mul_assoc] using
    re_hsInner_eq_traceRe (ℋ := H) (X := Z) (Y := M * (Z * D))

private lemma phi_meanProduct (p θ : ℝ) (Z : L H) {A B W : L H}
    (hA : A ∈ pdSet) (hB : B ∈ pdSet) (hW : W ∈ pdSet) :
    phiK (star Z) (mean θ (powerProduct p B W) (powerProduct p A W)) = gamma p θ Z A B W := by
  unfold powerProduct
  rw [mean_lr_common θ (pd_power p hB) (pd_power p hA) (pd_power (1 - p) hW), phi_lr]
  rfl

/-- Gamma is jointly concave in all three positive definite inputs, with one shared mixture. -/
theorem hs_gamma_triple_concave {p θ t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (Z : L H)
    {A₀ A₁ B₀ B₁ W₀ W₁ : L H}
    (hA₀ : A₀ ∈ pdSet) (hA₁ : A₁ ∈ pdSet)
    (hB₀ : B₀ ∈ pdSet) (hB₁ : B₁ ∈ pdSet)
    (hW₀ : W₀ ∈ pdSet) (hW₁ : W₁ ∈ pdSet) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * gamma p θ Z A₀ B₀ W₀ + t * gamma p θ Z A₁ B₁ W₁ ≤
      gamma p θ Z ((1 - t) • A₀ + t • A₁) ((1 - t) • B₀ + t • B₁)
        ((1 - t) • W₀ + t • W₁) := by
  have h := phiK_mono (star Z)
    (meanProduct_triple_concave hp hθ hA₀ hA₁ hB₀ hB₁ hW₀ hW₁ ht0 ht1)
  rw [phiK_add, phiK_smul, phiK_smul,
    phi_meanProduct p θ Z hA₀ hB₀ hW₀, phi_meanProduct p θ Z hA₁ hB₁ hW₁,
    phi_meanProduct p θ Z (pdSet_convexCombo hA₀ hA₁ ht0 ht1)
      (pdSet_convexCombo hB₀ hB₁ ht0 ht1) (pdSet_convexCombo hW₀ hW₁ ht0 ht1)] at h
  exact h

#print axioms hs_gamma_triple_concave
end HiaiHSMeanTrace

namespace D5.S3.Quantum.Hiai.ForwardTraceYoung
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix D5.S3.Quantum.Hiai.InverseMeanVariational
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- The maximized forward trace-Young objective. -/
def objective (p : ℝ) (M W : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (M * W ^ (1 - p))).re - (1 - p) * (Matrix.trace W).re

private lemma holder_trace {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (Matrix.trace (M * W ^ (1 - p))).re ≤
      tracePower (1 / p) M ^ p * (Matrix.trace W).re ^ (1 - p) ∧
    0 ≤ tracePower (1 / p) M ∧ 0 ≤ (Matrix.trace W).re := by
  let U := M ^ (1 / 2 : ℝ)
  let V := W ^ ((1 - p) / 2)
  let a := 2 / p
  let b := 2 / (1 - p)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hU : Uᴴ = U := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := M))).star_eq
  have hV : Vᴴ = V := (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := W))).star_eq
  have hUU : U * U = M := by
    dsimp [U]
    rw [← CFC.rpow_add hM.isUnit]
    norm_num
    exact CFC.rpow_one M hM.posSemidef.nonneg
  have hVV : V * V = W ^ (1 - p) := by
    dsimp [V]
    rw [← CFC.rpow_add hW.isUnit]
    congr 1
    ring
  have hUV : schattenNorm (U * V) 2 ^ (2 : ℝ) =
      (Matrix.trace (M * W ^ (1 - p))).re := by
    rw [norm_rpow_gram _ (by norm_num)]
    norm_num only [tracePower, show (2 : ℝ) / 2 = 1 by norm_num]
    rw [CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self (U * V)).nonneg,
      Matrix.conjTranspose_mul, hU, hV]
    have hg : V * U * (U * V) = V * M * V := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc V U U, hUU]
    rw [hg, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (V * V) M, hVV]
  have hnormU : schattenNorm U a ^ a = tracePower (1 / p) M := by
    rw [norm_rpow_gram _ ha, hU, hUU]
    congr 1
    dsimp [a]
    ring
  have hnormV : schattenNorm V b ^ b = (Matrix.trace W).re := by
    rw [norm_rpow_gram _ hb, hV, hVV]
    dsimp [tracePower]
    rw [CFC.rpow_rpow W (1 - p) (b / 2) (by linarith) hW.isStrictlyPositive]
    have he : (1 - p) * (b / 2) = 1 := by dsimp [b]; field_simp [show 1 - p ≠ 0 by linarith]
    rw [he, CFC.rpow_one W hW.posSemidef.nonneg]
  have hTM : 0 ≤ tracePower (1 / p) M := by
    rw [← hnormU]
    exact Real.rpow_nonneg (schattenNorm_nonneg U _) _
  have hTW : 0 ≤ (Matrix.trace W).re := by
    rw [← hnormV]
    exact Real.rpow_nonneg (schattenNorm_nonneg V _) _
  have hh := schattenNorm_mul_le U V (by norm_num : (0 : ℝ) < 2) ha hb
    (by dsimp [a, b]; field_simp; ring : 1 / (2 : ℝ) = 1 / a + 1 / b)
  have hh2 := Real.rpow_le_rpow (schattenNorm_nonneg (U * V) _) hh (by norm_num : (0 : ℝ) ≤ 2)
  rw [hUV, Real.mul_rpow (schattenNorm_nonneg U _) (schattenNorm_nonneg V _)] at hh2
  have heU : schattenNorm U  a ^ (2 : ℝ) = tracePower (1 / p) M ^ p := by
    rw [← hnormU, ← Real.rpow_mul (schattenNorm_nonneg U _)]
    have he : a * p = 2 := by dsimp [a]; field_simp
    rw [he]
  have heV : schattenNorm V b ^ (2 : ℝ) = (Matrix.trace W).re ^ (1 - p) := by
    rw [← hnormV, ← Real.rpow_mul (schattenNorm_nonneg V _)]
    have he : b * (1 - p) = 2 := by dsimp [b]; field_simp [show 1 - p ≠ 0 by linarith]
    rw [he]
  exact ⟨by simpa only [heU, heV] using hh2, hTM, hTW⟩

/-- Universal forward Young bound for arbitrary noncommuting positive definite matrices. -/
theorem forward_trace_young {M W : Matrix d d ℂ} (hM : M.PosDef) (hW : W.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    objective p M W ≤ p * tracePower (1 / p) M := by
  by_cases h1 : p = 1
  · subst p
    simp [objective, tracePower, CFC.rpow_one M hM.posSemidef.nonneg,
      CFC.rpow_zero W hW.posSemidef.nonneg]
  · have hp1' : p < 1 := lt_of_le_of_ne hp1 h1
    obtain ⟨hh, hTM, hTW⟩ := holder_trace hM hW hp hp1'
    have hy := Real.geom_mean_le_arith_mean2_weighted hp.le (sub_nonneg.mpr hp1)
      hTM hTW (by ring : p + (1 - p) = 1)
    unfold objective
    linarith

/-- The strictly positive optimizer is exactly `M^(1/p)`, including the endpoint `p=1`. -/
theorem maximum_and_attainment {M : Matrix d d ℂ} (hM : M.PosDef)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ W₀ : Matrix d d ℂ, W₀.PosDef ∧ W₀ = M ^ (1 / p) ∧
      objective p M W₀ = p * tracePower (1 / p) M ∧
      ∀ W : Matrix d d ℂ, W.PosDef → objective p M W ≤ objective p M W₀ := by
  have hW₀ : (M ^ (1 / p)).PosDef := (hM.isStrictlyPositive.rpow M (1 / p)).posDef
  have heq : objective p M (M ^ (1 / p)) = p * tracePower (1 / p) M := by
    have hprod : M * ((M ^ (1 / p)) ^ (1 - p)) = M ^ (1 / p) := by
      rw [CFC.rpow_rpow M (1 / p) (1 - p) (by positivity) hM.isStrictlyPositive]
      conv_lhs => lhs; rw [← CFC.rpow_one M hM.posSemidef.nonneg]
      rw [← CFC.rpow_add hM.isUnit]
      congr 1
      field_simp
      ring
    rw [objective, hprod, tracePower]
    ring
  exact ⟨_, hW₀, rfl, heq, fun W hW ↦ heq.symm ▸ forward_trace_young hM hW hp hp1⟩

#print axioms forward_trace_young
#print axioms maximum_and_attainment
end D5.S3.Quantum.Hiai.ForwardTraceYoung

namespace D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix InverseMeanVariational GeneralizedPerspectiveFunction LiebAndoTrace LownerHeinzTheorem
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private lemma map_strict {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A ≃⋆ₐ[ℂ] B) {X : A} (hX : IsStrictlyPositive X) : IsStrictlyPositive (φ X) := by
  obtain ⟨Q, hQ, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hX
  rw [map_mul, map_star]
  exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨φ Q, hQ.map φ, rfl⟩

private lemma map_power {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A ≃⋆ₐ[ℂ] B) {X : A} (hX : IsStrictlyPositive X) (s : ℝ) :
    φ (X ^ s) = (φ X) ^ s := by
  rw [CFC.rpow_def, CFC.rpow_def]
  exact StarAlgHomClass.map_cfc φ (fun x : NNReal ↦ x ^ s) X
    (NNReal.continuousOn_rpow_const (.inl (spectrum.zero_notMem NNReal hX.isUnit)))
    (StarAlgEquiv.isometry φ).continuous hX.nonneg (map_strict φ hX).nonneg

/-- The classical base-first geometric mean, with spectral matrix powers. -/
def geometricMean (θ : ℝ) (B A : Matrix d d ℂ) : Matrix d d ℂ :=
  B ^ (1 / 2 : ℝ) * (B ^ (-1 / 2 : ℝ) * A * B ^ (-1 / 2 : ℝ)) ^ θ * B ^ (1 / 2 : ℝ)

lemma mean_strict {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef) (θ : ℝ) :
    IsStrictlyPositive (geometricMean θ B A) := by
  have hI := hB.isStrictlyPositive.rpow B (-1 / 2)
  have hS := hB.isStrictlyPositive.rpow B (1 / 2)
  have hm := (hI.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint A
    (B ^ (-1 / 2 : ℝ)) hI.isSelfAdjoint).2 hA.isStrictlyPositive
  exact (hS.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint
    ((B ^ (-1 / 2 : ℝ) * A * B ^ (-1 / 2 : ℝ)) ^ θ) (B ^ (1 / 2 : ℝ))
    hS.isSelfAdjoint).2 (hm.rpow _ θ)

private abbrev φ : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)

private lemma φ_pd {A : Matrix d d ℂ} (hA : A.PosDef) : φ A ∈ pdSet := by
  have h := map_strict φ hA.isStrictlyPositive
  exact ⟨h.isSelfAdjoint, fun _ hx ↦ h.spectrum_pos hx⟩

private lemma φ_mean {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef) (θ : ℝ) :
    φ (geometricMean θ B A) = HiaiGeometricMean.mean θ (φ B) (φ A) := by
  have hI := hB.isStrictlyPositive.rpow B (-1 / 2)
  have hm := (hI.isUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint A
    (B ^ (-1 / 2 : ℝ)) hI.isSelfAdjoint).2 hA.isStrictlyPositive
  have hsB := map_strict φ hB.isStrictlyPositive
  have his : CFC.sqrt (Ring.inverse (φ B)) = (φ B) ^ (-1 / 2 : ℝ) := by
    rw [CFC.sqrt_eq_rpow, CFC.inverse_eq_rpow_neg_one hsB,
      CFC.rpow_rpow (φ B) (-1) (1 / 2) (by norm_num) hsB]
    norm_num
  unfold geometricMean HiaiGeometricMean.mean
  simp only [CFC.conjSqrt_apply]
  rw [his, CFC.sqrt_eq_rpow, map_mul, map_mul, map_power φ hm,
    map_power φ hB.isStrictlyPositive, map_mul, map_mul, map_power φ hB.isStrictlyPositive]

private lemma mix_pd {A B : Matrix d d ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((1 - t) • A + t • B).PosDef :=
  (CStarAlgebra.convexOn_ringInverse (A := Matrix d d ℂ)).1 hA.isStrictlyPositive
    hB.isStrictlyPositive (sub_nonneg.mpr ht1) ht0 (by ring) |>.posDef

/-- Gamma retains arbitrary Z and one common mixing coefficient for A, B and W. -/
def gamma (p θ : ℝ) (Z A B W : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z * W ^ (1 - p))).re

private lemma φ_gamma (p θ : ℝ) (Z : Matrix d d ℂ) {A B W : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hW : W.PosDef) :
    HiaiHSMeanTrace.gamma p θ (φ Z) (φ A) (φ B) (φ W) = gamma p θ Z A B W := by
  unfold HiaiHSMeanTrace.gamma gamma
  rw [← map_power φ hA.isStrictlyPositive, ← map_power φ hB.isStrictlyPositive,
    ← φ_mean (hA.isStrictlyPositive.rpow A p).posDef (hB.isStrictlyPositive.rpow B p).posDef,
    ← map_power φ hW.isStrictlyPositive, ← map_star φ Z,
    ← map_mul φ, ← map_mul φ, ← map_mul φ]
  change (LinearMap.trace ℂ (EuclideanSpace ℂ d)
    (Matrix.toEuclideanLin (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z * W ^ (1 - p)))).re = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- Matrix triple concavity, including the empty matrix dimension and arbitrary Z. -/
theorem gamma_triple_concave {p θ t : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (Z : Matrix d d ℂ)
    {A₀ A₁ B₀ B₁ W₀ W₁ : Matrix d d ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    (hW₀ : W₀.PosDef) (hW₁ : W₁.PosDef) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * gamma p θ Z A₀ B₀ W₀ + t * gamma p θ Z A₁ B₁ W₁ ≤
      gamma p θ Z ((1 - t) • A₀ + t • A₁) ((1 - t) • B₀ + t • B₁)
        ((1 - t) • W₀ + t • W₁) := by
  cases isEmpty_or_nonempty d with
  | inl hd =>
    letI := hd
    simp [gamma, Matrix.trace]
  | inr hd =>
    letI := hd
    have h := HiaiHSMeanTrace.hs_gamma_triple_concave hp hθ (φ Z)
      (φ_pd hA₀) (φ_pd hA₁) (φ_pd hB₀) (φ_pd hB₁) (φ_pd hW₀) (φ_pd hW₁) ht0 ht1
    have hm (X Y : Matrix d d ℂ) :
        (1 - t) • φ X + t • φ Y = φ ((1 - t) • X + t • Y) := by
      simp only [map_add, ← Complex.coe_smul, map_smul]
    rw [hm, hm, hm, φ_gamma p θ Z hA₀ hB₀ hW₀, φ_gamma p θ Z hA₁ hB₁ hW₁,
      φ_gamma p θ Z (mix_pd hA₀ hA₁ ht0 ht1) (mix_pd hB₀ hB₁ ht0 ht1)
        (mix_pd hW₀ hW₁ ht0 ht1)] at h
    exact h

/-- The actual outer spectral trace power; the geometric mean base is B^p. -/
def psi (p θ : ℝ) (Z A B : Matrix d d ℂ) : ℝ :=
  tracePower (1 / p) (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z)

private lemma congruence_pd (p θ : ℝ) {A B Z : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hZ : IsUnit Z) :
    (Zᴴ * geometricMean θ (B ^ p) (A ^ p) * Z).PosDef := by
  exact ((mean_strict (hA.isStrictlyPositive.rpow A p).posDef
    (hB.isStrictlyPositive.rpow B p).posDef θ).posDef).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hZ)

/-- Exact Psi joint concavity by mixing the attained endpoint optimizers. -/
theorem psi_jointly_concave {p θ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (Z : Matrix d d ℂ) (hZ : IsUnit Z) :
    JointlyConcaveOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (psi p θ Z) := by
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  let M₀ := Zᴴ * geometricMean θ (B₀ ^ p) (A₀ ^ p) * Z
  let M₁ := Zᴴ * geometricMean θ (B₁ ^ p) (A₁ ^ p) * Z
  obtain ⟨W₀, hW₀, _, heq₀, _⟩ :=
    ForwardTraceYoung.maximum_and_attainment (congruence_pd p θ hA₀ hB₀ hZ) hp hp1
  obtain ⟨W₁, hW₁, _, heq₁, _⟩ :=
    ForwardTraceYoung.maximum_and_attainment (congruence_pd p θ hA₁ hB₁ hZ) hp hp1
  have hAm := mix_pd hA₀ hA₁ ht0 ht1
  have hBm := mix_pd hB₀ hB₁ ht0 ht1
  have hWm := mix_pd hW₀ hW₁ ht0 ht1
  have hh := gamma_triple_concave ⟨hp.le, hp1⟩ hθ Z hA₀ hA₁ hB₀ hB₁ hW₀ hW₁ ht0 ht1
  have hb := ForwardTraceYoung.forward_trace_young (congruence_pd p θ hAm hBm hZ) hWm hp hp1
  have htrace : (Matrix.trace ((1 - t) • W₀ + t • W₁)).re =
      (1 - t) * (Matrix.trace W₀).re + t * (Matrix.trace W₁).re := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hobj : (1 - t) * ForwardTraceYoung.objective p M₀ W₀ +
      t * ForwardTraceYoung.objective p M₁ W₁ ≤
      ForwardTraceYoung.objective p
        (Zᴴ * geometricMean θ (((1 - t) • B₀ + t • B₁) ^ p)
          (((1 - t) • A₀ + t • A₁) ^ p) * Z) ((1 - t) • W₀ + t • W₁) := by
    unfold ForwardTraceYoung.objective
    rw [htrace]
    dsimp [M₀, M₁]
    unfold gamma at hh
    nlinarith [hh]
  have hc := hobj.trans hb
  rw [heq₀, heq₁] at hc
  change (1 - t) * psi p θ Z A₀ B₀ + t * psi p θ Z A₁ B₁ ≤ _
  unfold psi
  nlinarith [hc]

#print axioms psi_jointly_concave
end D5.S3.Quantum.Hiai.PsiMeanTraceConcavity
