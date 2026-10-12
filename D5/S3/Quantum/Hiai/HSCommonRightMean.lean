/- GID: D5/S3/Quantum/Hiai/HSCommonRightMean
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/HSCommonRightMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Powers and geometric means of commuting left and right Hilbert-Schmidt actions. -/
module

public import D5.S3.Quantum.Hiai.HSPowerProduct

@[expose] public section
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
