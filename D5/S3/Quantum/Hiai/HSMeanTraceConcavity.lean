/- GID: D5/S3/Quantum/Hiai/HSMeanTraceConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/HSMeanTraceConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triple joint concavity of the geometric-mean trace pairing on the true HS space. -/
module

public import D5.S3.Quantum.Hiai.HSCommonRightMean

@[expose] public section
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
theorem gamma_triple_concave {p θ t : ℝ}
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

#print axioms gamma_triple_concave
end HiaiHSMeanTrace
