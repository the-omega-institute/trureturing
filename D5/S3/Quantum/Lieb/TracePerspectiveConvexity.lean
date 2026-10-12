/- GID: D5/S3/Quantum/Lieb/TracePerspectiveConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/TracePerspectiveConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint trace perspective convexity from the all-Hilbert power supplier. -/

import D5.S3.Quantum.Lieb.PowerConvexity
import D5.S3.Quantum.Lieb.LiebConcavity

noncomputable section
namespace D5.S3.Quantum.Lieb.TracePerspectiveConvexity
universe u
open LownerHeinzTheorem GeneralizedPerspectiveFunction HilbertSchmidtOperatorSpace
open OperatorGeometricMean LiebAndoTrace
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

/-- Classical Ando trace perspective convexity; K is arbitrary and its adjoint is retained. -/
theorem trace_perspective_jointly_convex {a : ℝ} (ha : a ∈ Set.Icc 1 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) a K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft : (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
      leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright : (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
      rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA := pdSet_convexCombo hA₁ hA₂ hθ0 hθ1
  have hB := pdSet_convexCombo hB₁ hB₂ hθ0 hθ1
  let : Nontrivial (HSOp ℋ) := by delta HSOp; infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hidconc : OperatorConcaveOn (ℋ := HSOp ℋ) (Set.Ioi (0 : ℝ))
      (fun x : ℝ => x ^ (1 : ℝ)) := by
    intro X Y t hX hY ht0 ht1 hXs hYs
    exact power_Icc_zero_one_operatorConcaveOn_Ici 1 ⟨by norm_num, by norm_num⟩
      hX hY ht0 ht1
      (fun x hx => Set.mem_Ici.mpr (Set.mem_Ioi.mp (hXs hx)).le)
      (fun x hx => Set.mem_Ici.mpr (Set.mem_Ioi.mp (hYs hx)).le)
  have hpers := theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
    (ℋ := HSOp ℋ) (PowerConvexity.condIciAll_rpow ha) hidconc
    (by simp only [Real.rpow_one]; fun_prop)
    (by intro x hx; simpa only [Real.rpow_one] using Set.mem_Ioi.mp hx)
    (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
    (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
    (θ := θ)
    ⟨(leftMulHS_pdSet hA₁).1, fun x hx =>
      Set.mem_Ici.mpr (Set.mem_Ioi.mp ((leftMulHS_pdSet hA₁).2 hx)).le⟩
    ⟨(leftMulHS_pdSet hA₂).1, fun x hx =>
      Set.mem_Ici.mpr (Set.mem_Ioi.mp ((leftMulHS_pdSet hA₂).2 hx)).le⟩
    (rightMulHS_pdSet hB₁) (rightMulHS_pdSet hB₂) hθ0 hθ1
  change operatorPowerMean (ℋ := HSOp ℋ) a 1
      ((1 - θ) • leftMulHS A₁ + θ • leftMulHS A₂)
      ((1 - θ) • rightMulHS B₁ + θ • rightMulHS B₂) ≤
    (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) a 1 (leftMulHS A₁) (rightMulHS B₁) +
      θ • operatorPowerMean (ℋ := HSOp ℋ) a 1 (leftMulHS A₂) (rightMulHS B₂) at hpers
  rw [hleft, hright] at hpers
  have hphi := phiK_mono K hpers
  rw [phiK_add, phiK_smul, phiK_smul,
    phiK_operatorPowerMean_eq_liebTraceMap K _ _ hA hB,
    phiK_operatorPowerMean_eq_liebTraceMap K _ _ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap K _ _ hA₂ hB₂] at hphi
  simpa only [smul_eq_mul] using hphi

#print axioms trace_perspective_jointly_convex
end D5.S3.Quantum.Lieb.TracePerspectiveConvexity
