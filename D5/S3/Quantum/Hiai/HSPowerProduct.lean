/- GID: D5/S3/Quantum/Hiai/HSPowerProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/HSPowerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recovering Hilbert-Schmidt operator identities from the public arbitrary-vector Lieb bridge. -/
module

public import D5.S3.Quantum.Hiai.GeometricMeanOrder

@[expose] public section
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
