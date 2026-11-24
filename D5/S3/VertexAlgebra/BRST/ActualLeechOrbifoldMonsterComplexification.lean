/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterComplexification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterComplexification
   mirror-E: none(waiver:native-complex-BRST)
   anchors: []
   utility: none
   digest: The complexified rank-two Monster Lie algebra identifies with native complex BRST. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechBRSTComplexification
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterIdentification

/-!
# The rank-two Monster Lie algebra over ℂ

The native real identification extends to the complex relative BRST momentum algebra.
On pure tensors the map evaluates the rank-two presentation on the native real classes
and then multiplies by the complex coefficient.

proof_shape: monsterRankTwoComplexBRSTEquiv, monsterRankTwoComplexBRSTEquiv_tmul: content
admission_basis: escape-witness
escape_witness: The real identification preserves the native bracket on pairs of classes.
The tensor bracket formula extends this identity to arbitrary complex linear combinations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

attribute [local instance] realLieStateAddCommGroup realLieShellAddCommGroup
  realLieCyclesAddCommGroup

local notation "RealMonster" => MonsterRankTwoPresentation.Presented monsterRealOrder

/-- The complex scalar extension of the rank-two presentation evaluated in native BRST. -/
def monsterRankTwoComplexBRSTEquiv : (ℂ ⊗[ℝ] RealMonster) ≃ₗ⁅ℂ⁆ MomentumH1 :=
  let complexify : (ℂ ⊗[ℝ] RealMonster) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] momentumRealLie) :=
    { monsterRankTwoRealBRSTEquiv.toLinearEquiv.baseChange ℝ ℂ _ _ with
      map_lie' := by
        intro t u
        let extend :=
          monsterRankTwoRealBRSTEquiv.toLinearEquiv.baseChange ℝ ℂ RealMonster momentumRealLie
        change extend ⁅t, u⁆ = ⁅extend t, extend u⁆
        induction t using TensorProduct.inductionOn with
        | tmul z x =>
          induction u using TensorProduct.inductionOn with
          | tmul w y =>
            simp only [extend, LieAlgebra.ExtendScalars.bracket_tmul, LinearEquiv.baseChange_tmul,
              LieEquiv.coe_toLinearEquiv, LieEquiv.map_lie]
          | add u v hu hv => simp only [LieRing.lie_add, map_add, hu, hv]
        | add t v ht hv => simp only [LieRing.add_lie, map_add, ht, hv] }
  complexify.trans momentumRealComplexification

/-- The complex identification extends native real evaluation on every pure tensor. -/
@[simp] theorem monsterRankTwoComplexBRSTEquiv_tmul (z : ℂ) (x : RealMonster) :
    monsterRankTwoComplexBRSTEquiv (z ⊗ₜ[ℝ] x) =
      z • momentumRealValue (monsterRankTwoRealBRSTEquiv x) := by
  change momentumRealComplexification (z ⊗ₜ[ℝ] monsterRankTwoRealBRSTEquiv x) = _
  exact momentumRealComplexification_tmul z (monsterRankTwoRealBRSTEquiv x)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
