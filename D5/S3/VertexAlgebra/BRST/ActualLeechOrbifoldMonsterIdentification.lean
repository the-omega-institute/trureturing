/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterIdentification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterIdentification
   mirror-E: none(waiver:native-real-BRST)
   anchors: []
   utility: none
   digest: The explicit rank-two Monster Lie algebra is the actual fixed real relative BRST Lie algebra. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterNegativeEmbedding
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterPositiveSurjectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Classical

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle (Weight)
open MonsterRankTwoPresentation (CartanCoordinates cartan cartanWeight cartanWeight_apply)

local notation "M" => MonsterRankTwoPresentation.Presented monsterRealOrder

/-- The actual native evaluation identifies the rank-two Monster quotient with
the fixed real relative BRST Lie algebra of the Leech orbifold. -/
def monsterRankTwoRealBRSTEquiv : M ≃ₗ⁅ℝ⁆ momentumRealLie :=
  LieEquiv.ofBijective monsterRankTwoToRealBRST
    ⟨monsterRankTwoToRealBRST_injective,
      monsterRankTwoToRealBRST_surjective_of_positive monsterPositiveToRealBRSTGrade_surjective⟩

@[simp] theorem monsterRankTwoRealBRSTEquiv_apply (z : M) :
    monsterRankTwoRealBRSTEquiv z = monsterRankTwoToRealBRST z := rfl

/-- Under the identification, the paper Cartan eigenspace of weight `(m,n)`
is precisely the BRST momentum space of weight `(m,-n)`. -/
theorem monsterRankTwoRealBRSTEquiv_mem_grade_iff (p : Weight) (z : M) :
    monsterRankTwoRealBRSTEquiv z ∈ realMomentumWeightSpace (monsterNativeMomentum p) ↔
      ∀ h : CartanCoordinates, ⁅cartan monsterRealOrder h, z⁆ = cartanWeight p h • z := by
  rw [monsterRankTwoRealBRSTEquiv_apply]
  refine ⟨?_, monsterRankTwoToRealBRST_mem_weightSpace p z⟩
  intro hz h
  change monsterRankTwoToRealBRST z ∈
    LieModule.weightSpace momentumRealLie (realMomentumWeight (monsterNativeMomentum p)) at hz
  rw [LieModule.mem_weightSpace] at hz
  let k : CartanCoordinates := ![h 0, -h 1]
  have hweight : realMomentumWeight (monsterNativeMomentum p) (realCartanEquiv k) =
      cartanWeight p h := by
    rw [realMomentumWeight_coordinates, cartanWeight_apply]
    simp [k, monsterNativeMomentum]
    ring
  apply monsterRankTwoToRealBRST_injective
  rw [LieHom.map_lie, map_smul, monsterRankTwoToRealBRST_cartan, monsterCartanToRealBRST_apply,
    ← hweight]
  exact hz (realCartanEquiv k)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
