/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterPositiveEmbedding
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMonsterPositiveEmbedding
   mirror-E: none(waiver:native-real-BRST)
   anchors: []
   utility: none
   digest: The actual positive Monster Serre homomorphism embeds into the real relative BRST Lie algebra. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterRealPresentation
import D5.S3.VertexAlgebra.BRST.MonsterPositivePresentationInjectivity

/-!
The positive Serre map factors through the direct sum of native momentum spaces
whose first coordinate is positive. The factor sends paper degree `(m, n)` to
native momentum `(m, -n)`. The degree-one injectivity of the actual generators
then extends to the entire positive presentation by the split tensor identity.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open MonsterPositiveCocycle MonsterPositiveStringPresentation
open MonsterPositivePresentationInjectivity

local notation "P" => PositivePresentation monsterRealOrder
local notation "G" => presentationGrade monsterRealOrder
local notation "N" => RealPositiveMomentumSum

/-- Restrict the actual positive Serre map to a presentation grade and its native momentum. -/
def monsterPositiveToRealBRSTGrade (p : Weight) :
    G p →ₗ[ℝ] realMomentumGrade (monsterNativeMomentum p) :=
  (monsterPositiveToRealBRST.toLinearMap.comp (G p).subtype).codRestrict _
    (fun x => monsterPositiveToRealBRST_mem_grade x.property)

private def positiveFactorLinear : P →ₗ[ℝ] N :=
  (DirectSum.toModule ℝ Weight N fun p =>
    if hp : 0 < p.1 then
      (realPositiveMomentumLof (nativePositiveMomentum p hp)).comp (monsterPositiveToRealBRSTGrade p)
    else 0).comp (DirectSum.decomposeLinearEquiv G).toLinearMap

private theorem positiveFactorLinear_apply_grade (p : Weight) (hp : 0 < p.1) (x : G p) :
    positiveFactorLinear (x : P) =
      realPositiveMomentumLof (nativePositiveMomentum p hp) (monsterPositiveToRealBRSTGrade p x) := by
  simp only [positiveFactorLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof, dite_eq_left hp]
  rfl

private theorem incl_positiveFactorLinear (x : P) :
    realPositiveMomentumIncl (positiveFactorLinear x) = monsterPositiveToRealBRST x := by
  suffices realPositiveMomentumIncl.comp positiveFactorLinear = monsterPositiveToRealBRST.toLinearMap by
    exact LinearMap.congr_fun this x
  apply DirectSum.decompose_lhom_ext G
  intro p
  apply LinearMap.ext
  intro y
  change realPositiveMomentumIncl (positiveFactorLinear (y : P)) = monsterPositiveToRealBRST y
  by_cases hp : 0 < p.1
  · calc
      _ = realPositiveMomentumIncl
          (realPositiveMomentumLof (nativePositiveMomentum p hp) (monsterPositiveToRealBRSTGrade p y)) :=
        congrArg realPositiveMomentumIncl (positiveFactorLinear_apply_grade p hp y)
      _ = (monsterPositiveToRealBRSTGrade p y : momentumRealLie) :=
        realPositiveMomentumIncl_lof (nativePositiveMomentum p hp) (monsterPositiveToRealBRSTGrade p y)
      _ = _ := rfl
  · have hbot : G p = ⊥ := presentationGrade_eq_bot_of_outside monsterRealOrder p
      (fun h => hp (h.symm ▸ (show 0 < realRoot.1 by decide))) (fun h => hp h.1)
    have hy : (y : P) = 0 := (Submodule.mem_bot ℝ).mp (hbot.le y.property)
    rw [hy]
    exact ((realPositiveMomentumIncl.comp positiveFactorLinear).map_zero).trans
      monsterPositiveToRealBRST.map_zero.symm

private def positiveFactor : P →ₗ⁅ℝ⁆ N where
  toLinearMap := positiveFactorLinear
  map_lie' := by
    intro x y
    apply realPositiveMomentumIncl_injective
    change realPositiveMomentumIncl (positiveFactorLinear ⁅x, y⁆) =
      realPositiveMomentumIncl ⁅positiveFactorLinear x, positiveFactorLinear y⁆
    simp only [realPositiveMomentumIncl_lie, incl_positiveFactorLinear, LieHom.map_lie]

/-- The actual positive Serre generator map into real relative BRST is injective. -/
theorem monsterPositiveToRealBRST_injective : Function.Injective monsterPositiveToRealBRST := by
  have hgrade : PreservesGrades positiveFactor :=
    fun p hp x => ⟨monsterPositiveToRealBRSTGrade p x, positiveFactorLinear_apply_grade p hp x⟩
  have hfirst : ∀ (p : Weight), p.1 = 1 →
      Function.Injective (fun x : G p => positiveFactor x) := by
    rintro ⟨m, n⟩ hm
    change m = 1 at hm
    subst m
    intro x y hxy
    apply Subtype.ext
    apply monsterPositiveToRealBRST_injOn_first n x.property y.property
    exact (incl_positiveFactorLinear (x : P)).symm.trans
      ((congrArg realPositiveMomentumIncl hxy).trans (incl_positiveFactorLinear (y : P)))
  intro x y hxy
  apply positivePresentation_to_native_injective positiveFactor hgrade hfirst
  exact realPositiveMomentumIncl_injective
    ((incl_positiveFactorLinear x).trans (hxy.trans (incl_positiveFactorLinear y).symm))

/-- The actual map embeds each presentation grade linearly in the corresponding native grade. -/
theorem monsterPositiveToRealBRSTGrade_injective (p : Weight) :
    Function.Injective (monsterPositiveToRealBRSTGrade p) := by
  intro x y hxy
  exact Subtype.ext (monsterPositiveToRealBRST_injective (congrArg Subtype.val hxy))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
