/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTContravariant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTContravariant
   mirror-E: none(waiver:algebraic-original-orbifold-brst-contravariant)
   anchors: []
   utility: none
   digest: The native charge reversal preserves physical BPZ and defines the contravariant form. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChevalley
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTOppositeMomentumBracket
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalBPZNondegenerate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalBPZSymmetry
import Mathlib.Algebra.Module.Torsion.Field

/-! The literal physical BPZ form and the explicit charge reversal give the
complex bilinear contravariant form with the sign of Borcherds (1992), Theorem 6.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTContravariant

open LatticeGeneratingFieldLocality (Charge)
open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTMomentum (physicalMomentum physicalMomentum_grading)
open OriginalOrbifoldBRSTCartan (h)
open OriginalOrbifoldBRSTChevalley
  (chevalley chevalley_involutive chevalley_mem_physicalMomentum_iff
    chevalley_eq_neg_of_zero_momentum)
open OriginalOrbifoldBRSTOppositeMomentumBracket (H lie_eq_physicalBPZ_smul_H)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ physicalBPZ_eq_zero_of_momentum)
open OriginalOrbifoldBRSTPhysicalBPZSymmetry (physicalBPZ_symmetric)
open OriginalOrbifoldBRSTPhysicalBPZNondegenerate (physicalBPZ_nondegenerate)
open OriginalOrbifoldBRSTPhysicalInvariantBPZ (physicalBPZ_invariant)

open private H_mem_physicalMomentum_zero physicalBPZ_H_h from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTOppositeMomentumBracket

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private theorem H_neg (p : UCharge) : H (-p) = -H p := by
  simp only [H, Pi.neg_apply, Int.cast_neg, neg_smul, Finset.sum_neg_distrib]

private theorem H_ne_zero {p : UCharge} (hp : p ≠ 0) : H p ≠ 0 := by
  intro hzero
  apply hp
  funext i
  change p i = 0
  refine Int.cast_eq_zero.mp (show (p i : ℂ) = 0 from ?_)
  calc
    (p i : ℂ) = physicalBPZ (H p) (h i) := (physicalBPZ_H_h p i).symm
    _ = physicalBPZ 0 (h i) := congrArg (fun z => physicalBPZ z (h i)) hzero
    _ = 0 := by simp only [map_zero, LinearMap.zero_apply]

set_option maxHeartbeats 1600000 in
-- The charge components and bracket use the nested relative cohomology subtype.
private theorem physicalBPZ_chevalley_of_momentum {p q : UCharge} {x y : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hy : y ∈ physicalMomentum q) :
    physicalBPZ (chevalley x) (chevalley y) = physicalBPZ x y := by
  have hθx := (chevalley_mem_physicalMomentum_iff p x).mpr hx
  have hθy := (chevalley_mem_physicalMomentum_iff q y).mpr hy
  by_cases hpq : q = -p
  · subst q
    by_cases hp : p = 0
    · subst p
      rw [neg_zero] at hy
      calc
        physicalBPZ (chevalley x) (chevalley y) = physicalBPZ (-x) (-y) :=
          congrArg₂ (fun u v => physicalBPZ u v)
            (chevalley_eq_neg_of_zero_momentum x hx) (chevalley_eq_neg_of_zero_momentum y hy)
        _ = -physicalBPZ x (-y) :=
          LinearMap.congr_fun (physicalBPZ.map_neg x) (-y)
        _ = physicalBPZ x y := (congrArg Neg.neg ((physicalBPZ x).map_neg y)).trans (neg_neg _)
    · letI : Module.IsTorsionFree ℂ DegreeOne := DivisionSemiring.to_moduleIsTorsionFree
      apply smul_left_injective ℂ (neg_ne_zero.mpr (H_ne_zero hp))
      calc
        physicalBPZ (chevalley x) (chevalley y) • (-H p) =
            physicalBPZ (chevalley x) (chevalley y) • H (-p) :=
          congrArg (fun z => physicalBPZ (chevalley x) (chevalley y) • z) (H_neg p).symm
        _ = ⁅chevalley x, chevalley y⁆ := (lie_eq_physicalBPZ_smul_H hθx hθy).symm
        _ = chevalley ⁅x, y⁆ := (chevalley.map_lie x y).symm
        _ = chevalley (physicalBPZ x y • H p) :=
          congrArg (fun z => chevalley z) (lie_eq_physicalBPZ_smul_H hx hy)
        _ = physicalBPZ x y • chevalley (H p) := map_smul chevalley _ _
        _ = physicalBPZ x y • (-H p) :=
          congrArg (fun z => physicalBPZ x y • z)
            (chevalley_eq_neg_of_zero_momentum _ (H_mem_physicalMomentum_zero p))
  · have hne : -q ≠ -(-p) := fun e => hpq (neg_injective e)
    exact (physicalBPZ_eq_zero_of_momentum hne hθx hθy).trans
      (physicalBPZ_eq_zero_of_momentum hpq hx hy).symm

/-- The charge-reversal Lie automorphism is an isometry of the physical BPZ form. -/
theorem physicalBPZ_chevalley (x y : DegreeOne) :
    physicalBPZ (chevalley x) (chevalley y) = physicalBPZ x y := by
  have eq_of_momentum (f g : DegreeOne →ₗ[ℂ] ℂ)
      (hfg : ∀ (p : UCharge) (z : DegreeOne), z ∈ physicalMomentum p → f z = g z) : f = g := by
    apply LinearMap.eqLocus_eq_top.mp
    apply top_unique
    rw [← physicalMomentum_grading.submodule_iSup_eq_top]
    exact iSup_le fun p z hz => LinearMap.mem_eqLocus.mpr (hfg p z hz)
  let θ := chevalley.toLinearEquiv.toLinearMap
  let twisted := physicalBPZ.compl₁₂ θ θ
  change twisted x y = physicalBPZ x y
  refine LinearMap.congr_fun (eq_of_momentum (twisted x) (physicalBPZ x) ?_) y
  intro q z hz
  exact LinearMap.congr_fun (eq_of_momentum (twisted.flip z) (physicalBPZ.flip z)
    fun p w hw => physicalBPZ_chevalley_of_momentum hw hz) x

/-- The contravariant form on degree one, given by minus BPZ with charge reversal
in its second argument. -/
def contravariantBPZ : LinearMap.BilinForm ℂ DegreeOne :=
  -(physicalBPZ.compl₂ chevalley.toLinearEquiv.toLinearMap)

@[simp]
theorem contravariantBPZ_apply (x y : DegreeOne) :
    contravariantBPZ x y = -physicalBPZ x (chevalley y) := rfl

theorem contravariantBPZ_symmetric : contravariantBPZ.IsSymm := by
  constructor
  intro x y
  change -physicalBPZ x (chevalley y) = -physicalBPZ y (chevalley x)
  apply congrArg Neg.neg
  calc
    physicalBPZ x (chevalley y) = physicalBPZ (chevalley x) (chevalley (chevalley y)) :=
      (physicalBPZ_chevalley x (chevalley y)).symm
    _ = physicalBPZ (chevalley x) y := congrArg (physicalBPZ (chevalley x)) (chevalley_involutive y)
    _ = physicalBPZ y (chevalley x) := physicalBPZ_symmetric.eq _ _

theorem contravariantBPZ_nondegenerate : contravariantBPZ.Nondegenerate := by
  constructor
  · intro x hx
    refine physicalBPZ_nondegenerate.1 x fun y => ?_
    have hy := neg_eq_zero.mp (contravariantBPZ_apply x (chevalley y) ▸ hx (chevalley y))
    exact (congrArg (physicalBPZ x) (chevalley_involutive y)).symm.trans hy
  · intro y hy
    have hθ : chevalley y = 0 :=
      physicalBPZ_nondegenerate.2 _ fun x => by
        simpa only [contravariantBPZ_apply, neg_eq_zero] using hy x
    exact chevalley.injective (hθ.trans chevalley.map_zero.symm)

/-- Distinct physical momenta are orthogonal for the contravariant form. -/
theorem contravariantBPZ_eq_zero_of_momentum_ne {p q : UCharge} {x y : DegreeOne}
    (hpq : q ≠ p) (hx : x ∈ physicalMomentum p) (hy : y ∈ physicalMomentum q) :
    contravariantBPZ x y = 0 := by
  have hθy := (chevalley_mem_physicalMomentum_iff q y).mpr hy
  rw [contravariantBPZ_apply,
    physicalBPZ_eq_zero_of_momentum (fun e => hpq (neg_injective e)) hx hθy, neg_zero]

/-- The adjoint of the native adjoint action of `a` is the adjoint action of
`-chevalley a` for the contravariant form. -/
theorem contravariantBPZ_lie_adjoint (a x y : DegreeOne) :
    contravariantBPZ ⁅a, x⁆ y = -contravariantBPZ x ⁅chevalley a, y⁆ := by
  have hθ : chevalley ⁅chevalley a, y⁆ = ⁅a, chevalley y⁆ :=
    (chevalley.map_lie (chevalley a) y).trans
      (congrArg (fun z : DegreeOne => ⁅z, chevalley y⁆) (chevalley_involutive a))
  change -physicalBPZ ⁅a, x⁆ (chevalley y) = -(-physicalBPZ x (chevalley ⁅chevalley a, y⁆))
  apply congrArg Neg.neg
  calc
    physicalBPZ ⁅a, x⁆ (chevalley y) = physicalBPZ (-⁅x, a⁆) (chevalley y) :=
      congrArg (fun z => physicalBPZ z (chevalley y)) (lie_skew a x).symm
    _ = -physicalBPZ ⁅x, a⁆ (chevalley y) :=
      LinearMap.congr_fun (physicalBPZ.map_neg ⁅x, a⁆) (chevalley y)
    _ = -physicalBPZ x ⁅a, chevalley y⁆ :=
      congrArg Neg.neg (physicalBPZ_invariant x a (chevalley y))
    _ = -physicalBPZ x (chevalley ⁅chevalley a, y⁆) :=
      congrArg (fun z => -physicalBPZ x z) hθ.symm

#print axioms physicalBPZ_chevalley
#print axioms contravariantBPZ
#print axioms contravariantBPZ_apply
#print axioms contravariantBPZ_symmetric
#print axioms contravariantBPZ_nondegenerate
#print axioms contravariantBPZ_eq_zero_of_momentum_ne
#print axioms contravariantBPZ_lie_adjoint

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTContravariant
