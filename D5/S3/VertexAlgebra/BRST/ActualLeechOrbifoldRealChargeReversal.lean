/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealChargeReversal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealChargeReversal
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Plane charge reversal on the real native BRST Lie algebra and its root spaces. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealCartan
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldChargeReversalDescent

/-!
The plane lattice involution commutes with coefficient conjugation on the
literal state carrier and on its relative ghost-one cohomology. Its restriction
to the fixed real Lie algebra preserves the native BPZ form and reverses the
momentum of each real weight space.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeBracket (MomentumH1 nativeValue)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier_theta)
open private matterConjugation matterConjugation_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechBRSTCoefficientRealForm
open private matterChargeReversal_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPlaneChargeReversal
open private nativeValue_injective from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

private theorem matterConjugation_chargeReversal (v : Matter) :
    matterConjugation (matterChargeReversal v) = matterChargeReversal (matterConjugation v) := by
  have h : (matterConjugation.comp matterChargeReversal : Matter →ₗ⋆[ℂ] Matter) =
      matterChargeReversal.comp matterConjugation := by
    apply TensorProduct.ext'
    intro a u
    simp only [LinearMap.comp_apply, matterChargeReversal_tmul, matterConjugation_tmul]
    exact congrArg (fun w => _ ⊗ₜ[ℂ] w) (kappaCarrier_theta u)
  exact LinearMap.congr_fun h v

/-- On the original matter and ghost tensor product, reversal commutes with conjugation. -/
theorem coefficientConjugation_chargeReversal (x : ComplexState) :
    coefficientConjugation (chargeReversal x) = chargeReversal (coefficientConjugation x) := by
  have h : (coefficientConjugation.comp chargeReversal : ComplexState →ₗ⋆[ℂ] ComplexState) =
      chargeReversal.comp coefficientConjugation := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, chargeReversal_tmul, coefficientConjugation_tmul,
      matterConjugation_chargeReversal]
  exact LinearMap.congr_fun h x

local notation "Momentum" => Charge hyperbolicPlane
local notation "Cycles" => fun p : Momentum => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" => fun p : Momentum => GradedBoundaries planeFrame planeBasis p 1
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H

attribute [local instance] chargeReversalShellAddCommGroup chargeReversalCyclesAddCommGroup

set_option maxHeartbeats 1500000 in
/-- The native quotient maps commute across the two opposite momentum sectors. -/
theorem coefficientConjugationCohomology_chargeReversal (p : Momentum) (x : H p) :
    coefficientConjugationCohomology (-p) (chargeReversalCohomology p x) =
      chargeReversalCohomology p (coefficientConjugationCohomology p x) := by
  refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
  simp only [coefficientConjugationCohomology_mk, chargeReversalCohomology_mk]
  apply congrArg (fun z : Cycles (-p) => (Submodule.Quotient.mk z : H (-p)))
  apply nativeValue_injective
  simp only [coefficientConjugationCycles_nativeValue, chargeReversalCycles_nativeValue,
    coefficientConjugation_chargeReversal]

/-- Commutation on the finite-support sum of native momentum cohomology groups. -/
theorem coefficientConjugationMomentum_chargeReversal (x : MomentumH1) :
    coefficientConjugationMomentum (chargeReversalLieEquiv x) =
      chargeReversalLieEquiv (coefficientConjugationMomentum x) := by
  let conj := coefficientConjugationMomentum.toAddMonoidHom
  let rev := chargeReversalLieEquiv.toLinearEquiv.toLinearMap.toAddMonoidHom
  have h : conj.comp rev = rev.comp conj := by
    apply DirectSum.addHom_ext (ι := Momentum) (β := H)
    intro p a
    change coefficientConjugationMomentum (chargeReversalLieEquiv (incl p a)) =
      chargeReversalLieEquiv (coefficientConjugationMomentum (incl p a))
    simp only [coefficientConjugationMomentum_incl, chargeReversalLieEquiv_incl,
      coefficientConjugationCohomology_chargeReversal]
  exact DFunLike.congr_fun h x

namespace RelativeBracket

private def realChargeReversal (x : momentumRealLie) : momentumRealLie :=
  ⟨chargeReversalLieEquiv (momentumRealValue x), by
    change coefficientConjugationMomentum (chargeReversalLieEquiv (momentumRealValue x)) =
      chargeReversalLieEquiv (momentumRealValue x)
    rw [coefficientConjugationMomentum_chargeReversal, momentumConjugation_realValue]⟩

private theorem realChargeReversal_involutive : Function.Involutive realChargeReversal :=
  fun x => Subtype.ext (chargeReversalLieEquiv_involutive (momentumRealValue x))

/-- Plane charge reversal as a real Lie automorphism of native relative BRST cohomology. -/
def realChargeReversalLieEquiv : momentumRealLie ≃ₗ⁅ℝ⁆ momentumRealLie where
  toLieHom :=
    { toFun := realChargeReversal
      map_add' x y := Subtype.ext (map_add chargeReversalLieEquiv _ _)
      map_smul' r x := Subtype.ext (by
        change chargeReversalLieEquiv ((r : ℂ) • momentumRealValue x) =
          (r : ℂ) • chargeReversalLieEquiv (momentumRealValue x)
        exact map_smul chargeReversalLieEquiv _ _)
      map_lie' {x y} := Subtype.ext (chargeReversalLieEquiv.map_lie _ _) }
  invFun := realChargeReversal
  left_inv := realChargeReversal_involutive
  right_inv := realChargeReversal_involutive

@[simp] theorem momentumRealValue_realChargeReversalLieEquiv (x : momentumRealLie) :
    momentumRealValue (realChargeReversalLieEquiv x) =
      chargeReversalLieEquiv (momentumRealValue x) := rfl

theorem realChargeReversalLieEquiv_involutive : Function.Involutive realChargeReversalLieEquiv :=
  realChargeReversal_involutive

/-- The real Lie automorphism preserves the signed native BPZ form. -/
theorem realChargeReversalLieEquiv_bpz (x y : momentumRealLie) :
    momentumRealBPZ (realChargeReversalLieEquiv x) (realChargeReversalLieEquiv y) =
      momentumRealBPZ x y :=
  congrArg Complex.re (chargeReversalLieEquiv_bpz (momentumRealValue x) (momentumRealValue y))

/-- The real automorphism reverses the momentum of every real Cartan weight space. -/
theorem realChargeReversalLieEquiv_mem_weightSpace {p : Momentum} {x : momentumRealLie}
    (hx : x ∈ realMomentumWeightSpace p) :
    realChargeReversalLieEquiv x ∈ realMomentumWeightSpace (-p) := by
  obtain ⟨a, ha, hvalue⟩ := (mem_realMomentumWeightSpace_iff_fixed p x).mp hx
  refine (mem_realMomentumWeightSpace_iff_fixed (-p) _).mpr
    ⟨chargeReversalCohomology p a, ?_, ?_⟩
  · rw [coefficientConjugationCohomology_chargeReversal, ha]
  · rw [momentumRealValue_realChargeReversalLieEquiv, ← hvalue, chargeReversalLieEquiv_incl]

/-- The actual root spaces at opposite momenta are linearly equivalent by plane reversal. -/
def realChargeReversalWeightSpaceEquiv (p : Momentum) :
    realMomentumWeightSpace p ≃ₗ[ℝ] realMomentumWeightSpace (-p) where
  toFun x := ⟨realChargeReversalLieEquiv x, realChargeReversalLieEquiv_mem_weightSpace x.property⟩
  invFun y := ⟨realChargeReversalLieEquiv y, by
    simpa only [neg_neg] using realChargeReversalLieEquiv_mem_weightSpace y.property⟩
  left_inv x := Subtype.ext (realChargeReversalLieEquiv_involutive x)
  right_inv y := Subtype.ext (realChargeReversalLieEquiv_involutive y)
  map_add' x y := Subtype.ext (map_add realChargeReversalLieEquiv _ _)
  map_smul' r x := Subtype.ext (map_smul realChargeReversalLieEquiv _ _)

@[simp] theorem realChargeReversalWeightSpaceEquiv_apply (p : Momentum)
    (x : realMomentumWeightSpace p) :
    (realChargeReversalWeightSpaceEquiv p x : momentumRealLie) = realChargeReversalLieEquiv x := rfl

@[simp] theorem realChargeReversalWeightSpaceEquiv_symm_apply (p : Momentum)
    (y : realMomentumWeightSpace (-p)) :
    ((realChargeReversalWeightSpaceEquiv p).symm y : momentumRealLie) =
      realChargeReversalLieEquiv y := rfl

end RelativeBracket

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
