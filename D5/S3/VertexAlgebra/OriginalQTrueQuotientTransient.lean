import D5.S3.VertexAlgebra.OriginalQFixedEnergyTransferTransient
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQFiniteHplCheck

noncomputable section

variable {Source Target : Type*} [AddCommGroup Source] [Module ℂ Source]
  [AddCommGroup Target] [Module ℂ Target]

def trueBoundaries (operator : Module.End ℂ Source) (square : operator * operator = 0) :
    Submodule ℂ (LinearMap.ker operator) :=
  LinearMap.range (operator.codRestrict (LinearMap.ker operator) (by
    intro state
    change operator (operator state) = 0
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using LinearMap.congr_fun square state))

abbrev trueCohomology (operator : Module.End ℂ Source) (square : operator * operator = 0) :=
  (LinearMap.ker operator) ⧸ trueBoundaries operator square

def trueCycleMap (source : Module.End ℂ Source) (target : Module.End ℂ Target)
    (mapping : Source →ₗ[ℂ] Target) (chain : target.comp mapping = mapping.comp source) :
    LinearMap.ker source →ₗ[ℂ] LinearMap.ker target :=
  mapping.restrict (by
    intro state member
    have cycle : source state = 0 := member
    change target (mapping state) = 0
    simpa only [LinearMap.comp_apply, cycle, map_zero] using LinearMap.congr_fun chain state)

def trueCohomologyMap (source : Module.End ℂ Source) (target : Module.End ℂ Target)
    (sourceSquare : source * source = 0) (targetSquare : target * target = 0)
    (mapping : Source →ₗ[ℂ] Target) (chain : target.comp mapping = mapping.comp source) :
    trueCohomology source sourceSquare →ₗ[ℂ] trueCohomology target targetSquare :=
  (trueBoundaries source sourceSquare).mapQ (trueBoundaries target targetSquare)
    (trueCycleMap source target mapping chain) (by
      intro cycle member
      obtain ⟨state, equality⟩ := member
      refine ⟨mapping state, ?_⟩
      apply Subtype.ext
      change target (mapping state) = mapping cycle.val
      rw [← equality]
      exact LinearMap.congr_fun chain state)

theorem true_quotient_equivalence
    (source : Module.End ℂ Source) (target : Module.End ℂ Target)
    (sourceSquare : source * source = 0) (targetSquare : target * target = 0)
    (inclusion : Target →ₗ[ℂ] Source) (projection : Source →ₗ[ℂ] Target)
    (homotopy : Module.End ℂ Source)
    (inclusionChain : source.comp inclusion = inclusion.comp target)
    (projectionChain : target.comp projection = projection.comp source)
    (retract : projection.comp inclusion = LinearMap.id)
    (homotopyLaw : source * homotopy + homotopy * source = 1 - inclusion.comp projection) :
    Nonempty (trueCohomology target targetSquare ≃ₗ[ℂ] trueCohomology source sourceSquare) := by
  let forward := trueCohomologyMap target source targetSquare sourceSquare inclusion inclusionChain
  let backward := trueCohomologyMap source target sourceSquare targetSquare projection projectionChain
  have backwardForward : backward.comp forward = LinearMap.id := by
    apply LinearMap.ext
    intro quotient
    refine Submodule.Quotient.induction_on _ quotient ?_
    intro cycle
    change Submodule.Quotient.mk
      (trueCycleMap source target projection projectionChain
        (trueCycleMap target source inclusion inclusionChain cycle)) =
      (Submodule.Quotient.mk cycle : trueCohomology target targetSquare)
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun retract cycle.val
  have forwardBackward : forward.comp backward = LinearMap.id := by
    apply LinearMap.ext
    intro quotient
    refine Submodule.Quotient.induction_on _ quotient ?_
    intro cycle
    change Submodule.Quotient.mk
      (trueCycleMap target source inclusion inclusionChain
        (trueCycleMap source target projection projectionChain cycle)) =
      (Submodule.Quotient.mk cycle : trueCohomology source sourceSquare)
    apply (Submodule.Quotient.eq (trueBoundaries source sourceSquare)).mpr
    refine ⟨-homotopy cycle.val, ?_⟩
    apply Subtype.ext
    change source (-homotopy cycle.val) = inclusion (projection cycle.val) - cycle.val
    have cycleLaw : source cycle.val = 0 := cycle.property
    have equality := LinearMap.congr_fun homotopyLaw cycle.val
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.comp_apply, cycleLaw, map_zero, add_zero] at equality
    rw [map_neg, equality]
    abel
  exact ⟨LinearEquiv.ofLinear forward backward forwardBackward backwardForward⟩

end

end D5.S3.VertexAlgebra.OriginalQFiniteHplCheck
