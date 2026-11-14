/- GID: D5/S3/QuadraticForms/RadicalQuotientIsometry
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RadicalQuotientIsometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Quotient.Bilinear]
   utility: none
   digest: Every actual reflexive bilinear isometry descends to the full nondegenerate radical quotient. -/

import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! The entire original vector spaces and full radicals are used. The
quotient is not replaced by its dimension or a Gram-matrix scalar. This
bridge transports the restricted-form isometries in the received
Nikandish/Ma/Zhang profile obstruction to the actual radical quotients. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.QuadraticForms.RadicalQuotientIsometry

variable {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N]

/-- The entire original radical quotient with its induced bilinear form. -/
def reduced (B : LinearMap.BilinForm 𝕜 M) (hB : B.IsRefl) :
    LinearMap.BilinForm 𝕜 (M ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB le_rfl

/-- An actual bilinear isometry carries the full radical onto the full radical. -/
theorem radical_map {B : LinearMap.BilinForm 𝕜 M} {C : LinearMap.BilinForm 𝕜 N}
    (e : B.IsometryEquiv C) : B.ker.map e.toLinearEquiv.toLinearMap = C.ker := by
  ext n
  constructor
  · rintro ⟨m,hm,rfl⟩
    rw [LinearMap.mem_ker]
    ext y
    obtain ⟨x,rfl⟩ := e.toLinearEquiv.surjective y
    change C (e m) (e x) = 0
    exact (e.map_app' m x).trans (congrArg (fun l : M →ₗ[𝕜] 𝕜 => l x) hm)
  · intro hn
    refine ⟨e.toLinearEquiv.symm n,?_,e.toLinearEquiv.apply_symm_apply n⟩
    change B (e.toLinearEquiv.symm n) = 0
    ext x
    have hh := congrArg (fun l : N →ₗ[𝕜] 𝕜 => l (e x)) hn
    change C n (e x) = 0 at hh
    have hm := e.map_app' (e.toLinearEquiv.symm n) x
    change C (e.toLinearEquiv (e.toLinearEquiv.symm n)) (e.toLinearEquiv x) =
      B (e.toLinearEquiv.symm n) x at hm
    rw [LinearEquiv.apply_symm_apply] at hm
    exact hm.symm.trans hh

/-- The induced form on the full radical quotient is nondegenerate. -/
theorem reduced_nondegenerate (B : LinearMap.BilinForm 𝕜 M) (hB : B.IsRefl) :
    (reduced B hB).Nondegenerate := by
  have hr : (reduced B hB).IsRefl := by
    intro q r h
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      induction r using Submodule.Quotient.induction_on with
      | _ y => exact hB x y h
  refine hr.nondegenerate_iff_separatingLeft.mpr ?_
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    apply (Submodule.Quotient.mk_eq_zero B.ker).mpr
    change B x = 0
    ext y
    exact hq (Submodule.Quotient.mk y)

/-- Every actual isometry descends to the entire actual radical quotients. -/
def result {B : LinearMap.BilinForm 𝕜 M} {C : LinearMap.BilinForm 𝕜 N}
    (hB : B.IsRefl) (hC : C.IsRefl) (e : B.IsometryEquiv C) :
    (reduced B hB).IsometryEquiv (reduced C hC) where
  __ := Submodule.Quotient.equiv B.ker C.ker e.toLinearEquiv (radical_map e)
  map_app' q r := by
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      induction r using Submodule.Quotient.induction_on with
      | _ y =>
        change C (e x) (e y) = B x y
        exact e.map_app' x y

#print axioms result
#print axioms reduced_nondegenerate
end D5.S3.QuadraticForms.RadicalQuotientIsometry
