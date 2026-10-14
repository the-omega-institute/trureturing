/- GID: D5/S3/VertexAlgebra/LatticeBcGhostHermitianForm
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostHermitianForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native unrestricted matter and energy-rotated ghost tensor pairing.
-/

import D5.S3.VertexAlgebra.BcGhostRotatedForm
import D5.S3.VertexAlgebra.LatticeSugawaraHermitian
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge LatticeChargedFockForms
open BcGhostRotatedForm
open scoped TensorProduct BigOperators

noncomputable section

private def productFunctional (D : LatticeData) (matter : Carrier D →ₗ[ℂ] ℂ)
    (ghost : BcGhostFockSupport.Fock ℂ →ₗ[ℂ] ℂ) : State D →ₗ[ℂ] ℂ :=
  TensorProduct.lift {
    toFun := fun state => matter state • ghost
    map_add' := by intro first second; simp [add_smul]
    map_smul' := by intro scalar state; simp [smul_smul] }

def tensorForm (D : LatticeData) : State D →ₗ⋆[ℂ] State D →ₗ[ℂ] ℂ :=
  TensorProduct.lift {
    toFun := fun matter => {
      toFun := fun ghost => productFunctional D (hermitianForm D matter) (HplusForm ghost)
      map_add' := by
        intro first second
        apply TensorProduct.ext'
        intro rightMatter rightGhost
        simp [productFunctional, mul_add]
      map_smul' := by
        intro scalar ghost
        apply TensorProduct.ext'
        intro rightMatter rightGhost
        simp [productFunctional, LinearMap.map_smulₛₗ, mul_assoc, mul_left_comm] }
    map_add' := by
      intro first second
      apply LinearMap.ext
      intro ghost
      apply TensorProduct.ext'
      intro rightMatter rightGhost
      simp [productFunctional, add_mul]
    map_smul' := by
      intro scalar matter
      apply LinearMap.ext
      intro ghost
      apply TensorProduct.ext'
      intro rightMatter rightGhost
      simp [productFunctional, LinearMap.map_smulₛₗ, mul_assoc] }

def F (D : LatticeData) (left right : State D) : ℂ := tensorForm D left right

theorem F_tmul (D : LatticeData) (leftMatter rightMatter : Carrier D)
    (leftGhost rightGhost : BcGhostFockSupport.Fock ℂ) :
    F D (leftMatter ⊗ₜ[ℂ] leftGhost) (rightMatter ⊗ₜ[ℂ] rightGhost) =
      hermitianForm D leftMatter rightMatter * Hplus leftGhost rightGhost := rfl

private theorem matter_hermitian (D : LatticeData) (left right : Carrier D) :
    hermitianForm D left right = star (hermitianForm D right left) := by
  classical
  induction left using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, LinearMap.add_apply, firstProof, secondProof, star_add]
  | single leftCharge leftPolynomial =>
    induction right using Finsupp.induction_linear with
    | zero => simp
    | add first second firstProof secondProof =>
      simp only [map_add, LinearMap.add_apply, firstProof, secondProof, star_add]
    | single rightCharge rightPolynomial =>
      rw [hermitian_single, hermitian_single]
      by_cases same : leftCharge = rightCharge
      · subst rightCharge
        simp only [if_true]
        exact ((LatticeOscillatorFockForm.fockForm_isSymm D).eq rightPolynomial leftPolynomial).symm
      · simp [same, Ne.symm same]

theorem F_hermitian (D : LatticeData) (left right : State D) :
    F D left right = star (F D right left) := by
  induction left using TensorProduct.induction_on with
  | zero => simp [F]
  | add first second firstProof secondProof =>
    change tensorForm D (first + second) right = star (tensorForm D right (first + second))
    simp only [map_add, LinearMap.add_apply, star_add]
    change F D first right + F D second right = star (F D right first) + star (F D right second)
    rw [firstProof, secondProof]
  | tmul matter ghost =>
    induction right using TensorProduct.induction_on with
    | zero => simp [F]
    | add first second firstProof secondProof =>
      change tensorForm D (matter ⊗ₜ[ℂ] ghost) (first + second) =
        star (tensorForm D (first + second) (matter ⊗ₜ[ℂ] ghost))
      simp only [map_add, LinearMap.add_apply, star_add]
      change F D (matter ⊗ₜ[ℂ] ghost) first + F D (matter ⊗ₜ[ℂ] ghost) second =
        star (F D first (matter ⊗ₜ[ℂ] ghost)) + star (F D second (matter ⊗ₜ[ℂ] ghost))
      rw [firstProof, secondProof]
    | tmul otherMatter otherGhost =>
      rw [F_tmul, F_tmul, matter_hermitian D matter otherMatter,
        Hplus_hermitian ghost otherGhost]
      simp [mul_comm]

end
end D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm
