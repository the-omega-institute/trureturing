/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unmodified statewise finite BRST charge has ghost number one on every original tensor state. -/

import D5.S3.VertexAlgebra.BcGhostNumber
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber

noncomputable section

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport
open scoped TensorProduct

def J (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id BcGhostNumber.J

theorem product_degree {space : Type*} [AddCommGroup space] [Module ℂ space]
    (number left right : Module.End ℂ space) (leftDegree rightDegree : ℂ)
    (leftGrading : number * left - left * number = leftDegree • left)
    (rightGrading : number * right - right * number = rightDegree • right) :
    number * (left * right) - (left * right) * number =
      (leftDegree + rightDegree) • (left * right) := by
  calc
    _ = (number * left - left * number) * right +
        left * (number * right - right * number) := by noncomm_ring
    _ = (leftDegree • left) * right + left * (rightDegree • right) := by
      rw [leftGrading, rightGrading]
    _ = _ := by simp [smul_mul_assoc, mul_smul_comm, add_smul]

private theorem J_C_commutator (D : LatticeData) (mode : ℤ) :
    J D * C D mode - C D mode * J D = C D mode := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_c_commutator (K := ℂ) mode)
  simp only [map_sub, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
  simpa only [J, C, LinearMap.lTensor_def] using lifted

private theorem J_G_commutator (D : LatticeData) (mode : ℤ) :
    J D * G D mode - G D mode * J D = 0 := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_L_commutator (K := ℂ) mode)
  simp only [map_sub, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
  simpa only [J, G, LinearMap.lTensor_def] using lifted

private theorem J_M_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    J D * M D H mode - M D H mode * J D = 0 := by
  have commute : J D * M D H mode = M D H mode * J D := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [J, M, Module.End.mul_apply]
  exact sub_eq_zero.mpr commute

private theorem J_N_commutator (D : LatticeData) (mode : ℤ) :
    J D * N D mode - N D mode * J D = N D mode := by
  have cGrading : J D * C D (-mode) - C D (-mode) * J D =
      (1 : ℂ) • C D (-mode) := by simpa using J_C_commutator D (-mode)
  have gGrading : J D * G D mode - G D mode * J D =
      (0 : ℂ) • G D mode := by simpa using J_G_commutator D mode
  by_cases branch : -1 ≤ mode
  · simpa only [N, if_pos branch, ← Module.End.mul_eq_comp, add_zero, one_smul]
      using product_degree (J D) (C D (-mode)) (G D mode) 1 0 cGrading gGrading
  · simpa only [N, if_neg branch, ← Module.End.mul_eq_comp, zero_add, one_smul]
      using product_degree (J D) (G D mode) (C D (-mode)) 0 1 gGrading cGrading

private theorem J_A_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) :
    J D * A D H mode - A D H mode * J D = A D H mode := by
  have cGrading : J D * C D (-mode) - C D (-mode) * J D =
      (1 : ℂ) • C D (-mode) := by simpa using J_C_commutator D (-mode)
  have mGrading : J D * M D H mode - M D H mode * J D =
      (0 : ℂ) • M D H mode := by simpa using J_M_commutator D H mode
  have matterGrading : J D * (C D (-mode) * M D H mode) -
      (C D (-mode) * M D H mode) * J D = C D (-mode) * M D H mode := by
    simpa using product_degree (J D) (C D (-mode)) (M D H mode)
      1 0 cGrading mGrading
  simp only [A, ← Module.End.mul_eq_comp]
  calc
    _ = (J D * (C D (-mode) * M D H mode) -
          (C D (-mode) * M D H mode) * J D) +
        (2 : ℂ)⁻¹ • (J D * N D mode - N D mode * J D) := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = _ := by rw [matterGrading, J_N_commutator]

theorem J_Q_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    J D * Q D H - Q D H * J D = Q D H := by
  apply LinearMap.ext
  intro state
  have stateFinite := A_finite D H state
  have numberFinite := A_finite D H (J D state)
  have imageFinite := stateFinite.fun_comp (map_zero (J D))
  have numberSum := (J D).toAddMonoidHom.map_finsum stateFinite
  simp only [LinearMap.toAddMonoidHom_coe] at numberSum
  change J D (∑ᶠ mode : ℤ, A D H mode state) -
      (∑ᶠ mode : ℤ, A D H mode (J D state)) =
    ∑ᶠ mode : ℤ, A D H mode state
  rw [numberSum, ← finsum_sub_distrib imageFinite numberFinite]
  apply finsum_congr
  intro mode
  have grading := congrArg (fun operator : Module.End ℂ (State D) => operator state)
    (J_A_commutator D H mode)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply] using grading

#print axioms J_Q_commutator

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
