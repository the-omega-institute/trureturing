/- GID: D5/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostHermitianAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Corrected original BRST summand and genuine finite symmetric charge adjoints.
-/

import D5.S3.VertexAlgebra.LatticeBcGhostHermitianForm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostHermitianAdjoint

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraHermitian
open LatticeBcGhostBrstCharge LatticeBcGhostHermitianForm BcGhostRotatedForm
open scoped BigOperators TensorProduct

noncomputable section

def Pi (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id BcGhostBpZForm.Pi

private theorem F_add_left (D : LatticeData) (first second right : State D) :
    F D (first + second) right = F D first right + F D second right := by simp [F]

private theorem F_add_right (D : LatticeData) (left first second : State D) :
    F D left (first + second) = F D left first + F D left second := by simp [F]

private theorem F_smul_left (D : LatticeData) (scalar : ℂ) (left right : State D) :
    F D (scalar • left) right = star scalar * F D left right := by
  simp [F, LinearMap.map_smulₛₗ]

private theorem F_smul_right (D : LatticeData) (scalar : ℂ) (left right : State D) :
    F D left (scalar • right) = scalar * F D left right := by simp [F]

private theorem Pi_M (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ) (state : State D) :
    Pi D (M D matrixH mode state) = M D matrixH mode (Pi D state) := by
  have commute : (Pi D).comp (M D matrixH mode) = (M D matrixH mode).comp (Pi D) := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [Pi, M]
  exact LinearMap.congr_fun commute state

private theorem M_C (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ) (matterMode ghostMode : ℤ)
    (state : State D) :
    M D matrixH matterMode (C D ghostMode state) =
      C D ghostMode (M D matrixH matterMode state) := by
  have commute : (M D matrixH matterMode).comp (C D ghostMode) =
      (C D ghostMode).comp (M D matrixH matterMode) := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [M, C]
  exact LinearMap.congr_fun commute state

private theorem Pi_G (D : LatticeData) (mode : ℤ) (state : State D) :
    Pi D (G D mode state) = G D mode (Pi D state) := by
  have commute : (Pi D).comp (G D mode) = (G D mode).comp (Pi D) := by
    apply TensorProduct.ext'
    intro matter ghost
    simp [Pi, G, Pi_stress]
  exact LinearMap.congr_fun commute state

theorem F_M (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (mode : ℤ) (left right : State D) :
    F D (M D matrixH mode left) right = F D left (M D matrixH (-mode) right) := by
  induction left using TensorProduct.induction_on with
  | zero => simp [F]
  | add first second firstProof secondProof =>
    simp only [map_add, F_add_left, firstProof, secondProof]
  | tmul matter ghost =>
    induction right using TensorProduct.induction_on with
    | zero => simp [F]
    | add first second firstProof secondProof =>
      simp only [map_add, F_add_right, firstProof, secondProof]
    | tmul otherMatter otherGhost =>
      simp only [M, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul]
      rw [sugawara_adjoint D matrixH hHG hGH]

theorem F_G (D : LatticeData) (mode : ℤ) (left right : State D) :
    F D (G D mode left) right = F D left (G D (-mode) right) := by
  induction left using TensorProduct.induction_on with
  | zero => simp [F]
  | add first second firstProof secondProof =>
    simp only [map_add, F_add_left, firstProof, secondProof]
  | tmul matter ghost =>
    induction right using TensorProduct.induction_on with
    | zero => simp [F]
    | add first second firstProof secondProof =>
      simp only [map_add, F_add_right, firstProof, secondProof]
    | tmul otherMatter otherGhost =>
      simp only [G, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul, Hplus_stress]

theorem F_C (D : LatticeData) (mode : ℤ) (left right : State D) :
    F D (C D mode left) right = -F D (Pi D left) (C D (-mode) right) := by
  induction left using TensorProduct.induction_on with
  | zero => simp [F]
  | add first second firstProof secondProof =>
    simp only [map_add, F_add_left, firstProof, secondProof]
    ring
  | tmul matter ghost =>
    induction right using TensorProduct.induction_on with
    | zero => simp [F]
    | add first second firstProof secondProof =>
      simp only [map_add, F_add_right, firstProof, secondProof]
      ring
    | tmul otherMatter otherGhost =>
      simp only [C, Pi, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul, Hplus_c]
      ring

private theorem G_C_middle (D : LatticeData) (mode : ℤ) (state : State D) :
    G D (-mode) (C D mode state) =
      C D mode (G D (-mode) state) + (mode : ℂ) • C D 0 state := by
  have ghost := BcGhostStressCurrent.L_c_commutator (K := ℂ) (-mode) mode
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D)) ghost
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
  have tensor : G D (-mode) * C D mode - C D mode * G D (-mode) =
      (-2 * ((-mode : ℤ) : ℂ) - (mode : ℂ)) • C D (-mode + mode) := by
    simpa only [G, C, LinearMap.lTensor_def] using lifted
  have evaluated := LinearMap.congr_fun tensor state
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    neg_add_cancel] at evaluated
  have scalar : (-2 * ((-mode : ℤ) : ℂ) - (mode : ℂ)) = (mode : ℂ) := by
    push_cast
    ring
  rw [scalar] at evaluated
  have expanded := sub_eq_iff_eq_add.mp evaluated
  simpa only [add_comm] using expanded

def d0 (mode : ℤ) : ℂ := if -1 ≤ mode ∧ mode ≤ 1 then 1 else 0

private theorem F_N (D : LatticeData) (mode : ℤ) (left right : State D) :
    F D (N D mode left) right = -F D (Pi D left) (N D (-mode) right) -
      (mode : ℂ) * d0 mode * F D (Pi D left) (C D 0 right) := by
  by_cases branch : -1 ≤ mode
  · by_cases opposite : -1 ≤ -mode
    · have middle : -1 ≤ mode ∧ mode ≤ 1 := ⟨branch, by omega⟩
      simp only [N, if_pos branch, if_pos opposite, LinearMap.comp_apply]
      rw [F_C, Pi_G, F_G, neg_neg, G_C_middle, F_add_right, F_smul_right]
      simp only [d0, if_pos middle]
      ring
    · have outside : ¬ (-1 ≤ mode ∧ mode ≤ 1) := by omega
      simp only [N, if_pos branch, if_neg opposite, LinearMap.comp_apply]
      rw [F_C, Pi_G, F_G, neg_neg]
      simp [d0, outside]
  · have opposite : -1 ≤ -mode := by omega
    have outside : ¬ (-1 ≤ mode ∧ mode ≤ 1) := by omega
    simp only [N, if_neg branch, if_pos opposite, LinearMap.comp_apply]
    rw [F_G, F_C, neg_neg]
    simp [d0, outside]

theorem F_A (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (mode : ℤ) (left right : State D) :
    F D (A D matrixH mode left) right = -F D (Pi D left) (A D matrixH (-mode) right) -
      ((mode : ℂ) * d0 mode / 2) * F D (Pi D left) (C D 0 right) := by
  simp only [A, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    F_add_left, F_smul_left, F_add_right, F_smul_right]
  rw [F_C, Pi_M, F_M D matrixH hHG hGH, neg_neg, M_C, F_N]
  norm_num
  ring

end
end D5.S3.VertexAlgebra.LatticeBcGhostHermitianAdjoint
