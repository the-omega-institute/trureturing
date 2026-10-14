/- GID: D5/S3/VertexAlgebra/RelativePairing/TensorRelativeForm
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none -/

import D5.S3.VertexAlgebra.RelativePairing.RotatedAntighostAdjoint
import D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostHermitianRelative

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge
  LatticeBcGhostBrstCAction LatticeBcGhostHermitianForm LatticeBcGhostHermitianAdjoint
  LatticeBcGhostHermitianCohomology
open scoped TensorProduct BigOperators

noncomputable section

theorem F_B (D : LatticeData) (mode : ℤ) (left right : State D) :
    F D (B D mode left) right = F D (Pi D left) (B D (-mode) right) := by
  induction left using TensorProduct.induction_on with
  | zero => simp [F]
  | add first second firstProof secondProof =>
    simpa only [map_add, F, LinearMap.add_apply] using
      congrArg₂ (fun first second : ℂ => first + second) firstProof secondProof
  | tmul matter ghost =>
    induction right using TensorProduct.induction_on with
    | zero => simp [F]
    | add first second firstProof secondProof =>
      simpa only [map_add, F, LinearMap.add_apply] using
        congrArg₂ (fun first second : ℂ => first + second) firstProof secondProof
    | tmul otherMatter otherGhost =>
      simp only [B, Pi, TensorProduct.map_tmul, LinearMap.id_apply, F_tmul,
        BcGhostRotatedForm.Hplus_b]

theorem relative_isotropic (D : LatticeData) (left right : State D)
    (leftRelative : B D 0 left = 0) (rightRelative : B D 0 right = 0) :
    F D left right = 0 := by
  have split : B D 0 (C D 0 left) + C D 0 (B D 0 left) = left := by
    have operators : (B D 0).comp (C D 0) + (C D 0).comp (B D 0) = LinearMap.id := by
      apply TensorProduct.ext'
      intro matter ghost
      have law := LinearMap.congr_fun (BcGhostStressCurrent.b_c (K := ℂ) 0 0) ghost
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, B, C, TensorProduct.map_tmul,
        LinearMap.id_apply, ← TensorProduct.tmul_add, Module.End.mul_apply, if_true,
        zero_add, Module.End.one_apply] using congrArg (fun vector => matter ⊗ₜ[ℂ] vector) law
    exact LinearMap.congr_fun operators left
  have reconstruction : B D 0 (C D 0 left) = left := by
    simpa only [leftRelative, map_zero, add_zero] using split
  rw [← reconstruction, F_B]
  simp [rightRelative, F]

theorem Pi_relative (D : LatticeData) (state : State D)
    (relative : B D 0 state = 0) : B D 0 (Pi D state) = 0 := by
  have parity : Pi D (B D 0 state) = -B D 0 (Pi D state) := by
    have operators : (Pi D).comp (B D 0) = -((B D 0).comp (Pi D)) := by
      apply TensorProduct.ext'
      intro matter ghost
      simp [B, Pi, BcGhostBpZForm.Pi_b, TensorProduct.tmul_neg]
    exact LinearMap.congr_fun operators state
  simpa only [relative, map_zero, zero_eq_neg] using parity

theorem V0_relative (D : LatticeData) (state : State D)
    (relative : B D 0 state = 0) : B D 0 (V D 0 state) = 0 := by
  have anticommute (mode : ℤ) (nonzero : mode ≠ 0) (input : State D) :
      B D 0 (C D mode input) = -C D mode (B D 0 input) := by
    have operators : (B D 0).comp (C D mode) + (C D mode).comp (B D 0) = 0 := by
      apply TensorProduct.ext'
      intro matter ghost
      have law := LinearMap.congr_fun (BcGhostStressCurrent.b_c (K := ℂ) 0 mode) ghost
      simp only [LinearMap.add_apply, Module.End.mul_apply, zero_add, if_neg nonzero,
        LinearMap.zero_apply] at law
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, B, C, TensorProduct.map_tmul,
        LinearMap.id_apply, ← TensorProduct.tmul_add, law, TensorProduct.tmul_zero,
        LinearMap.zero_apply]
    have sumZero : B D 0 (C D mode input) + C D mode (B D 0 input) = 0 :=
      LinearMap.congr_fun operators input
    exact eq_neg_of_add_eq_zero_left sumZero
  simp only [V, Int.cast_zero, add_zero]
  apply finsum_induction (fun vector : State D => B D 0 vector = 0)
    (by simp) (by intro first second firstProof secondProof; simp [firstProof, secondProof])
  intro mode
  by_cases zeroMode : mode = 0
  · simp [zeroMode]
  · simp only [map_smul, RingHom.id_apply, Module.End.mul_apply, add_zero,
      anticommute (-mode) (neg_ne_zero.mpr zeroMode), anticommute mode zeroMode,
      relative, map_zero, neg_zero, smul_zero]

theorem left_boundary_obstruction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGram : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (rightGram : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (preimage cycle : State D) (closed : Q D H cycle = 0) :
    F D (Q D H preimage) (C D 0 cycle) =
      (2 : ℂ)⁻¹ * F D (Pi D preimage) (V D 0 cycle) := by
  have law := LinearMap.congr_fun (c_action D H 0) cycle
  have action : Q D H (C D 0 cycle) = -(2 : ℂ)⁻¹ • V D 0 cycle := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, closed, map_zero,
      add_zero, LinearMap.smul_apply] using law
  rw [F_Q D H leftGram rightGram, action]
  simp [F]

theorem right_boundary_obstruction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGram : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (rightGram : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (cycle preimage : State D) (closed : Q D H cycle = 0) :
    F D cycle (C D 0 (Q D H preimage)) =
      -(2 : ℂ)⁻¹ * F D cycle (V D 0 preimage) := by
  have law := LinearMap.congr_fun (c_action D H 0) preimage
  have action : C D 0 (Q D H preimage) =
      -(2 : ℂ)⁻¹ • V D 0 preimage - Q D H (C D 0 preimage) := by
    exact eq_sub_of_add_eq' law
  rw [action]
  change tensorForm D cycle (_ - _) = _
  rw [map_sub]
  have orthogonal := cycle_boundary_orthogonal D H leftGram rightGram
    (⟨cycle, closed⟩ : LatticeBcGhostNeutralCohomology.OriginalCycles D H)
    (C D 0 preimage)
  change F D cycle (Q D H (C D 0 preimage)) = 0 at orthogonal
  simp only [F] at orthogonal
  simp only [map_smul, smul_eq_mul, orthogonal, sub_zero, F]

theorem boundary_pairing_vanishes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGram : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (rightGram : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (preimage cycle : State D) (preimageRelative : B D 0 preimage = 0)
    (cycleRelative : B D 0 cycle = 0) (closed : Q D H cycle = 0) :
    F D (Q D H preimage) (C D 0 cycle) = 0 ∧
      F D cycle (C D 0 (Q D H preimage)) = 0 := by
  constructor
  · rw [left_boundary_obstruction D H leftGram rightGram preimage cycle closed,
      relative_isotropic D _ _ (Pi_relative D preimage preimageRelative)
        (V0_relative D cycle cycleRelative), mul_zero]
  · rw [right_boundary_obstruction D H leftGram rightGram cycle preimage closed,
      relative_isotropic D _ _ cycleRelative (V0_relative D preimage preimageRelative), mul_zero]

#print axioms V0_relative
#print axioms boundary_pairing_vanishes

end

end D5.S3.VertexAlgebra.LatticeBcGhostHermitianRelative
