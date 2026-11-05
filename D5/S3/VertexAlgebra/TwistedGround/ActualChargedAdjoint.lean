/- GID: D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.TensorProduct]
   utility: none
   digest: The actual tensor charged coefficient is signed adjoint at the exact reflected exponent, with a nonzero two-twisted-input dual consumer. -/

import D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
import D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
The tensor form uses the existing selected ActualGround D hu and a chosen
GroundPairing furnished by actual_ground_pairing. No symmetry of that form
is asserted or assumed. Two different ground dual bases isolate the two
slots. The native charged leading term is consumed, never postulated.
The original charge a, signed norm and exponent e are retained. This does
not establish corrected all-state adjointness, restricted-dual closure,
an intertwining field, mixed Jacobi, fusion, string theory or AdS/CFT.
Classical bilinear lattice Fock construction; no literature novelty claim.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct
namespace D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeTwistedGroundRealization TwistedGround.InvariantPairing SignedOscillatorWick



/-- Select from the existing theorem on the pre-existing chosen ground. -/
private def selectedGroundPairing (D : LatticeData) (hu : IsUnit D.G.det) :
    GroundPairing D hu := Classical.choice (actual_ground_pairing D hu)

def actualForm (D : LatticeData) (hu : IsUnit D.G.det) :
    LinearMap.BilinForm ℂ (ActualTensor D hu) :=
  (wick D).tmul (selectedGroundPairing D hu).form

private theorem actualForm_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (p q : Oscillator D) (u v : ActualGround D hu) :
    actualForm D hu (p ⊗ₜ[ℂ] u) (q ⊗ₜ[ℂ] v) =
      (selectedGroundPairing D hu).form u v * wick D p q := by
  rfl

/-- Original all-lattice actual tensor coefficient statement, not a model surrogate. -/
theorem actual_charged_coefficient_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu (chargedCoefficient D hu a e x) y =
      paritySign (bilinear D a a / 2) *
        actualForm D hu x (chargedCoefficient D hu a (-e-2*chargeNorm D a) y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, mul_add, hx, hz]
  | tmul p u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, mul_add, hy, hz]
    | tmul q v =>
      simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
        map_smul, LinearMap.smul_apply, actualForm_tmul, smul_eq_mul]
      rw [(selectedGroundPairing D hu).signed_adjoint, oscillator_coefficient_adjoint]
      ring

/-- Finite ground-coordinate isolation; no use of a symmetric right-dual lemma. -/
theorem actualForm_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det) :
    (actualForm D hu).Nondegenerate := by
  classical
  let G := (selectedGroundPairing D hu).form
  have hG : G.Nondegenerate := (selectedGroundPairing D hu).nondegenerate
  let b := Pi.basisFun ℂ (Half (groundRank D hu))
  let bL := G.dualBasis hG b
  let bR := G.flip.dualBasis hG.flip b
  let E := TensorProduct.equivFinsuppOfBasisRight (M := Oscillator D) b
  have coordinateL (u : ActualGround D hu) (j : Half (groundRank D hu)) :
      G (bL j) u = b.repr u j := by
    change G ((G.toDual hG).symm (b.dualBasis j)) u = _
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
    simp only [Module.Basis.coe_dualBasis, Module.Basis.coord_apply]
  have coordinateR (u : ActualGround D hu) (j : Half (groundRank D hu)) :
      G u (bR j) = b.repr u j := by
    change G.flip ((G.flip.toDual hG.flip).symm (b.dualBasis j)) u = _
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
    simp only [Module.Basis.coe_dualBasis, Module.Basis.coord_apply]
  have isolateL (x : ActualTensor D hu) (q : Oscillator D)
      (j : Half (groundRank D hu)) :
      actualForm D hu x (q ⊗ₜ[ℂ] bR j) = wick D (E x j) q := by
    induction x using TensorProduct.inductionOn with
    | tmul p u =>
      rw [actualForm_tmul]
      change G u (bR j) * wick D p q = _
      rw [coordinateR]
      simp only [E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul, LinearMap.smul_apply, smul_eq_mul]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, Finsupp.add_apply]
  have isolateR (x : ActualTensor D hu) (q : Oscillator D)
      (j : Half (groundRank D hu)) :
      actualForm D hu (q ⊗ₜ[ℂ] bL j) x = wick D q (E x j) := by
    induction x using TensorProduct.inductionOn with
    | tmul p u =>
      rw [actualForm_tmul]
      change G (bL j) u * wick D q p = _
      rw [coordinateL]
      simp only [E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul, LinearMap.smul_apply, smul_eq_mul]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, Finsupp.add_apply]
  constructor
  · intro x hx
    have zero_coordinates : E x = 0 := by
      apply Finsupp.ext
      intro j
      change E x j = 0
      apply (wick_nondegenerate D hu).1
      intro q
      rw [← isolateL]
      exact hx _
    exact E.injective (by simpa using zero_coordinates)
  · intro x hx
    have zero_coordinates : E x = 0 := by
      apply Finsupp.ext
      intro j
      change E x j = 0
      apply (wick_nondegenerate D hu).2
      intro q
      rw [← isolateR]
      exact hx _
    exact E.injective (by simpa using zero_coordinates)

/-- Actual two-twisted-input coefficient on the charged generating subspace.
The codomain is a full dual, not a claimed untwisted state or intertwiner. -/
def chargedDualCoefficient (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (x y : ActualTensor D hu) : Module.Dual ℂ (Charge D →₀ ℂ) :=
  Finsupp.linearCombination ℂ
    (fun a => actualForm D hu (chargedCoefficient D hu a e x) y)

/-- This consumes the constructed tensor form and existing actual leading term.
The nonzero statement is at the actual charged coordinate, for EVERY charge. -/
theorem chargedDualCoefficient_nonzero_second_ground (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (u : ActualGround D hu) (hu0 : u ≠ 0) :
    ∃ x : ActualTensor D hu,
      chargedDualCoefficient D hu (-chargeNorm D a) x ((1 : Oscillator D) ⊗ₜ[ℂ] u)
        (Finsupp.single a 1) ≠ 0 := by
  classical
  have nonzero := charged_ground_leading D hu a u hu0
  have detects : ∃ x : ActualTensor D hu,
      actualForm D hu x
        (chargedCoefficient D hu a (-chargeNorm D a) ((1 : Oscillator D) ⊗ₜ[ℂ] u)) ≠ 0 := by
    by_contra absent
    push Not at absent
    exact nonzero ((actualForm_nondegenerate D hu).2 _ absent)
  obtain ⟨x, hx⟩ := detects
  refine ⟨x, ?_⟩
  simp only [chargedDualCoefficient, Finsupp.linearCombination_single, one_smul]
  rw [actual_charged_coefficient_adjoint,
    show -(-chargeNorm D a)-2*chargeNorm D a = -chargeNorm D a by omega]
  exact mul_ne_zero (by unfold paritySign; split_ifs <;> norm_num) hx

#print axioms actual_charged_coefficient_adjoint
#print axioms actualForm_nondegenerate
#print axioms chargedDualCoefficient_nonzero_second_ground

end D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
