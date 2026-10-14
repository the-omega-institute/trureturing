/- GID: D5/S3/VertexAlgebra/LatticeBcGhostHermitianCohomology
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostHermitianCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite symmetric original-Q adjoint and literal unrestricted quotient pairing.
-/

import D5.S3.VertexAlgebra.LatticeBcGhostHermitianAdjoint
import D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open LatticeBcGhostHermitianForm LatticeBcGhostHermitianAdjoint LatticeBcGhostNeutralCohomology
open scoped BigOperators

noncomputable section

private theorem support_in_symmetric_interval (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ) (state : State D) (radius : ℕ)
    (bound : (A_finite D matrixH state).toFinset.sup Int.natAbs ≤ radius) :
    Function.support (fun mode : ℤ => A D matrixH mode state) ⊆
      (Finset.Icc (-(radius : ℤ)) (radius : ℤ) : Set ℤ) := by
  intro mode member
  have finiteMember : mode ∈ (A_finite D matrixH state).toFinset :=
    (Set.Finite.mem_toFinset (A_finite D matrixH state)).mpr member
  have absolute : mode.natAbs ≤ radius := le_trans (Finset.le_sup finiteMember) bound
  have upper : mode ≤ (mode.natAbs : ℤ) := Int.le_natAbs
  have lower : -mode ≤ (mode.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using
      (Int.le_natAbs : -mode ≤ ((-mode).natAbs : ℤ))
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor <;> omega

private theorem correction_sum (radius : ℕ) (large : 1 ≤ radius) :
    ∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), (mode : ℂ) * d0 mode / 2 = 0 := by
  have subset : Finset.Icc (-1 : ℤ) 1 ⊆ Finset.Icc (-(radius : ℤ)) (radius : ℤ) := by
    intro mode member
    simp only [Finset.mem_Icc] at member ⊢
    constructor <;> omega
  have equality : (∑ mode ∈ Finset.Icc (-1 : ℤ) 1, (mode : ℂ) * d0 mode / 2) =
      ∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), (mode : ℂ) * d0 mode / 2 := by
    apply Finset.sum_subset subset
    intro mode member outside
    have notMiddle : ¬ (-1 ≤ mode ∧ mode ≤ 1) := by simpa using outside
    simp [d0, notMiddle]
  rw [← equality, show Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} by decide]
  norm_num [d0]

theorem F_Q (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (left right : State D) :
    F D (Q D matrixH left) right = -F D (Pi D left) (Q D matrixH right) := by
  classical
  let radius : ℕ := max ((A_finite D matrixH left).toFinset.sup Int.natAbs)
    ((A_finite D matrixH right).toFinset.sup Int.natAbs) + 1
  have boundLeft : (A_finite D matrixH left).toFinset.sup Int.natAbs ≤ radius := by
    dsimp [radius]
    omega
  have boundRight : (A_finite D matrixH right).toFinset.sup Int.natAbs ≤ radius := by
    dsimp [radius]
    omega
  have large : 1 ≤ radius := by dsimp [radius]; omega
  have leftSum : Q D matrixH left =
      ∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), A D matrixH mode left := by
    exact finsum_eq_sum_of_support_subset (fun mode => A D matrixH mode left)
      (support_in_symmetric_interval D matrixH left radius boundLeft)
  have rightSum : Q D matrixH right =
      ∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), A D matrixH mode right := by
    exact finsum_eq_sum_of_support_subset (fun mode => A D matrixH mode right)
      (support_in_symmetric_interval D matrixH right radius boundRight)
  rw [leftSum]
  change tensorForm D (∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
    A D matrixH mode left) right = _
  rw [map_sum, LinearMap.sum_apply]
  change (∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
    F D (A D matrixH mode left) right) = _
  simp_rw [F_A D matrixH hHG hGH]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, correction_sum radius large, zero_mul,
    sub_zero, Finset.sum_neg_distrib]
  congr 1
  rw [rightSum]
  change (∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
    tensorForm D (Pi D left) (A D matrixH (-mode) right)) =
      tensorForm D (Pi D left)
        (∑ mode ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), A D matrixH mode right)
  rw [map_sum]
  apply Finset.sum_bij (fun mode _ => -mode)
  · intro mode member
    simp only [Finset.mem_Icc] at member ⊢
    constructor <;> omega
  · intro first firstMember second secondMember same
    omega
  · intro mode member
    refine ⟨-mode, ?_, by omega⟩
    simp only [Finset.mem_Icc] at member ⊢
    constructor <;> omega
  · intro mode member
    rfl

theorem boundary_cycle_orthogonal (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (ambient : State D) (cycle : OriginalCycles D matrixH) :
    F D (Q D matrixH ambient) cycle.val = 0 := by
  rw [F_Q D matrixH hHG hGH]
  have killed : Q D matrixH cycle.val = 0 := cycle.property
  rw [killed]
  simp [F]

theorem cycle_boundary_orthogonal (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (cycle : OriginalCycles D matrixH) (ambient : State D) :
    F D cycle.val (Q D matrixH ambient) = 0 := by
  rw [F_hermitian, boundary_cycle_orthogonal D matrixH hHG hGH]
  simp

private def cycleForm (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    OriginalCycles D matrixH →ₗ⋆[ℂ] OriginalCycles D matrixH →ₗ[ℂ] ℂ :=
  (tensorForm D).domRestrict₁₂ (OriginalCycles D matrixH) (OriginalCycles D matrixH)

def quotientForm (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (hcritical : D.rank = 26) :
    OriginalCohomology D matrixH →ₗ⋆[ℂ] OriginalCohomology D matrixH →ₗ[ℂ] ℂ :=
  Submodule.liftQ (OriginalBoundaries D matrixH) {
    toFun := fun left => Submodule.liftQ (OriginalBoundaries D matrixH)
      (cycleForm D matrixH left) (by
        intro boundary member
        obtain ⟨ambient, image⟩ := member
        change Q D matrixH ambient = boundary.val at image
        let ambientCycle : OriginalCycles D matrixH :=
          ⟨Q D matrixH ambient,
            original_image_in_cycles D matrixH hHG hGH hcritical ⟨ambient, rfl⟩⟩
        have representativeEquality : ambientCycle = boundary := Subtype.ext image
        change F D left.val boundary.val = 0
        rw [← representativeEquality]
        exact cycle_boundary_orthogonal D matrixH hHG hGH left ambient)
    map_add' := by
      intro first second
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative => simp [cycleForm, F]
    map_smul' := by
      intro scalar left
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative => simp [cycleForm, F, LinearMap.map_smulₛₗ] }
    (by
      intro boundary member
      obtain ⟨ambient, image⟩ := member
      change Q D matrixH ambient = boundary.val at image
      let ambientCycle : OriginalCycles D matrixH :=
        ⟨Q D matrixH ambient,
          original_image_in_cycles D matrixH hHG hGH hcritical ⟨ambient, rfl⟩⟩
      have representativeEquality : ambientCycle = boundary := Subtype.ext image
      apply LinearMap.ext
      intro quotient
      induction quotient using Submodule.Quotient.induction_on with
      | _ representative =>
        change F D boundary.val representative.val = 0
        rw [← representativeEquality]
        exact boundary_cycle_orthogonal D matrixH hHG hGH ambient representative)


end
end D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology
