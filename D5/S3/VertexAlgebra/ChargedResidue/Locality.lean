/- GID: D5/S3/VertexAlgebra/ChargedResidue/Locality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/Locality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent complete charged residue tails at every padded locality cutoff. -/

/- proof_shape: chargedPhysicalResidueRow_tail: content
   admission_basis: escape-witness
   escape_witness: The four reflected charged commutators have the same exact
   locality order. Their projected linear combination is annihilated before
   extracting the complete residue; padding is by powers of the actual
   difference operator, including order zero.
   literature_status: classical locality and residue calculus; no novelty claim. -/

import D5.S3.VertexAlgebra.ChargedResidue.LatticeHalfFockChargedResidue
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

/-! The complete residue tail is obtained independently of the collision transform. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockFockNormalField
open LatticeHalfFockGroundRightCurrentTransport LatticeHalfFockPhysicalRescaling
open FieldNormalProductLocality
open scoped BigOperators VertexOperator

noncomputable section

private theorem projected_slice (D : LatticeData) (hu : IsUnit D.G.det)
    (alpha : Charge D) (epsilon : Bool) (gamma : ℤ) :
    physicalSlice D hu (correctedField D hu (projectedGround D alpha epsilon)) gamma =
      (2 : ℂ)⁻¹ • physicalSlice D hu (chargedField D hu alpha) gamma +
        ((2 : ℂ)⁻¹ * projectedSign epsilon) •
          physicalSlice D hu (chargedField D hu (-alpha)) gamma := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] using
    projectedGround_slice_mode_expansion D hu alpha epsilon gamma (-e-1) x

private theorem projected_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta : ℤ)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K) :
    (deltaEnd ^ K) (commutator
      (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
      (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)) = 0 := by
  let A (u : Bool) := physicalSlice D hu (chargedField D hu (reflectedCharge sigma u)) gamma
  let B (v : Bool) := physicalSlice D hu (chargedField D hu (reflectedCharge tau v)) delta
  have killed (u v : Bool) : (deltaEnd ^ K) (commutator (A u) (B v)) = 0 := by
    rw [Module.End.pow_apply]
    apply FiniteFieldLocality.monotone _
      (bilinear D (reflectedCharge sigma u) (reflectedCharge tau v)).natAbs K
      (by simpa only [reflected_bilinear_natAbs] using hK)
    exact LatticeHalfFockPhysicalWordLocality.physicalSlice_charged_locality
      D hu (reflectedCharge sigma u) (reflectedCharge tau v) gamma delta
  have split : commutator
      (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
      (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta) =
      (1 / 4 : ℂ) • (commutator (A false) (B false) +
        projectedSign eta • commutator (A false) (B true) +
        projectedSign epsilon • commutator (A true) (B false) +
        (projectedSign epsilon * projectedSign eta) • commutator (A true) (B true)) := by
    rw [projected_slice, projected_slice]
    funext m n
    apply LinearMap.ext
    intro x
    simp only [FieldNormalProductLocality.commutator, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.mul_apply, A, B, reflectedCharge, Bool.false_eq_true,
      if_false, if_true]
    module
  rw [split]
  simp only [map_smul, map_add, killed, smul_zero, add_zero]

/- The adapter consumes the actual ordered residue constructor; it does not
   posit a source-to-residue law. -/
theorem physicalResidueCoefficient_eq_R
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    physicalResidueCoefficient A B r n x = ((Calculus.R A B r)[[n]]) x := by
  simp only [Calculus.R, VertexOperator.ncoeff_of_coeff]
  rw [show -(-n-1)-1 = n by omega]
  change physicalResidueCoefficient A B r n x =
    (∑ᶠ j : ℕ, residueWeight r j • (A[[r-j]]) ((B[[n+j]]) x)) -
      (-1 : ℂ)^r • ∑ᶠ j : ℕ, residueWeight r j • (B[[n+r-j]]) ((A[[j]]) x)
  have choose (j : ℕ) : ((Ring.choose r j : ℤ) : ℂ) = Ring.choose (r : ℂ) j :=
    Ring.map_choose (Int.castRingHom ℂ) r j
  simp only [physicalResidueCoefficient, physicalResidueLeft, physicalResidueRight,
    physicalResidueWeight, StateFieldResidueReconstruction.integerBinomial,
    residueWeight, choose, add_comm n r]

/-- The complete residue has an independent unweighted tail, also at the
boundary and when the natural outer cutoff is zero. No individual ordered
branch is asserted to vanish. -/
theorem chargedPhysicalResidueRow_tail (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K)
    (l : ℕ) (hl : ((K : ℤ) - r).toNat ≤ l) (x : ActualTensor D hu) :
    chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x = 0 := by
  have hr : (K : ℤ) ≤ r + (l : ℤ) := by omega
  obtain ⟨degree, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r + (l : ℤ) by omega)
  have hdegree : K ≤ degree := by omega
  have locality := projected_locality D hu sigma tau epsilon eta gamma delta K hK
  have killed := Module.End.pow_map_zero_of_le hdegree locality
  unfold chargedPhysicalResidueRow
  rw [physicalResidueCoefficient_eq_R, hd, Calculus.R_nat, killed]
  rfl

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
