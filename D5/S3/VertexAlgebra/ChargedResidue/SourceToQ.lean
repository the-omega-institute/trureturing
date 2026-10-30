/- GID: D5/S3/VertexAlgebra/ChargedResidue/SourceToQ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/SourceToQ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original charged source equals the actual Q field and supplies matching ground pairs. -/
import D5.S3.VertexAlgebra.ChargedResidue.Forward
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation

/-! Source-to-residue equality on the actual tensor carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGroundRightCurrentTransport LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling Calculus
open scoped BigOperators VertexOperator
noncomputable section

/- proof_shape: chargedGroundSource_to_Q: bind-only
   consumer: charged_sector_ground_pair
   obligation: compose the actual finite inverse with the public all-N source law. -/
theorem chargedGroundSource_to_Q (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K) :
    physicalSlice D hu
      (correctedField D hu (chargedGroundSource D sigma tau epsilon eta r)) (gamma+delta) =
      Q (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
        (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)
        gamma r K := by
  apply HVertexOperator.coeff_inj
  funext e
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  apply LinearMap.ext
  intro x
  rw [Q_mode]
  have inverse := chargedPhysicalSourceRow_inverse D hu sigma tau epsilon eta gamma delta r
    (-e-1) hgamma hdelta K hK x
  simpa only [chargedPhysicalSourceRow, chargedPhysicalOutputExponent,
    chargedGroundSourceCoefficient, chargedPhysicalResidueRow,
    physicalResidueCoefficient_eq_R, physicalSlice_mode,
    Nat.cast_zero, add_zero, sub_zero, sub_add_eq_sub_sub] using inverse

/- proof_shape: charged_sector_ground_pair: content
   admission_basis: escape-witness
   escape_witness: The complete original source-to-Q fields combine with actual
   shifted locality and the independent source tail to recover every signed
   three-supported coefficient law. No all-lifts compatibility is assumed.
   literature_status: classical finite twisted-lattice Jacobi recovery. -/
theorem charged_sector_ground_pair (D : LatticeData) (hu : IsUnit D.G.det) :
    SectorGroundPair D hu := by
  intro sigma tau epsilon eta gamma delta gammaMatch deltaMatch
  have hgamma : (-1 : ℂ)^gamma = projectedSign epsilon := gammaMatch.symm
  have hdelta : (-1 : ℂ)^delta = projectedSign eta := deltaMatch.symm
  let A := physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma
  let B := physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta
  let U := fun r => physicalSlice D hu
    (correctedField D hu (chargedGroundSource D sigma tau epsilon eta r)) (gamma+delta)
  have existsLocality := native_valid_exists D hu (projectedGround D sigma epsilon)
    (projectedGround D tau eta) gamma delta
  change ∃ KR : ℕ, ∀ shift : ℤ, Valid (Z (-shift) A) B KR at existsLocality
  obtain ⟨KR, locality⟩ := existsLocality
  let K := max KR (bilinear D sigma tau).natAbs
  have hK : (bilinear D sigma tau).natAbs ≤ K := le_max_right _ _
  have shifted : ∀ p : ℤ, Valid (Z (-p) A) B K := by
    intro p t ht
    exact locality p t (le_trans (by exact_mod_cast (le_max_left KR
      (bilinear D sigma tau).natAbs)) ht)
  have Z0 : Z 0 A = A := by
    apply HVertexOperator.coeff_inj
    funext e
    simp [Z]
  have valid : Valid A B K := by simpa only [neg_zero, Z0] using shifted 0
  have tail : ∀ t : ℤ, (K : ℤ) ≤ t → U t = 0 := by
    intro t ht
    apply HVertexOperator.coeff_inj
    funext e
    rw [VertexOperator.coeff_eq_ncoeff]
    apply LinearMap.ext
    intro x
    change ((U t)[[-e-1]]) x = 0
    have zero := chargedPhysicalSourceRow_tail D hu sigma tau epsilon eta gamma delta t
      (-e-1) K hK 0 (by omega) x
    simpa only [U, chargedPhysicalSourceRow, chargedPhysicalOutputExponent,
      chargedGroundSourceCoefficient, physicalSlice_mode, Nat.cast_zero,
      add_zero, sub_zero, sub_add_eq_sub_sub] using zero
  change fullLaw A B U gamma
  exact recover_full A B U gamma K K tail shifted valid
    (fun t => chargedGroundSource_to_Q D hu sigma tau epsilon eta gamma delta t
      hgamma hdelta K hK)

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
