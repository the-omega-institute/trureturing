/- GID: D5/S3/VertexAlgebra/ChargedResidue/Forward
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/Forward
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete physical charged residue is the finite binomial collision transform. -/
import D5.S3.VertexAlgebra.ChargedResidue.Reflections

/-! Arbitrary actual input and the original matching integer lifts are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCollision
open scoped BigOperators TensorProduct VertexOperator
noncomputable section

/- proof_shape: chargedPhysicalResidueRow_forward: content
   admission_basis: escape-witness
   escape_witness: Both independently supported ordered expansions are combined
   on the common creation diagonal, then evaluated by residue substitution with
   Jacobian and all four reflected kernels. Tensor induction uses the actual
   finite-support additivity of each ordered physical residue.
   literature_status: classical twisted-lattice residue calculus. -/
theorem chargedPhysicalResidueRow_forward (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K)
    (l : ℕ) (x : ActualTensor D hu) :
    chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x =
      ∑ k ∈ Finset.range (((K : ℤ)-r).toNat-l),
        Ring.choose ((gamma : ℂ)/2) k •
          chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n (l+k) x := by
  classical
  by_cases htail : ((K : ℤ)-r).toNat ≤ l
  · rw [chargedPhysicalResidueRow_tail D hu sigma tau epsilon eta gamma delta r n
      K hK l htail x]
    simp only [Nat.sub_eq_zero_of_le htail, Finset.range_zero, Finset.sum_empty]
  have residue_add (x y : ActualTensor D hu) :
      chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l (x+y) =
        chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x +
          chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l y := by
    unfold chargedPhysicalResidueRow physicalResidueCoefficient physicalResidueLeft physicalResidueRight
    simp only [map_add, smul_add]
    rw [finsum_add_distrib
      (chargedPhysicalResidueRow_left_finite D hu sigma tau epsilon eta gamma delta r n l x)
      (chargedPhysicalResidueRow_left_finite D hu sigma tau epsilon eta gamma delta r n l y),
      finsum_add_distrib
        (chargedPhysicalResidueRow_right_finite D hu sigma tau epsilon eta gamma delta r n l x)
        (chargedPhysicalResidueRow_right_finite D hu sigma tau epsilon eta gamma delta r n l y)]
    module
  simp_rw [← chargedPhysicalSourceRow_eq_collision]
  induction x using TensorProduct.induction_on with
  | zero =>
    simp [chargedPhysicalResidueRow, physicalResidueCoefficient, physicalResidueLeft,
      physicalResidueRight, chargedPhysicalSourceRow, chargedGroundSourceCoefficient]
  | add x y hx hy =>
    rw [residue_add, hx, hy]
    simp only [chargedPhysicalSourceRow, chargedGroundSourceCoefficient,
      map_add, smul_add, Finset.sum_add_distrib]
  | tmul p g =>
    simp_rw [chargedPhysicalSourceRow_eq_collision]
    rw [chargedPhysicalResidueRow_collision_diagonal D hu sigma tau epsilon eta gamma delta r n
      hgamma hdelta l p g,
      chargedPhysicalCollisionRow_transform_native D hu sigma tau epsilon eta gamma delta r n
        l K hK p g,
      charged_reflected_collision_diagonal D hu sigma tau epsilon eta gamma delta r n
        hgamma hdelta l p g]

/- proof_shape: chargedPhysicalSourceRow_inverse: bind-only
   consumer: chargedGroundSource_to_Q
   obligation: instantiate the finite inverse on the proved actual full family. -/
theorem chargedPhysicalSourceRow_inverse (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K) (x : ActualTensor D hu) :
    chargedPhysicalSourceRow D hu sigma tau epsilon eta gamma delta r n 0 x =
      ∑ l ∈ Finset.range (((K : ℤ)-r).toNat),
        Ring.choose (-(gamma : ℂ)/2) l •
          chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x := by
  rw [chargedPhysicalSourceRow_eq_collision]
  have inverse := charged_finite_binomial_inverse ((gamma : ℂ)/2) (((K : ℤ)-r).toNat)
    (fun l => chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n l x)
    (fun l => chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x)
    (fun l _ => chargedPhysicalResidueRow_forward D hu sigma tau epsilon eta gamma delta r n
      hgamma hdelta K hK l x)
    (fun l hl => chargedPhysicalCollisionRow_tail D hu sigma tau epsilon eta gamma delta r n
      K hK l hl x)
  simpa only [neg_div] using inverse

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
