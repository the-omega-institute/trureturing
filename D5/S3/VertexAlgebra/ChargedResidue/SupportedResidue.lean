/- GID: D5/S3/VertexAlgebra/ChargedResidue/SupportedResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/SupportedResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual supported residue consumes the two-pole scalar identity. -/
import D5.S3.VertexAlgebra.ChargedResidue.FiniteChambers

/-! Whole ordered sums are enlarged before their monomial expansions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedCollision
open LatticeHalfFockProductKernel LatticeHalfFockPhysicalRescaling
open scoped BigOperators TensorProduct
noncomputable section

def twoPoleScalar (q B v : ℤ) : ℂ :=
  (1/2 : ℂ) * (2 : ℂ)^(-2*B) *
    (if -q-1-B < 0 then 0 else collisionScalar (v-2*q-2) B (-q-1-B).toNat) +
  (-1 : ℂ)^v * (1/2 : ℂ) * (2 : ℂ)^(2*B) *
    (if -q-1+B < 0 then 0 else collisionScalar (v-2*q-2) (-B) (-q-1+B).toNat)

def physicalResidueCollisionDiagonal (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (d : Fin 2 →₀ ℕ) : Oscillator D :=
  let total := physicalCreationTotal D left right gamma delta q z d
  if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat+1),
      twoPoleScalar q (bilinear D left right)
        ((m : ℤ)-(-2*q-gamma-2+chargeNorm D left+d 0)) •
        (halfCreationCoeff D left m * halfCreationCoeff D right (total-m))

/- proof_shape: chargedPhysicalResidueRow_collision_diagonal: content
   admission_basis: escape-witness
   escape_witness: Each complete ordered tensor range is enlarged using its
   own actual field order. Only then are its translated monomial supports
   reindexed, and the two signed scalar convolutions cancelled by the
   quadratic residue theorem with Jacobian, for every supported creation term.
   literature_status: classical finite twisted-lattice residue calculus. -/
theorem chargedPhysicalResidueRow_collision_diagonal (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (l : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l (p ⊗ₜ[ℂ] g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (pairTranslation D sigma tau p).support,
          (pairTranslation D sigma tau p).coeff d *
            physicalResidueCollisionDiagonal D sigma tau gamma delta (r+l) (n-l) d)
              ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)) := by
  classical
  let F := max
    (-(n-l)-((HahnModule.of ℂ).symm
      ((physicalSlice D hu (chargedField D hu tau) delta) (p ⊗ₜ[ℂ] g))).order).toNat
    (nativeContractionCutoff D sigma tau (-2*(n-l)-delta-2) p)
  let R := max
    (-((HahnModule.of ℂ).symm
      ((physicalSlice D hu (chargedField D hu sigma) gamma) (p ⊗ₜ[ℂ] g))).order).toNat
    (nativeContractionCutoff D tau sigma (-gamma-2) p)
  rw [chargedPhysicalResidueRow_joint_supported D hu sigma tau epsilon eta gamma delta r n
    hgamma hdelta l p g F R (le_max_left _ _) (le_max_left _ _)]
  apply congrArg (fun O : Oscillator D =>
    (chargeScalar D sigma * chargeScalar D tau) •
      (O ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)))
  apply Finset.sum_congr rfl
  intro d member
  congr 1
  unfold nativeJointDiagonal physicalResidueCollisionDiagonal
  by_cases negative : physicalCreationTotal D sigma tau gamma delta (r+l) (n-l) d < 0
  · simp only [ite_eq_left negative]
  · simp only [ite_eq_right negative]
    apply Finset.sum_congr rfl
    intro m within
    have m_bound := Finset.mem_range.mp within
    have right_support := Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 1) member
    have right_integer : (d 1 : ℤ) ≤
        ((pairTranslation D sigma tau p).support.sup (fun d => d 1) : ℕ) := by
      exact_mod_cast right_support
    have forward : (m : ℤ)-(-2*(r+l)-gamma-2+chargeNorm D sigma+d 0) < F := by
      have cutoff : nativeContractionCutoff D sigma tau (-2*(n-l)-delta-2) p ≤ F :=
        le_max_right _ _
      dsimp only [nativeContractionCutoff] at cutoff
      dsimp only [physicalCreationTotal] at negative m_bound
      omega
    have reverse_bound := reverse_support_bound D sigma tau (-gamma-2) p d member
    have reverse : 2*(r+l)-((m : ℤ)-(-2*(r+l)-gamma-2+chargeNorm D sigma+d 0)) < R := by
      have cutoff : nativeContractionCutoff D tau sigma (-gamma-2) p ≤ R := le_max_right _ _
      omega
    rw [native_chamber_scalar_full D sigma tau (r+l)
      ((m : ℤ)-(-2*(r+l)-gamma-2+chargeNorm D sigma+d 0)) F R forward reverse]
    rfl

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
