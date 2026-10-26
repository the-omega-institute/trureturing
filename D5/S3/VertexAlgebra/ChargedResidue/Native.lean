/- GID: D5/S3/VertexAlgebra/ChargedResidue/Native
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/Native
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both actual physical residue branches have independently supported finite native kernels. -/

/- proof_shape: chargedPhysicalResidueRow_native: content
   admission_basis: escape-witness
   escape_witness: Each contraction range is computed from its own right
   exponent and pair-translated input polynomial. The reverse branch swaps
   both charges and exponents; the two actual inner-field orders bound the
   outer mode sums independently.
   literature_status: classical twisted-lattice coefficient calculus; no novelty claim. -/

import D5.S3.VertexAlgebra.ChargedResidue.Locality
import D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

/-! Pointwise supported kernels of the complete physical residue. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients LatticeHalfFockProductKernel
open LatticeHalfFockCorrectedField LatticeHalfFockFockNormalField
open LatticeHalfFockGroundRightCurrentTransport LatticeHalfFockPhysicalRescaling
open LatticeHalfFockPhysicalLocality LatticeHalfFockClearedKernel
open scoped BigOperators TensorProduct VertexOperator
noncomputable section

def nativeContractionCutoff (D : LatticeData) (left right : Charge D)
    (second : ℤ) (p : Oscillator D) : ℕ :=
  (second + chargeNorm D right +
    (((pairTranslation D left right p).support.sup (fun d => d 1) : ℕ) : ℤ) + 1).toNat

def nativeOrderedKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (p : Oscillator D)
    (g : ActualGround D hu) : ActualTensor D hu :=
  (chargeScalar D left * chargeScalar D right) •
    ((∑ k ∈ Finset.range (nativeContractionCutoff D left right second p),
      (PowerSeries.coeff k (halfContraction D left right)) •
        commonKernel D left right (first + chargeNorm D left + k)
          (second + chargeNorm D right - k) p) ⊗ₜ[ℂ]
      groundAction D hu left (groundAction D hu right g))

def nativeReversedKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (p : Oscillator D)
    (g : ActualGround D hu) : ActualTensor D hu :=
  (paritySign (bilinear D left right) * (chargeScalar D left * chargeScalar D right)) •
    ((∑ k ∈ Finset.range (nativeContractionCutoff D right left first p),
      (PowerSeries.coeff k (halfContraction D right left)) •
        commonKernel D left right (first + chargeNorm D left - k)
          (second + chargeNorm D right + k) p) ⊗ₜ[ℂ]
      groundAction D hu left (groundAction D hu right g))

theorem native_kernel_reverse (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (p : Oscillator D)
    (g : ActualGround D hu) :
    nativeOrderedKernel D hu right left second first p g =
      nativeReversedKernel D hu left right first second p g := by
  unfold nativeOrderedKernel nativeReversedKernel
  simp_rw [common_kernel_branch_exchange D right left]
  have exchange := congrArg (fun T : Module.End ℂ (ActualGround D hu) => T g)
    (LatticeHalfFockGroundProducts.ground_action_exchange D hu right left)
  change groundAction D hu right (groundAction D hu left g) =
    paritySign (bilinear D right left) •
      groundAction D hu left (groundAction D hu right g) at exchange
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D right left] at exchange
  rw [exchange, TensorProduct.tmul_smul, smul_smul]
  congr 1
  ring

theorem native_ordered_range (D : LatticeData) (hu : IsUnit D.G.det)
    (left right : Charge D) (first second : ℤ) (p : Oscillator D)
    (g : ActualGround D hu) :
    chargedCoefficient D hu left first
      (chargedCoefficient D hu right second (p ⊗ₜ[ℂ] g)) =
      nativeOrderedKernel D hu left right first second p g := by
  classical
  rw [product_pure]
  apply congrArg (fun z : Oscillator D => (chargeScalar D left * chargeScalar D right) •
    (z ⊗ₜ[ℂ] groundAction D hu left (groundAction D hu right g)))
  change (∑ᶠ k : ℕ, (PowerSeries.coeff k (halfContraction D left right)) •
    commonKernel D left right (first + chargeNorm D left + k)
      (second + chargeNorm D right - k) p) = _
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra outside
  have hkbound : nativeContractionCutoff D left right second p ≤ k := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using outside
  have zero : commonKernel D left right (first + chargeNorm D left + k)
      (second + chargeNorm D right - k) p = 0 := by
    rw [kernel_expansion]
    apply Finset.sum_eq_zero
    intro d hd
    have hb := Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 1) hd
    have hb' : (d 1 : ℤ) ≤
        (((pairTranslation D left right p).support.sup (fun d => d 1) : ℕ) : ℤ) := by
      exact_mod_cast hb
    have negative : second + chargeNorm D right - k + d 1 < 0 := by
      dsimp [nativeContractionCutoff] at hkbound
      omega
    simp only [halfCreationCoeff, if_pos negative, mul_zero]
  exact hk (by simp only [zero, smul_zero])

private theorem slice_parity (gamma m : ℤ) :
    (-1 : ℂ) ^ (-2 * m - gamma - 2) = (-1 : ℂ) ^ gamma := by
  rw [show -2*m-gamma-2 = gamma+2*(-m-gamma-1) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    (even_two_mul (-m-gamma-1)).neg_one_zpow, mul_one]

private theorem projected_ordered_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta m n : ℤ)
    (x : ActualTensor D hu) :
    let A := fun c => (physicalSlice D hu (chargedField D hu c) gamma)[[m]]
    let B := fun c => (physicalSlice D hu (chargedField D hu c) delta)[[n]]
    ((physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)[[m]])
      (((physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)[[n]]) x) =
      (1 / 4 : ℂ) • (A sigma (B tau x) +
        projectedSign eta • A sigma (B (-tau) x) +
        projectedSign epsilon • A (-sigma) (B tau x) +
        (projectedSign epsilon * projectedSign eta) • A (-sigma) (B (-tau) x)) := by
  dsimp only
  rw [projectedGround_slice_mode_expansion D hu sigma epsilon gamma m]
  simp_rw [projectedGround_slice_mode_expansion D hu tau eta delta n]
  simp only [map_add, map_smul, smul_add, smul_smul]
  module

private theorem projected_ordered_matching (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta m n : ℤ)
    (hgamma : (-1 : ℂ) ^ gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ) ^ delta = projectedSign eta) (x : ActualTensor D hu) :
    ((physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)[[m]])
      (((physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)[[n]]) x) =
      ((physicalSlice D hu (chargedField D hu sigma) gamma)[[m]])
        (((physicalSlice D hu (chargedField D hu tau) delta)[[n]]) x) := by
  rw [projected_ordered_expansion]
  dsimp only
  simp only [physicalSlice_mode, chargedField, HVertexOperator.coeff_of_coeff]
  rw [LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy
    D hu sigma (-2*m-gamma-2),
    LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy
      D hu tau (-2*n-delta-2)]
  simp only [LinearMap.smul_apply, map_smul, smul_smul, slice_parity, hgamma, hdelta]
  cases epsilon <;> cases eta <;>
    simp only [projectedSign, Bool.false_eq_true, ite_false, ite_true]
  all_goals module

private theorem projected_slice_matching (D : LatticeData) (hu : IsUnit D.G.det)
    (alpha : Charge D) (epsilon : Bool) (gamma : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon) :
    physicalSlice D hu (correctedField D hu (projectedGround D alpha epsilon)) gamma =
      physicalSlice D hu (chargedField D hu alpha) gamma := by
  apply HVertexOperator.coeff_inj
  funext e
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  apply LinearMap.ext
  intro x
  rw [projectedGround_slice_mode_expansion, physicalSlice_mode, physicalSlice_mode]
  simp only [chargedField, HVertexOperator.coeff_of_coeff]
  rw [LatticeHalfFockChargedMonodromy.charged_coefficient_coordinate_monodromy]
  simp only [LinearMap.smul_apply, smul_smul]
  rw [slice_parity, hgamma]
  cases epsilon <;> simp only [projectedSign, Bool.false_eq_true, if_false, if_true]
  all_goals module

private theorem residue_left_range {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    physicalResidueLeft A B r n x =
      ∑ j ∈ Finset.range (-n-((HahnModule.of ℂ).symm (B x)).order).toNat,
        physicalResidueWeight r j • (A[[r-j]]) ((B[[n+j]]) x) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra outside
  have bound : (-n-((HahnModule.of ℂ).symm (B x)).order).toNat ≤ j := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using outside
  have zero : (B[[n+j]]) x = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact hj (by simp [zero])

private theorem residue_right_range {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (r n : ℤ) (x : M) :
    physicalResidueRight A B r n x =
      ∑ j ∈ Finset.range (-((HahnModule.of ℂ).symm (A x)).order).toNat,
        physicalResidueWeight r j • (B[[r+n-j]]) ((A[[j]]) x) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra outside
  have bound : (-((HahnModule.of ℂ).symm (A x)).order).toNat ≤ j := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using outside
  have zero : (A[[j]]) x = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  exact hj (by simp [zero])

/-- The actual complete physical row, with both matching sectors, is a
difference of finite native ordered kernels. Each branch and each translated
polynomial retains its own support. -/
theorem chargedPhysicalResidueRow_native (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (l : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    let A := physicalSlice D hu (chargedField D hu sigma) gamma
    let B := physicalSlice D hu (chargedField D hu tau) delta
    chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l
        (p ⊗ₜ[ℂ] g) =
      (∑ j ∈ Finset.range (-(n-l)-((HahnModule.of ℂ).symm (B (p ⊗ₜ[ℂ] g))).order).toNat,
        physicalResidueWeight (r+l) j • nativeOrderedKernel D hu sigma tau
          (-2*((r+l)-j)-gamma-2) (-2*((n-l)+j)-delta-2) p g) -
      (-1 : ℂ)^(r+l) •
        ∑ j ∈ Finset.range (-((HahnModule.of ℂ).symm (A (p ⊗ₜ[ℂ] g))).order).toNat,
          physicalResidueWeight (r+l) j • nativeReversedKernel D hu sigma tau
            (-2*(j:ℤ)-gamma-2) (-2*((r+l)+(n-l)-j)-delta-2) p g := by
  dsimp only
  unfold chargedPhysicalResidueRow
  unfold physicalResidueCoefficient
  rw [residue_left_range, residue_right_range]
  simp_rw [projected_ordered_matching D hu sigma tau epsilon eta gamma delta _ _
    hgamma hdelta,
    projected_ordered_matching D hu tau sigma eta epsilon delta gamma _ _ hdelta hgamma]
  rw [projected_slice_matching D hu sigma epsilon gamma hgamma,
    projected_slice_matching D hu tau eta delta hdelta]
  simp only [physicalSlice_mode, chargedField, HVertexOperator.coeff_of_coeff,
    native_ordered_range, native_kernel_reverse]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
