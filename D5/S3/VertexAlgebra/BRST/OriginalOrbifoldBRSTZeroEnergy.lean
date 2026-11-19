/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTZeroEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTZeroEnergy
   mirror-E: none(waiver:algebraic-original-brst-zero-energy-reduction)
   anchors: []
   utility: none
   digest: Zero-energy retraction of the actual critical Leech orbifold BRST complex. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatter
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction

/-! The algebraic energy splitting of the original orbifold, hyperbolic lattice and
native bc carrier. The lattice basis and coefficient-weight homotopy are from
`LatticeBRSTZeroEnergyReduction`. Total energy uses the signed ghost occupation
energy, with the ghost vacuum at energy zero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTZeroEnergy

open OriginalOrbifoldCriticalMatter
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open Module.End (eigenspace mem_eigenspace_iff)

-- Expose the canonical tensor instance through the native State abbreviation.
local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev orbifoldGrade (n : ℕ) := (orbifoldMode 0).eigenspace (n : ℂ)

private theorem orbifold_grades_internal : DirectSum.IsInternal orbifoldGrade :=
  TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_positive_integral_grading.1

private def orbifoldGradeBasis (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (orbifoldGrade n))) ℂ (orbifoldGrade n) :=
  letI : FiniteDimensional ℂ (orbifoldGrade n) :=
    TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_positive_integral_grading.2.2 n
  Module.finBasis ℂ (orbifoldGrade n)

abbrev OrbifoldLabel := Σ n : ℕ, Fin (Module.finrank ℂ (orbifoldGrade n))

def orbifoldBasis : Module.Basis OrbifoldLabel ℂ Orbifold :=
  orbifold_grades_internal.collectedBasis orbifoldGradeBasis

private theorem orbifoldMode_basis (label : OrbifoldLabel) :
    orbifoldMode 0 (orbifoldBasis label) = (label.1 : ℂ) • orbifoldBasis label :=
  mem_eigenspace_iff.mp (orbifold_grades_internal.collectedBasis_mem orbifoldGradeBasis label)

abbrev FullLabel := OrbifoldLabel × LatticeBRSTZeroEnergyReduction.FullLabel hyperbolicData

/-- A basis indexed by orbifold weight, hyperbolic monomial and charge, and ghost occupation. -/
def fullBasis : Module.Basis FullLabel ℂ State :=
  (orbifoldBasis.tensorProduct (LatticeBRSTZeroEnergyReduction.fullBasis hyperbolicData)).map
    (TensorProduct.assoc ℂ Orbifold Hyperbolic Fock).symm

def totalEnergy (label : FullLabel) : ℤ :=
  (label.1.1 : ℤ) + LatticeBRSTZeroEnergyReduction.totalEnergy hyperbolicData label.2

abbrev totalL0 : Module.End ℂ State := VirasoroBRST.Ltotal matterDatum 0

private theorem fullBasis_apply (label : FullLabel) :
    fullBasis label =
      (orbifoldBasis label.1 ⊗ₜ[ℂ] LatticePositiveEnergy.carrierBasis hyperbolicData label.2.1)
        ⊗ₜ[ℂ] ket label.2.2 := by
  simp only [fullBasis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply',
    LatticeBRSTZeroEnergyReduction.fullBasis, Finsupp.coe_basisSingleOne, ket,
    TensorProduct.assoc_symm_tmul]

/-- The actual total zero mode is diagonal in the tensor basis at the indicated integer energies. -/
theorem totalL0_basis (label : FullLabel) :
    totalL0 (fullBasis label) = (totalEnergy label : ℂ) • fullBasis label := by
  have hyperbolicEigen :
      hyperbolicMode 0 (LatticePositiveEnergy.carrierBasis hyperbolicData label.2.1) =
        (LatticePositiveEnergy.energy hyperbolicData label.2.1 : ℂ) •
          LatticePositiveEnergy.carrierBasis hyperbolicData label.2.1 :=
    LatticePositiveEnergy.actualL0_basis hyperbolicData hyperbolicInverse
      hyperbolic_inverse_left hyperbolic_inverse_right label.2.1
  change
    (TensorProduct.map (mode 0) LinearMap.id +
      TensorProduct.map LinearMap.id (BcGhostVirasoro.L 0) : Module.End ℂ State)
      (fullBasis label) = _
  simp only [fullBasis_apply, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    mode, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, orbifoldMode_basis, hyperbolicEigen,
    BcGhostRelativeEnergy.L_zero_ket, TensorProduct.add_tmul, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, totalEnergy, LatticeBRSTZeroEnergyReduction.totalEnergy,
    Int.cast_add, Int.cast_natCast, add_smul]
  abel

/-- The whole carrier is the algebraic direct sum of the actual integer eigenspaces. -/
theorem integral_grading :
    DirectSum.IsInternal (fun n : ℤ => totalL0.eigenspace (n : ℂ)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact totalL0.eigenspaces_iSupIndep.comp Int.cast_injective
  · apply top_unique
    rw [← fullBasis.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨label, rfl⟩
    exact le_iSup (fun n : ℤ => totalL0.eigenspace (n : ℂ)) (totalEnergy label)
      (mem_eigenspace_iff.mpr (totalL0_basis label))

/-- Multiply each finitely supported basis coefficient by its energy's weight. -/
def energyWeight (weight : ℤ → ℂ) : Module.End ℂ State :=
  fullBasis.constr ℂ (fun label => weight (totalEnergy label) • fullBasis label)

private theorem energyWeight_basis (weight : ℤ → ℂ) (label : FullLabel) :
    energyWeight weight (fullBasis label) = weight (totalEnergy label) • fullBasis label :=
  fullBasis.constr_basis ℂ (fun input => weight (totalEnergy input) • fullBasis input) label

theorem energyWeight_coeff (weight : ℤ → ℂ) (x : State) (label : FullLabel) :
    fullBasis.repr (energyWeight weight x) label =
      weight (totalEnergy label) * fullBasis.repr x label := by
  classical
  let coeff : State →ₗ[ℂ] ℂ := (Finsupp.lapply label).comp fullBasis.repr.toLinearMap
  have diagonal : coeff.comp (energyWeight weight) = weight (totalEnergy label) • coeff := by
    apply fullBasis.ext
    intro input
    change coeff (energyWeight weight (fullBasis input)) =
      weight (totalEnergy label) • coeff (fullBasis input)
    rw [energyWeight_basis, map_smul]
    change weight (totalEnergy input) * fullBasis.repr (fullBasis input) label =
      weight (totalEnergy label) * fullBasis.repr (fullBasis input) label
    rw [fullBasis.repr_self]
    by_cases same : input = label
    · subst input
      rfl
    · simp [same]
  exact LinearMap.congr_fun diagonal x

private theorem totalL0_eq_energyWeight : totalL0 = energyWeight (fun n => (n : ℂ)) := by
  apply fullBasis.ext
  intro label
  rw [totalL0_basis, energyWeight_basis]

theorem totalL0_coeff (x : State) (label : FullLabel) :
    fullBasis.repr (totalL0 x) label = (totalEnergy label : ℂ) * fullBasis.repr x label := by
  rw [totalL0_eq_energyWeight, energyWeight_coeff]

theorem Q_totalL0 : Q * totalL0 = totalL0 * Q := by
  apply sub_eq_zero.mp
  simpa using VirasoroBRST.Q_Ltotal matterDatum 0

private theorem Q_energy_coeff_zero (input output : FullLabel)
    (different : totalEnergy output ≠ totalEnergy input) :
    fullBasis.repr (Q (fullBasis input)) output = 0 := by
  have eigen : totalL0 (Q (fullBasis input)) =
      (totalEnergy input : ℂ) • Q (fullBasis input) := by
    simpa only [Module.End.mul_apply, totalL0_basis, map_smul] using
      LinearMap.congr_fun Q_totalL0.symm (fullBasis input)
  have coeff := congrArg (fun x : State => fullBasis.repr x output) eigen
  rw [totalL0_coeff, fullBasis.repr.map_smul, Finsupp.smul_apply, smul_eq_mul] at coeff
  by_contra nonzero
  exact different (Int.cast_injective (mul_right_cancel₀ nonzero coeff))

private theorem energyWeight_commutes (weight : ℤ → ℂ) :
    energyWeight weight * Q = Q * energyWeight weight := by
  apply fullBasis.ext
  intro input
  change energyWeight weight (Q (fullBasis input)) = Q (energyWeight weight (fullBasis input))
  rw [energyWeight_basis, map_smul]
  apply fullBasis.repr.injective
  ext output
  rw [energyWeight_coeff, fullBasis.repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases same : totalEnergy output = totalEnergy input
  · rw [same]
  · rw [Q_energy_coeff_zero input output same, mul_zero, mul_zero]

/-- The projection that retains exactly the zero-energy coefficients. -/
def P0 : Module.End ℂ State :=
  energyWeight (fun energy => if energy = 0 then 1 else 0)

/-- The inverse energy multiplier, extended by zero on energy zero. -/
def EInv : Module.End ℂ State := energyWeight (fun energy => (energy : ℂ)⁻¹)

def h : Module.End ℂ State := b 0 * EInv

theorem P0_commutes : P0 * Q = Q * P0 :=
  energyWeight_commutes _

theorem EInv_commutes : EInv * Q = Q * EInv :=
  energyWeight_commutes _

theorem EInv_totalL0 : EInv * totalL0 = 1 - P0 := by
  apply fullBasis.ext
  intro label
  simp only [Module.End.mul_apply, totalL0_basis, map_smul, P0, EInv, energyWeight_basis,
    smul_smul, LinearMap.sub_apply, Module.End.one_apply]
  by_cases zero : totalEnergy label = 0
  · simp [zero]
  · have nonzero : (totalEnergy label : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    simp [zero, nonzero]

theorem totalL0_EInv : totalL0 * EInv = 1 - P0 := by
  rw [← EInv_totalL0]
  apply fullBasis.ext
  intro label
  simp only [Module.End.mul_apply, EInv, energyWeight_basis, totalL0_basis, map_smul, smul_smul]
  rw [mul_comm]

theorem totalL0_P0 (x : State) : totalL0 (P0 x) = 0 := by
  have killed : totalL0 * P0 = 0 := by
    apply fullBasis.ext
    intro label
    simp only [Module.End.mul_apply, P0, energyWeight_basis, totalL0_basis, map_smul,
      smul_smul, LinearMap.zero_apply]
    by_cases zero : totalEnergy label = 0 <;> simp [zero]
  exact LinearMap.congr_fun killed x

/-- The fixed space of the projection is exactly the native total zero-mode kernel. -/
theorem P0_fixed_iff (x : State) : P0 x = x ↔ totalL0 x = 0 := by
  constructor
  · intro fixed
    rw [← fixed]
    exact totalL0_P0 x
  · intro killed
    have equality := LinearMap.congr_fun EInv_totalL0 x
    change EInv (totalL0 x) = x - P0 x at equality
    rw [killed, map_zero] at equality
    exact (sub_eq_zero.mp equality.symm).symm

theorem homotopy_identity : Q * h + h * Q = 1 - P0 := by
  calc
    Q * h + h * Q = (Q * b 0 + b 0 * Q) * EInv := by
      simp only [h, add_mul, mul_assoc, EInv_commutes]
    _ = totalL0 * EInv := congrArg (fun T => T * EInv) (Q_ward_b 0)
    _ = 1 - P0 := totalL0_EInv

/-- For any native BRST cycle, its zero-energy projection is a cycle in the same class. -/
theorem cycle_reduction (x : State) (hx : Q x = 0) :
    totalL0 (P0 x) = 0 ∧ Q (P0 x) = 0 ∧ x - P0 x = Q (h x) := by
  refine ⟨totalL0_P0 x, ?_, ?_⟩
  · have commute := LinearMap.congr_fun P0_commutes x
    simpa only [Module.End.mul_apply, hx, map_zero] using commute.symm
  · have equality := LinearMap.congr_fun homotopy_identity x
    simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hx, map_zero, add_zero] using equality.symm

/-- Projecting an arbitrary primitive of a zero-energy boundary gives a zero-energy primitive. -/
theorem boundary_reduction (x y : State) (hx : totalL0 x = 0) (hy : Q y = x) :
    totalL0 (P0 y) = 0 ∧ Q (P0 y) = x := by
  refine ⟨totalL0_P0 y, ?_⟩
  have commute := LinearMap.congr_fun P0_commutes y
  change P0 (Q y) = Q (P0 y) at commute
  rw [hy, (P0_fixed_iff x).mpr hx] at commute
  exact commute.symm

#print axioms fullBasis
#print axioms totalL0_basis
#print axioms integral_grading
#print axioms energyWeight_coeff
#print axioms totalL0_coeff
#print axioms Q_totalL0
#print axioms P0_commutes
#print axioms EInv_commutes
#print axioms EInv_totalL0
#print axioms totalL0_EInv
#print axioms totalL0_P0
#print axioms P0_fixed_iff
#print axioms homotopy_identity
#print axioms cycle_reduction
#print axioms boundary_reduction

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTZeroEnergy
