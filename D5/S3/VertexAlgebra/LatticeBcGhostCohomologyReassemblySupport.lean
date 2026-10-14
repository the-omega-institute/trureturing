import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
import Mathlib.LinearAlgebra.TensorProduct.Basis
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct Classical

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

noncomputable section

abbrev FullLabel (D : LatticeData) :=
  LatticePositiveEnergy.Label D × Finset ℕ

def fullBasis (D : LatticeData) :
    Module.Basis (FullLabel D) ℂ (State D) :=
  (LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))

def totalEnergy (D : LatticeData) (label : FullLabel D) : ℤ :=
  LatticePositiveEnergy.energy D label.1 + BcGhostLZeroSpectrum.energy label.2

def coefficientMap (D : LatticeData) (label : FullLabel D) :
    State D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply label).comp (fullBasis D).repr.toLinearMap

def energyWeight (D : LatticeData) (weight : ℤ → ℂ) :
    Module.End ℂ (State D) :=
  (fullBasis D).constr ℂ (fun label =>
    weight (totalEnergy D label) • fullBasis D label)

def P0 (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => if energy = 0 then 1 else 0)

def EInv (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => (energy : ℂ)⁻¹)

def h (D : LatticeData) : Module.End ℂ (State D) :=
  (B D 0).comp (EInv D)

theorem fullBasis_apply (D : LatticeData) (label : FullLabel D) :
    fullBasis D label =
      LatticePositiveEnergy.carrierBasis D label.1 ⊗ₜ[ℂ]
        Finsupp.single label.2 1 := by
  simp [fullBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basisSingleOne]

theorem totalZero_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : FullLabel D) :
    (M D H 0 + G D 0) (fullBasis D label) =
      (totalEnergy D label : ℂ) • fullBasis D label := by
  rw [fullBasis_apply]
  simp only [fullBasis_apply, LinearMap.add_apply, M, G, TensorProduct.map_tmul,
    LinearMap.id_apply, LatticePositiveEnergy.actualL0_basis D H hHG hGH,
    BcGhostLZeroSpectrum.L_zero_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, totalEnergy, Int.cast_add, add_smul]

theorem totalZero_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (label : FullLabel D) :
    (fullBasis D).repr ((M D H 0 + G D 0) state) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr state label := by
  classical
  have diagonal : (coefficientMap D label).comp (M D H 0 + G D 0) =
      (totalEnergy D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label ((M D H 0 + G D 0) (fullBasis D input)) =
      (totalEnergy D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [totalZero_basis D H hHG hGH, map_smul]
    change (totalEnergy D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input
      rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal state

theorem totalZero_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * Q D H = Q D H * (M D H 0 + G D 0) := by
  have covariance := LatticeBcGhostBrstTotalCovariance.total_covariance D H hHG hGH 0
  have vanished : Q D H * (M D H 0 + G D 0) -
      (M D H 0 + G D 0) * Q D H = 0 := by
    simpa using covariance
  exact (sub_eq_zero.mp vanished).symm

theorem Q_energy_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (different : totalEnergy D output ≠ totalEnergy D input) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  have eigenvector : (M D H 0 + G D 0) (Q D H (fullBasis D input)) =
      (totalEnergy D input : ℂ) • Q D H (fullBasis D input) := by
    have equality := LinearMap.congr_fun (totalZero_commutes D H hHG hGH)
      (fullBasis D input)
    simpa only [Module.End.mul_apply, totalZero_basis D H hHG hGH, map_smul]
      using equality
  have coefficients := congrArg (fun state : State D => (fullBasis D).repr state output)
    eigenvector
  rw [totalZero_coeff D H hHG hGH] at coefficients
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficients
  have separated : ((totalEnergy D output : ℂ) - (totalEnergy D input : ℂ)) *
      (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
    rw [sub_mul, coefficients, sub_self]
  have scalarNonzero : (totalEnergy D output : ℂ) - (totalEnergy D input : ℂ) ≠ 0 := by
    intro equality
    exact different (Int.cast_injective (sub_eq_zero.mp equality))
  exact (mul_eq_zero.mp separated).resolve_left scalarNonzero

theorem energyWeight_basis (D : LatticeData) (weight : ℤ → ℂ)
    (label : FullLabel D) :
    energyWeight D weight (fullBasis D label) =
      weight (totalEnergy D label) • fullBasis D label := by
  exact (fullBasis D).constr_basis ℂ
    (fun input => weight (totalEnergy D input) • fullBasis D input) label

theorem energyWeight_coeff (D : LatticeData) (weight : ℤ → ℂ)
    (state : State D) (label : FullLabel D) :
    (fullBasis D).repr (energyWeight D weight state) label =
      weight (totalEnergy D label) * (fullBasis D).repr state label := by
  classical
  have diagonal : (coefficientMap D label).comp (energyWeight D weight) =
      weight (totalEnergy D label) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (energyWeight D weight (fullBasis D input)) =
      weight (totalEnergy D label) • coefficientMap D label (fullBasis D input)
    rw [energyWeight_basis, map_smul]
    change weight (totalEnergy D input) * (fullBasis D).repr (fullBasis D input) label =
      weight (totalEnergy D label) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input
      rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal state

theorem energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    energyWeight D weight * Q D H = Q D H * energyWeight D weight := by
  classical
  apply (fullBasis D).ext
  intro input
  change energyWeight D weight (Q D H (fullBasis D input)) =
    Q D H (energyWeight D weight (fullBasis D input))
  rw [energyWeight_basis, map_smul]
  apply (fullBasis D).repr.injective
  ext output
  rw [energyWeight_coeff]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases zeroCoefficient : (fullBasis D).repr (Q D H (fullBasis D input)) output = 0
  · simp only [zeroCoefficient, mul_zero]
  · have equalEnergy : totalEnergy D output = totalEnergy D input := by
      by_contra different
      exact zeroCoefficient (Q_energy_coeff_zero D H hHG hGH input output different)
    rw [equalEnergy]

theorem totalZero_energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    (M D H 0 + G D 0) * energyWeight D weight =
      energyWeight D weight * (M D H 0 + G D 0) := by
  apply (fullBasis D).ext
  intro label
  simp only [Module.End.mul_apply, energyWeight_basis,
    totalZero_basis D H hHG hGH, map_smul, smul_smul]
  rw [mul_comm]

theorem EInv_totalZero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    EInv D * (M D H 0 + G D 0) = 1 - P0 D := by
  classical
  apply (fullBasis D).ext
  intro label
  change EInv D ((M D H 0 + G D 0) (fullBasis D label)) =
    fullBasis D label - P0 D (fullBasis D label)
  rw [totalZero_basis D H hHG hGH, map_smul]
  change (totalEnergy D label : ℂ) •
      energyWeight D (fun energy => (energy : ℂ)⁻¹) (fullBasis D label) =
    fullBasis D label -
      energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)
  rw [energyWeight_basis, energyWeight_basis, smul_smul]
  by_cases zeroEnergy : totalEnergy D label = 0
  · simp [zeroEnergy]
  · have scalarNonzero : (totalEnergy D label : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr zeroEnergy
    simp [zeroEnergy, scalarNonzero]

theorem totalZero_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (M D H 0 + G D 0) * P0 D = 0 := by
  classical
  apply (fullBasis D).ext
  intro label
  change (M D H 0 + G D 0)
    (energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)) = 0
  rw [energyWeight_basis, map_smul, totalZero_basis D H hHG hGH, smul_smul]
  by_cases zeroEnergy : totalEnergy D label = 0 <;> simp [zeroEnergy]

theorem homotopy_identity (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Q D H * h D + h D * Q D H = 1 - P0 D := by
  have inverseCommutes : EInv D * Q D H = Q D H * EInv D :=
    energyWeight_commutes D H hHG hGH (fun energy => (energy : ℂ)⁻¹)
  have spectralCommutes : (M D H 0 + G D 0) * EInv D =
      EInv D * (M D H 0 + G D 0) :=
    totalZero_energyWeight_commutes D H hHG hGH (fun energy => (energy : ℂ)⁻¹)
  change Q D H * (B D 0 * EInv D) + (B D 0 * EInv D) * Q D H = 1 - P0 D
  calc
    Q D H * (B D 0 * EInv D) + (B D 0 * EInv D) * Q D H =
        (Q D H * B D 0 + B D 0 * Q D H) * EInv D := by
      simp only [add_mul, mul_assoc, inverseCommutes]
    _ = (M D H 0 + G D 0) * EInv D := by
      rw [LatticeBcGhostBrstCharge.ward_identity D H 0]
    _ = EInv D * (M D H 0 + G D 0) := spectralCommutes
    _ = 1 - P0 D := EInv_totalZero D H hHG hGH


theorem cycle_to_zero (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : Q D H x = 0) :
    ∃ y : State D, (M D H 0 + G D 0) y = 0 ∧ Q D H y = 0 ∧
      x - y = Q D H ((B D 0).comp (EInv D) x) := by
  refine ⟨P0 D x, ?_, ?_, ?_⟩
  · have killed := LinearMap.congr_fun (totalZero_P0 D H hHG hGH) x
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using killed
  · have projectionCommutes : P0 D * Q D H = Q D H * P0 D :=
      energyWeight_commutes D H hHG hGH (fun energy => if energy = 0 then 1 else 0)
    have equality := LinearMap.congr_fun projectionCommutes x
    change P0 D (Q D H x) = Q D H (P0 D x) at equality
    rw [hx, map_zero] at equality
    exact equality.symm
  · change x - P0 D x = Q D H (h D x)
    have equality := LinearMap.congr_fun (homotopy_identity D H hHG hGH) x
    simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hx, map_zero, add_zero] using equality.symm

theorem single_charge_coeff_zero (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (ghost : Fock ℂ) (output : FullLabel D)
    (different : output.1.1 ≠ charge) :
    (fullBasis D).repr (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) output = 0 := by
  classical
  change ((LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))).repr
      (Finsupp.single charge polynomial ⊗ₜ[ℂ] ghost) (output.1, output.2) = 0
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  change ghost output.2 •
    MvPolynomial.coeff output.1.2 ((Finsupp.single charge polynomial) output.1.1) = 0
  simp [Finsupp.single_apply, Ne.symm different]

theorem Q_charge_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (input output : FullLabel D) (different : output.1.1 ≠ input.1.1) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  classical
  change coefficientMap D output (Q D H (fullBasis D input)) = 0
  rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply, Q_tmul]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro mode modeMembership
  rw [map_add, map_smul, LatticeSugawaraVirasoro.sugawaraMode_single_sector]
  change (fullBasis D).repr
      (Finsupp.single input.1.1
        (LatticeSugawaraVirasoro.sectorSugawaraMode D H input.1.1 mode
          (MvPolynomial.monomial input.1.2 1)) ⊗ₜ[ℂ]
            BcGhostFockSupport.c (-mode) (Finsupp.single input.2 1)) output +
    (2 : ℂ)⁻¹ • (fullBasis D).repr
      (Finsupp.single input.1.1 (MvPolynomial.monomial input.1.2 1) ⊗ₜ[ℂ]
        BcGhostStressTails.outerNormalPair mode (Finsupp.single input.2 1)) output = 0
  rw [single_charge_coeff_zero D _ _ _ output different,
    single_charge_coeff_zero D _ _ _ output different]
  simp

theorem Q_coefficient_blocks (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (nonzero : (fullBasis D).repr (Q D H (fullBasis D input)) output ≠ 0) :
    output.1.1 = input.1.1 ∧ totalEnergy D output = totalEnergy D input := by
  constructor
  · by_contra different
    exact nonzero (Q_charge_coeff_zero D H input output different)
  · by_contra different
    exact nonzero (Q_energy_coeff_zero D H hHG hGH input output different)


end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
