/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction
   mirror-E: none(waiver:algebraic-original-brst-zero-energy-reduction)
   anchors: []
   utility: none
   digest: The critical lattice BRST quotient admits zero-energy representatives and a square-zero descended antighost. -/

/- Current-operator port on the actual lattice matter-ghost carrier.

The full-basis energyWeight/P0/EInv/h mechanism is adapted from the completed
OriginalBrstReassembly source in LatticeBcGhostCohomologyReassemblySupport
(SHA256 b9364c39f6486223c48d64b4713372282f3387a2581da8b6be0b21c68f6fb804).
The B0 CAR/Ward and explicit negative-B0 boundary-primitive mechanism is adapted
from TensorConformal.OriginalTopologicalApplications
(SHA256 85302c4b23c6e4e0f271ca7aa794ba69c65fbef4af813ca5e0204940696d95ad).
These are proof-mechanism ports, not imports of the historical Fock/BRST hierarchy.
Original authorship/copyright of those sources and their suppliers is retained:
the lattice realization follows Bakalov--Kac, the Sugawara supplier retains
Kalle Kytölä's Apache-2.0 attribution, the current field/quotient supplier retains
Scott Carnahan's attribution, and basis/quotient machinery retains Mathlib's
Apache-2.0 attribution and original authorship. No novelty is claimed.

The carrier and all operators below are the PRESENT actual ones. In particular,
totalEnergy uses raw BcGhostRelativeEnergy.energy, NOT relativeEnergy = energy+1:
c1 has energy -1, c0 has energy 0, and the vacuum intercept is zero. There is no
charge restriction or positivity assumption. Rank 26 and BOTH Gram inverses are
used to obtain actual Q²=0, hence its commutation with the actual total L0.

The sole live endpoint is Delta on the EXISTING full Cohomology, using the
imported LatticeBRSTCohomologyField API on the actual tensor-state carrier.
Square-zero here does not establish a product law, second-order law or full BV.
No multiplicativity of P0 or preservation of arbitrary cycles by raw B0 is used.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Classical

namespace D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction

open LatticeGeneratingFieldLocality (LatticeData Carrier)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State matterMode ghostB ghostVirasoro)
open LatticeBRST (totalCharge)
open LatticeBRSTCohomologyField (cycles boundaries Cohomology classOf)
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket)

noncomputable section

abbrev FullLabel (D : LatticeData) := LatticePositiveEnergy.Label D × Finset ℕ

def fullBasis (D : LatticeData) : Module.Basis (FullLabel D) ℂ (State D) :=
  (LatticePositiveEnergy.carrierBasis D).tensorProduct
    (Finsupp.basisSingleOne (ι := Finset ℕ) (R := ℂ))

def totalEnergy (D : LatticeData) (label : FullLabel D) : ℤ :=
  LatticePositiveEnergy.energy D label.1 + BcGhostRelativeEnergy.energy label.2

def totalL0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) := matterMode D H 0 + ghostVirasoro D 0

abbrev B0 (D : LatticeData) : Module.End ℂ (State D) := ghostB D 0

private def coefficientMap (D : LatticeData) (label : FullLabel D) :
    State D →ₗ[ℂ] ℂ := (Finsupp.lapply label).comp (fullBasis D).repr.toLinearMap

def energyWeight (D : LatticeData) (weight : ℤ → ℂ) : Module.End ℂ (State D) :=
  (fullBasis D).constr ℂ
    (fun label => weight (totalEnergy D label) • fullBasis D label)

def P0 (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => if energy = 0 then 1 else 0)

def EInv (D : LatticeData) : Module.End ℂ (State D) :=
  energyWeight D (fun energy => (energy : ℂ)⁻¹)

def h (D : LatticeData) : Module.End ℂ (State D) := (B0 D).comp (EInv D)

theorem fullBasis_apply (D : LatticeData) (label : FullLabel D) :
    fullBasis D label = LatticePositiveEnergy.carrierBasis D label.1 ⊗ₜ[ℂ]
      ket label.2 := by
  simp [fullBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basisSingleOne, ket]

/-- The actual total zero mode on the full all-charge/oscillator/occupation basis. -/
theorem totalL0_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (label : FullLabel D) :
    totalL0 D H (fullBasis D label) =
      (totalEnergy D label : ℂ) • fullBasis D label := by
  simp only [fullBasis_apply, totalL0, LinearMap.add_apply, matterMode, ghostVirasoro,
    TensorProduct.map_tmul, LinearMap.id_apply,
    LatticePositiveEnergy.actualL0_basis D H hHG hGH,
    BcGhostRelativeEnergy.L_zero_ket, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, totalEnergy, Int.cast_add, add_smul]

/-- Coefficient diagonalization holds for arbitrary finite mixed-energy states. -/
theorem totalL0_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (label : FullLabel D) :
    (fullBasis D).repr (totalL0 D H x) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr x label := by
  classical
  have diagonal : (coefficientMap D label).comp (totalL0 D H) =
      (totalEnergy D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (totalL0 D H (fullBasis D input)) =
      (totalEnergy D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [totalL0_basis D H hHG hGH, map_smul]
    change (totalEnergy D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (totalEnergy D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input; rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal x

private theorem critical_square (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalCharge D H * totalCharge D H = 0 := by
  have square := LatticeBRST.total_square_anomaly D H hHG hGH
  rw [h26] at square
  norm_num at square
  simpa only [pow_two] using square

/-- Derived from actual Q²=0 and actual Ward, without any old/new Q comparison. -/
theorem totalL0_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalL0 D H * totalCharge D H = totalCharge D H * totalL0 D H := by
  have square := critical_square D H h26 hHG hGH
  have ward : totalCharge D H * B0 D + B0 D * totalCharge D H = totalL0 D H :=
    LatticeBRST.total_ward_b D H 0
  calc
    totalL0 D H * totalCharge D H =
        (totalCharge D H * B0 D + B0 D * totalCharge D H) * totalCharge D H := by
      rw [ward]
    _ =
        totalCharge D H * B0 D * totalCharge D H +
          B0 D * (totalCharge D H * totalCharge D H) := by noncomm_ring
    _ = totalCharge D H * B0 D * totalCharge D H := by
      rw [square, mul_zero, add_zero]
    _ = (totalCharge D H * totalCharge D H) * B0 D +
        totalCharge D H * (B0 D * totalCharge D H) := by
      rw [square, zero_mul, zero_add, mul_assoc]
    _ = totalCharge D H * (totalCharge D H * B0 D + B0 D * totalCharge D H) := by
      noncomm_ring
    _ = totalCharge D H * totalL0 D H := by rw [ward]

private theorem Q_energy_coeff_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (input output : FullLabel D)
    (different : totalEnergy D output ≠ totalEnergy D input) :
    (fullBasis D).repr (totalCharge D H (fullBasis D input)) output = 0 := by
  have eigenvector : totalL0 D H (totalCharge D H (fullBasis D input)) =
      (totalEnergy D input : ℂ) • totalCharge D H (fullBasis D input) := by
    have equality := LinearMap.congr_fun (totalL0_commutes D H h26 hHG hGH)
      (fullBasis D input)
    simpa only [Module.End.mul_apply, totalL0_basis D H hHG hGH, map_smul]
      using equality
  have coefficients := congrArg (fun x : State D => (fullBasis D).repr x output)
    eigenvector
  rw [totalL0_coeff D H hHG hGH] at coefficients
  rw [(fullBasis D).repr.map_smul] at coefficients
  rw [Finsupp.smul_apply, smul_eq_mul] at coefficients
  have separated : ((totalEnergy D output : ℂ) - (totalEnergy D input : ℂ)) *
      (fullBasis D).repr (totalCharge D H (fullBasis D input)) output = 0 := by
    rw [sub_mul, coefficients, sub_self]
  have scalarNonzero : (totalEnergy D output : ℂ) - (totalEnergy D input : ℂ) ≠ 0 := by
    intro equality
    exact different (Int.cast_injective (sub_eq_zero.mp equality))
  exact (mul_eq_zero.mp separated).resolve_left scalarNonzero

theorem energyWeight_basis (D : LatticeData) (weight : ℤ → ℂ)
    (label : FullLabel D) :
    energyWeight D weight (fullBasis D label) =
      weight (totalEnergy D label) • fullBasis D label :=
  (fullBasis D).constr_basis ℂ
    (fun input => weight (totalEnergy D input) • fullBasis D input) label

private theorem energyWeight_coeff (D : LatticeData) (weight : ℤ → ℂ)
    (x : State D) (label : FullLabel D) :
    (fullBasis D).repr (energyWeight D weight x) label =
      weight (totalEnergy D label) * (fullBasis D).repr x label := by
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
    · subst input; rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal x

private theorem energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    energyWeight D weight * totalCharge D H = totalCharge D H * energyWeight D weight := by
  classical
  apply (fullBasis D).ext
  intro input
  change energyWeight D weight (totalCharge D H (fullBasis D input)) =
    totalCharge D H (energyWeight D weight (fullBasis D input))
  rw [energyWeight_basis, map_smul]
  apply (fullBasis D).repr.injective
  ext output
  rw [energyWeight_coeff]
  rw [(fullBasis D).repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases zeroCoefficient :
      (fullBasis D).repr (totalCharge D H (fullBasis D input)) output = 0
  · simp only [zeroCoefficient, mul_zero]
  · have equalEnergy : totalEnergy D output = totalEnergy D input := by
      by_contra different
      exact zeroCoefficient (Q_energy_coeff_zero D H h26 hHG hGH input output different)
    rw [equalEnergy]

theorem P0_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    P0 D * totalCharge D H = totalCharge D H * P0 D :=
  energyWeight_commutes D H h26 hHG hGH (fun energy => if energy = 0 then 1 else 0)

theorem EInv_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    EInv D * totalCharge D H = totalCharge D H * EInv D :=
  energyWeight_commutes D H h26 hHG hGH (fun energy => (energy : ℂ)⁻¹)

private theorem totalL0_energyWeight_commutes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (weight : ℤ → ℂ) :
    totalL0 D H * energyWeight D weight = energyWeight D weight * totalL0 D H := by
  apply (fullBasis D).ext
  intro label
  simp only [Module.End.mul_apply, energyWeight_basis,
    totalL0_basis D H hHG hGH, map_smul, smul_smul]
  rw [mul_comm]

theorem EInv_totalL0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    EInv D * totalL0 D H = 1 - P0 D := by
  classical
  apply (fullBasis D).ext
  intro label
  change EInv D (totalL0 D H (fullBasis D label)) =
    fullBasis D label - P0 D (fullBasis D label)
  rw [totalL0_basis D H hHG hGH, map_smul]
  change (totalEnergy D label : ℂ) •
      energyWeight D (fun energy => (energy : ℂ)⁻¹) (fullBasis D label) =
    fullBasis D label -
      energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)
  rw [energyWeight_basis, energyWeight_basis, smul_smul]
  by_cases zeroEnergy : totalEnergy D label = 0
  · simp [zeroEnergy]
  · have scalarNonzero : (totalEnergy D label : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zeroEnergy
    simp [zeroEnergy, scalarNonzero]

theorem totalL0_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) : totalL0 D H (P0 D x) = 0 := by
  classical
  have killed : totalL0 D H * P0 D = 0 := by
    apply (fullBasis D).ext
    intro label
    change totalL0 D H
      (energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label)) = 0
    rw [energyWeight_basis, map_smul, totalL0_basis D H hHG hGH, smul_smul]
    by_cases zeroEnergy : totalEnergy D label = 0 <;> simp [zeroEnergy]
  exact LinearMap.congr_fun killed x

/-- P0 fixes exactly the actual kernel; no positive-definiteness is needed. -/
theorem P0_fixed_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) :
    P0 D x = x ↔ totalL0 D H x = 0 := by
  constructor
  · intro fixed
    rw [← fixed]
    exact totalL0_P0 D H hHG hGH x
  · intro killed
    have equality := LinearMap.congr_fun (EInv_totalL0 D H hHG hGH) x
    change EInv D (totalL0 D H x) = x - P0 D x at equality
    rw [killed, map_zero] at equality
    exact (sub_eq_zero.mp equality.symm).symm

private theorem P0_idempotent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : State D) :
    P0 D (P0 D x) = P0 D x :=
  (P0_fixed_iff D H hHG hGH _).mpr (totalL0_P0 D H hHG hGH x)

theorem homotopy_identity (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalCharge D H * h D + h D * totalCharge D H = 1 - P0 D := by
  have inverseCommutes := EInv_commutes D H h26 hHG hGH
  have spectralCommutes : totalL0 D H * EInv D = EInv D * totalL0 D H :=
    totalL0_energyWeight_commutes D H hHG hGH (fun energy => (energy : ℂ)⁻¹)
  change totalCharge D H * (B0 D * EInv D) +
    (B0 D * EInv D) * totalCharge D H = 1 - P0 D
  calc
    _ = (totalCharge D H * B0 D + B0 D * totalCharge D H) * EInv D := by
      simp only [add_mul, mul_assoc, inverseCommutes]
    _ = totalL0 D H * EInv D := by
      change _ = (matterMode D H 0 + ghostVirasoro D 0) * EInv D
      rw [LatticeBRST.total_ward_b]
    _ = EInv D * totalL0 D H := spectralCommutes
    _ = 1 - P0 D := EInv_totalL0 D H hHG hGH

theorem P0_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : totalCharge D H x = 0) : totalCharge D H (P0 D x) = 0 := by
  have equality := LinearMap.congr_fun (P0_commutes D H h26 hHG hGH) x
  change P0 D (totalCharge D H x) = totalCharge D H (P0 D x) at equality
  rw [hx, map_zero] at equality
  exact equality.symm

/-- Explicit boundary witnessing genuine zero-energy reduction of every cycle. -/
theorem cycle_reduction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : totalCharge D H x = 0) :
    x - P0 D x = totalCharge D H (h D x) := by
  have equality := LinearMap.congr_fun (homotopy_identity D H h26 hHG hGH) x
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hx, map_zero, add_zero] using equality.symm

theorem B0_square (D : LatticeData) (x : State D) : B0 D (B0 D x) = 0 := by
  have ghostSquare (w : Fock) : BcGhostFock.b 0 (BcGhostFock.b 0 w) = 0 := by
    have car := LinearMap.congr_fun (BcGhostFock.ghost_b_car 0 0) w
    change BcGhostFock.b 0 (BcGhostFock.b 0 w) +
      BcGhostFock.b 0 (BcGhostFock.b 0 w) = 0 at car
    have twice : (2 : ℂ) • BcGhostFock.b 0 (BcGhostFock.b 0 w) = 0 := by
      simpa only [two_smul] using car
    exact (smul_eq_zero.mp twice).resolve_left (by norm_num)
  have square : B0 D * B0 D = 0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [B0, ghostB, Module.End.mul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.zero_apply, ghostSquare, TensorProduct.tmul_zero]
  exact LinearMap.congr_fun square x

private theorem totalL0_B0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) :
    totalL0 D H (B0 D x) = B0 D (totalL0 D H x) := by
  have first := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) (B0 D x)
  have second := congrArg (B0 D)
    (LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) x)
  change totalCharge D H (B0 D (B0 D x)) +
    B0 D (totalCharge D H (B0 D x)) = totalL0 D H (B0 D x) at first
  change B0 D (totalCharge D H (B0 D x) + B0 D (totalCharge D H x)) =
    B0 D (totalL0 D H x) at second
  rw [B0_square D, map_zero, zero_add] at first
  rw [map_add, B0_square D, add_zero] at second
  exact first.symm.trans second

/-- Raw B0 is only applied after the actual zero-energy cycle projection. -/
theorem B0_P0_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : totalCharge D H x = 0) :
    totalCharge D H (B0 D (P0 D x)) = 0 := by
  have ward := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) (P0 D x)
  change totalCharge D H (B0 D (P0 D x)) + B0 D (totalCharge D H (P0 D x)) =
    totalL0 D H (P0 D x) at ward
  simpa only [P0_cycle D H h26 hHG hGH x hx, map_zero, add_zero,
    totalL0_P0 D H hHG hGH] using ward

private theorem reduced_boundary_primitive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (preimage : State D) :
    totalCharge D H (-(B0 D (P0 D preimage))) =
      B0 D (P0 D (totalCharge D H preimage)) := by
  have ward := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) (P0 D preimage)
  change totalCharge D H (B0 D (P0 D preimage)) +
    B0 D (totalCharge D H (P0 D preimage)) = totalL0 D H (P0 D preimage) at ward
  have commutes := LinearMap.congr_fun (P0_commutes D H h26 hHG hGH) preimage
  change P0 D (totalCharge D H preimage) = totalCharge D H (P0 D preimage) at commutes
  rw [← commutes, totalL0_P0 D H hHG hGH] at ward
  rw [map_neg]
  exact (neg_eq_iff_add_eq_zero).mpr ward

/-- A true boundary for the output difference, with the explicit historical primitive.
No cycle/homogeneity premise is needed for this identity on full states. -/
theorem B0_P0_representative_change (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y preimage : State D) (boundary : totalCharge D H preimage = x - y) :
    totalCharge D H (-(B0 D (P0 D preimage))) = B0 D (P0 D x) - B0 D (P0 D y) := by
  rw [reduced_boundary_primitive D H h26 hHG hGH, boundary, map_sub, map_sub]

def cycleP0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (cycles D H) :=
  ((P0 D).comp (cycles D H).subtype).codRestrict (cycles D H)
    (fun x => P0_cycle D H h26 hHG hGH x x.property)

/-- In the supplied full quotient, projection changes no cohomology class. -/
theorem classOf_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : cycles D H) :
    classOf D H h26 hHG hGH (cycleP0 D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH x := by
  apply (Submodule.Quotient.eq (boundaries D H h26 hHG hGH)).mpr
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-(h D (x : State D)), ?_⟩
  change totalCharge D H (-(h D (x : State D))) =
    P0 D (x : State D) - (x : State D)
  simpa only [map_neg, neg_sub] using
    congrArg (fun z : State D => -z)
      (cycle_reduction D H h26 hHG hGH x x.property).symm

def cycleDelta (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (cycles D H) :=
  (((B0 D).comp (P0 D)).comp (cycles D H).subtype).codRestrict (cycles D H)
    (fun x => B0_P0_cycle D H h26 hHG hGH x x.property)

private theorem cycleDelta_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : cycles D H) (hx : x ∈ boundaries D H h26 hHG hGH) :
    cycleDelta D H h26 hHG hGH x ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨preimage, equation⟩ :=
    (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH x).mp hx
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-(B0 D (P0 D preimage)), ?_⟩
  change totalCharge D H (-(B0 D (P0 D preimage))) =
    B0 D (P0 D (x : State D))
  have primitive := B0_P0_representative_change D H h26 hHG hGH x 0 preimage
    (by simpa only [sub_zero] using equation)
  simpa only [map_zero, sub_zero] using primitive

/-- The P0-reduced physical B0 on the EXISTING full original cohomology quotient. -/
def Delta (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mapQ (boundaries D H h26 hHG hGH)
    (cycleDelta D H h26 hHG hGH) (cycleDelta_boundary D H h26 hHG hGH)

/-- The live endpoint for EVERY actual cycle, including mixed charges and energies.
The proof also consumes the genuine full-quotient zero-energy reduction. -/
@[simp] theorem Delta_classOf (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (x : cycles D H) :
    Delta D H h26 hHG hGH (classOf D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH
        ⟨ghostB D 0 (P0 D (x : State D)), B0_P0_cycle D H h26 hHG hGH x x.property⟩ := by
  change Delta D H h26 hHG hGH (classOf D H h26 hHG hGH x) =
    classOf D H h26 hHG hGH (cycleDelta D H h26 hHG hGH x)
  calc
    _ = Delta D H h26 hHG hGH
        (classOf D H h26 hHG hGH (cycleP0 D H h26 hHG hGH x)) := by
      rw [classOf_P0 D H h26 hHG hGH]
    _ = classOf D H h26 hHG hGH
        (cycleDelta D H h26 hHG hGH (cycleP0 D H h26 hHG hGH x)) := rfl
    _ = _ := by
      apply congrArg (classOf D H h26 hHG hGH)
      apply Subtype.ext
      change B0 D (P0 D (P0 D (x : State D))) = B0 D (P0 D (x : State D))
      rw [P0_idempotent D H hHG hGH]

/-- Square-zero of the actual quotient operator, with no BV/product assertion. -/
theorem Delta_square (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (Delta D H h26 hHG hGH a) = 0 := by
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH a
  rw [Delta_classOf, Delta_classOf]
  change classOf D H h26 hHG hGH
    (cycleDelta D H h26 hHG hGH (cycleDelta D H h26 hHG hGH x)) = 0
  have fixed : P0 D (B0 D (P0 D (x : State D))) = B0 D (P0 D (x : State D)) := by
    apply (P0_fixed_iff D H hHG hGH _).mpr
    rw [totalL0_B0 D H, totalL0_P0 D H hHG hGH, map_zero]
  have vanished : cycleDelta D H h26 hHG hGH (cycleDelta D H h26 hHG hGH x) = 0 := by
    apply Subtype.ext
    change B0 D (P0 D (B0 D (P0 D (x : State D)))) = 0
    rw [fixed, B0_square D]
  rw [vanished, map_zero]

end
end D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction
