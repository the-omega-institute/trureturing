/-
SOURCE-ONLY zero-energy parity consumer for the actual full lattice/ghost
carrier.  The basis, P0/B0 reduction, raw antighost, and quotient interfaces
are the fixed snapshots named by zero-energy-parity-inputs.json.  This module
adds no quotient, product, or BV construction and has not been kernel checked.

The parity calculation is on every charge, oscillator, and ghost occupation
label.  The energy is the raw BcGhostRelativeEnergy.energy convention supplied
by LatticeBRSTZeroEnergyReduction.  Historical/source attribution is retained:
Bakalov--Kac for the lattice realization, Scott Carnahan's vertexAlg supplier,
the original CountableOccupationFock/BcGhost construction, and Mathlib's
linear-algebra and quotient machinery.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostAntighostSecondOrder
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyLaws
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator Classical

namespace D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyParity

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State matterMode ghostB ghostVirasoro)
open LatticeMatterGhostStateField (Y stateField_parity)
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction
  (FullLabel fullBasis energyWeight P0 B0 totalL0 totalL0_P0 P0_fixed_iff
    cycleP0 classOf_P0 Delta Delta_classOf)
open D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
  (Cohomology cycles classOf classOf_surjective homogeneous_cycle_lift
    parity_classOf vacuum)
open private fullBasis_apply energyWeight_basis from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section

/-- The actual parity is diagonal on the complete charge/oscillator/occupation
basis; its eigenvalue sees exactly the ghost occupation cardinality. -/
theorem parity_fullBasis (D : LatticeData) (label : FullLabel D) :
    LatticeMatterGhostStateField.parity D (fullBasis D label) =
      (-1 : ℂ) ^ label.2.card • fullBasis D label := by
  rw [fullBasis_apply]
  simp only [LatticeMatterGhostStateField.parity, TensorProduct.map_tmul,
    LinearMap.id_apply, parity_ket, TensorProduct.tmul_smul]

/-- Every diagonal energy weight commutes with the literal state parity. -/
theorem energyWeight_parity_commutes (D : LatticeData) (weight : ℤ → ℂ) :
    energyWeight D weight * LatticeMatterGhostStateField.parity D =
      LatticeMatterGhostStateField.parity D * energyWeight D weight := by
  classical
  apply (fullBasis D).ext
  intro label
  change energyWeight D weight
      (LatticeMatterGhostStateField.parity D (fullBasis D label)) =
    LatticeMatterGhostStateField.parity D
      (energyWeight D weight (fullBasis D label))
  simp only [parity_fullBasis, energyWeight_basis, map_smul, smul_smul]
  rw [mul_comm]

/-- The actual zero-energy projector commutes with the actual ghost parity. -/
theorem P0_parity_commutes (D : LatticeData) :
    P0 D * LatticeMatterGhostStateField.parity D =
      LatticeMatterGhostStateField.parity D * P0 D := by
  exact energyWeight_parity_commutes D (fun energy => if energy = 0 then 1 else 0)

/-- Every parity eigenclass of the supplied full quotient has a representative
in the actual total-L0 kernel, with the same class and the same parity. -/
theorem homogeneous_zero_energy_cycle_lift
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (u : Cohomology D H h26 hHG hGH) (p : ℕ)
    (hu : D5.S3.VertexAlgebra.LatticeBRSTCohomologyField.parity
      D H h26 hHG hGH u = (-1 : ℂ)^p • u) :
    ∃ x : cycles D H,
      classOf D H h26 hHG hGH x = u ∧
      D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyReduction.totalL0 D H
          (x : State D) = 0 ∧
      LatticeMatterGhostStateField.parity D (x : State D) =
        (-1 : ℂ)^p • (x : State D) := by
  obtain ⟨x, hx, hpar⟩ := homogeneous_cycle_lift D H h26 hHG hGH u p hu
  refine ⟨cycleP0 D H h26 hHG hGH x, ?_, ?_, ?_⟩
  · exact (classOf_P0 D H h26 hHG hGH x).trans hx
  · change totalL0 D H (P0 D (x : State D)) = 0
    exact totalL0_P0 D H hHG hGH (x : State D)
  · change LatticeMatterGhostStateField.parity D (P0 D (x : State D)) =
      (-1 : ℂ)^p • P0 D (x : State D)
    have commute := LinearMap.congr_fun (P0_parity_commutes D) (x : State D)
    change P0 D (LatticeMatterGhostStateField.parity D (x : State D)) =
      LatticeMatterGhostStateField.parity D (P0 D (x : State D)) at commute
    rw [hpar, map_smul] at commute
    exact commute.symm

/-- The actual physical B0 is odd for the literal state parity.  The proof uses
its beta-state mode-one normalization and the actual state-field parity law. -/
theorem B0_parity_anticommutes (D : LatticeData) :
    B0 D * LatticeMatterGhostStateField.parity D +
      LatticeMatterGhostStateField.parity D * B0 D = 0 := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (stateField_parity D
    (D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta D) 1) x
  change LatticeMatterGhostStateField.parity D (((Y D
      (D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta D))[[1]]) x) =
    ((Y D (LatticeMatterGhostStateField.parity D
      (D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta D))[[1]])
        (LatticeMatterGhostStateField.parity D x)) at h
  rw [D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta_odd D] at h
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply,
    D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta_mode_one] at h
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  change B0 D (LatticeMatterGhostStateField.parity D x) +
      LatticeMatterGhostStateField.parity D (B0 D x) = 0
  rw [h, add_neg_cancel]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 4000000 in
/-- The induced Delta on the existing full quotient is odd for quotient parity,
with no descent law assumed: both sides are reduced to the same actual cycle
representatives using Delta_classOf, parity_classOf, classOf_surjective, the
P0/parity commutation, and the raw B0 anticommutation. -/
theorem Delta_parity_odd
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (u : Cohomology D H h26 hHG hGH) :
    D5.S3.VertexAlgebra.LatticeBRSTCohomologyField.parity
      D H h26 hHG hGH (Delta D H h26 hHG hGH u) =
      -(Delta D H h26 hHG hGH
        (D5.S3.VertexAlgebra.LatticeBRSTCohomologyField.parity
          D H h26 hHG hGH u)) := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH u
  rw [Delta_classOf, parity_classOf, parity_classOf, Delta_classOf]
  rw [← map_neg]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D
      (B0 D (P0 D (x : State D))) =
    -(B0 D (P0 D (LatticeMatterGhostStateField.parity D (x : State D))))
  have hB := LinearMap.congr_fun (B0_parity_anticommutes D)
    (P0 D (x : State D))
  change B0 D (LatticeMatterGhostStateField.parity D (P0 D (x : State D))) +
      LatticeMatterGhostStateField.parity D (B0 D (P0 D (x : State D))) = 0 at hB
  have hB' : -(B0 D (LatticeMatterGhostStateField.parity D
      (P0 D (x : State D)))) =
      LatticeMatterGhostStateField.parity D (B0 D (P0 D (x : State D))) :=
    (neg_eq_iff_add_eq_zero.mpr hB)
  have hP := LinearMap.congr_fun (P0_parity_commutes D) (x : State D)
  change P0 D (LatticeMatterGhostStateField.parity D (x : State D)) =
      LatticeMatterGhostStateField.parity D (P0 D (x : State D)) at hP
  calc
    LatticeMatterGhostStateField.parity D (B0 D (P0 D (x : State D))) =
        -(B0 D (LatticeMatterGhostStateField.parity D
          (P0 D (x : State D)))) := hB'.symm
    _ = -(B0 D (P0 D (LatticeMatterGhostStateField.parity D
      (x : State D)))) := by rw [← hP]

/-- The actual quotient vacuum is Delta-closed.  Its zero-energy statement is
obtained from the current conformal mode and its B0 statement from beta-mode
creation, so no vacuum normalization is assumed. -/
theorem Delta_vacuum
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    Delta D H h26 hHG hGH (vacuum D H h26 hHG hGH) = 0 := by
  have hL0 : totalL0 D H
      (LatticeMatterGhostStateField.vacuum D) = 0 := by
    change (matterMode D H 0 + ghostVirasoro D 0)
      (LatticeMatterGhostStateField.vacuum D) = 0
    rw [← LatticeMatterGhostStateField.conformal_modes D H 0]
    exact (LatticeMatterGhostStateField.stateField_vacuum_creation D).2.2.1
      (LatticeMatterGhostStateField.omega D H) 1 (by omega)
  have hP0 : P0 D (LatticeMatterGhostStateField.vacuum D) =
      LatticeMatterGhostStateField.vacuum D :=
    (P0_fixed_iff D H hHG hGH _).mpr hL0
  have hB0 : B0 D (LatticeMatterGhostStateField.vacuum D) = 0 := by
    have h := (LatticeMatterGhostStateField.stateField_vacuum_creation D).2.2.1
      (D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta D) 1 (by omega)
    rw [D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder.beta_mode_one D] at h
    exact h
  rw [vacuum, Delta_classOf]
  change classOf D H h26 hHG hGH
      ⟨B0 D (P0 D (LatticeMatterGhostStateField.vacuum D)), _⟩ = 0
  apply (LatticeBRSTCohomologyField.classOf_eq_zero D H h26 hHG hGH _).mpr
  refine ⟨0, ?_⟩
  have hzero : B0 D (P0 D (LatticeMatterGhostStateField.vacuum D)) = 0 := by
    rw [hP0]
    exact hB0
  simpa only [map_zero] using hzero.symm

end
end D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyParity
