/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalCharacter
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Actual finite monomial bases and the unsigned Euler24 character of original physical fibers. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality
import D5.S3.Combinatorics.Partitions.ColouredOccupation
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY UNCOMPILED. These bases use the sealed actual HPL coordinate
equivalence, whose domain is the signed level 1-chargeEnergy D p. They
remain bases at negative levels (the index is empty). The ambient module
is the literal physicalChargeFiber inside the original global Cohomology.
In particular no restriction of incoming ALL-State primitives is made.

The Euler series is the unsigned integer ledger with exponent 24. No
signed theta factor, perfectness premise, or all-charge finite-grade
assumption enters the construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

open private Poly Occ wt signedWeight signedWeight_cast levelSpace LevelIndex
  levelIndexFinite levelIndexFintype monomialAt level_expansion leftCoordinates from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalCharacter

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticePositiveEnergy
open LatticeSugawaraCurrents D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
open D5.S3.Combinatorics.Partitions.ColouredOccupation
open D5.S3.Combinatorics.Partitions.ColouredEulerLedger
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality (eulerSeries)
open MvPolynomial

attribute [local instance] levelIndexFinite levelIndexFintype

/-- Coefficients and their finite monomial sum are genuine inverse maps. -/
private def levelCoefficients (r : ℕ) (ell : ℤ) :
    levelSpace r ell ≃ₗ[ℂ] (LevelIndex r ell → ℂ) where
  toFun f a := f.val.coeff a.val
  invFun c := ∑ a : LevelIndex r ell, c a • monomialAt r ell a
  left_inv f := level_expansion r ell f
  right_inv c := by
    classical
    funext a
    change (∑ b : LevelIndex r ell, c b • monomialAt r ell b).val.coeff a.val = c a
    simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul]
    rw [Finset.sum_eq_single a]
    · simp [monomialAt]
    · intro b hb hba
      have hne : b.val ≠ a.val := fun h => hba (Subtype.ext h)
      simp [monomialAt, coeff_monomial, hne, Ne.symm hne]
    · simp
  map_add' f g := by
    funext a
    simp only [Submodule.coe_add, MvPolynomial.coeff_add, Pi.add_apply]
  map_smul' c f := by
    funext a
    simp only [Submodule.coe_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]

private def levelMonomialBasis (r : ℕ) (ell : ℤ) :
    Module.Basis (LevelIndex r ell) ℂ (levelSpace r ell) :=
  Module.Basis.ofEquivFun (levelCoefficients r ell)

private def levelIndexEquivPartition (r : ℕ) (ell : ℤ) (hell : 0 ≤ ell) :
    LevelIndex r ell ≃ ColouredPartition (fun _ => r) ell.toNat :=
  (show LevelIndex r ell ≃ OccupationFiber r ell.toNat from
    { toFun := fun a => ⟨a.val, by
        have ha := a.property
        rw [signedWeight_cast] at ha
        change (Finsupp.weight (fun x : Fin r × ℕ => x.2+1) a.val : ℤ) = ell at ha
        change Finsupp.weight (fun x : Fin r × ℕ => x.2+1) a.val = ell.toNat
        omega⟩
      invFun := fun a => ⟨a.val, by
        rw [signedWeight_cast]
        change (Finsupp.weight (fun x : Fin r × ℕ => x.2+1) a.val : ℤ) = ell
        have ha := a.property
        omega⟩
      left_inv a := rfl
      right_inv a := rfl }).trans (occupationPartitionEquiv r ell.toNat)

private def physicalIndexEquivPartition (D : LatticeData) (h26 : D.rank = 26)
    (ell : ℤ) (hell : 0 ≤ ell) :
    LevelIndex (D.rank-2) ell ≃ ColouredPartition (fun _ => 24) ell.toNat := by
  have hr : D.rank-2 = 24 := by omega
  simpa only [hr] using levelIndexEquivPartition (D.rank-2) ell hell

section OriginalPhysicalFiber

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1) (p : Charge D) (hp : p ≠ 0)

/-- The actual monomial basis, transported by the original HPL inclusion.
The signed exact-level index is finite, including when it is empty. -/
def physicalOccupationBasis :
    Module.Basis
      {d : (Fin (D.rank-2) × ℕ) →₀ ℕ //
        Finsupp.weight (fun x => (x.2 : ℤ)+1) d = 1-chargeEnergy D p}
      ℂ (physicalChargeFiber D H h26 hHG hGH p) :=
  (levelMonomialBasis (D.rank-2) (1-chargeEnergy D p)).map
    (leftCoordinates D H h26 hHG hGH p hp)

/- The actual basis has a finite index, so the physical fiber is finite-dimensional. -/
/-- The same basis, now indexed by actual 24-colour partitions, at every
nonnegative signed shell. This includes the empty partition at shell zero. -/
def physicalPartitionBasis (hell : 0 ≤ 1-chargeEnergy D p) :
    Module.Basis (ColouredPartition (fun _ => 24) (1-chargeEnergy D p).toNat)
      ℂ (physicalChargeFiber D H h26 hHG hGH p) :=
  (physicalOccupationBasis D H h26 hHG hGH p hp).reindex
    (physicalIndexEquivPartition D h26 (1-chargeEnergy D p) hell)

include hp in
/-- A negative oscillator shell makes the literal physical submodule zero;
this is a vanishing proof, not a default value of finrank. -/
theorem physicalChargeFiber_eq_bot_of_level_neg (hell : 1-chargeEnergy D p < 0) :
    physicalChargeFiber D H h26 hHG hGH p = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  let E := leftCoordinates D H h26 hHG hGH p hp
  have hf : E.symm ⟨x,hx⟩ = 0 := by
    rw [← level_expansion (D.rank-2) (1-chargeEnergy D p) (E.symm ⟨x,hx⟩)]
    apply Finset.sum_eq_zero
    intro a ha
    have he := a.property
    rw [signedWeight_cast] at he
    have hn : (0 : ℤ) ≤ (wt a.val : ℤ) := Int.natCast_nonneg _
    omega
  have hzero : (⟨x,hx⟩ : physicalChargeFiber D H h26 hHG hGH p) = 0 := by
    have h := congrArg E hf
    rw [E.apply_symm_apply, E.map_zero] at h
    exact h
  exact congrArg Subtype.val hzero

include hp in
/-- Exact unsigned physical root multiplicity at every nonzero original
charge. Both complex inverse-Gram equations and the original quotient
remain in the full telescope. -/
theorem physicalChargeFiber_character :
    (Module.finrank ℂ (physicalChargeFiber D H h26 hHG hGH p) : ℤ) =
      if 0 ≤ 1-chargeEnergy D p then
        PowerSeries.coeff (1-chargeEnergy D p).toNat
          (eulerSeries (fun _ => (24 : ℤ)))
      else 0 := by
  classical
  by_cases hell : 0 ≤ 1-chargeEnergy D p
  · rw [if_pos hell]
    have hc : PowerSeries.coeff (1-chargeEnergy D p).toNat
        (eulerSeries (fun _ => (24 : ℤ))) =
        (Nat.card (ColouredPartition (fun _ => 24) (1-chargeEnergy D p).toNat) : ℤ) := by
      simpa only [Nat.cast_ofNat] using
        coloured_coefficient (fun _ => 24) (1-chargeEnergy D p).toNat
    rw [hc]
    exact_mod_cast (Module.finrank_eq_nat_card_basis
      (physicalPartitionBasis D H h26 hHG hGH p hp hell))
  · rw [if_neg hell]
    have hbot := physicalChargeFiber_eq_bot_of_level_neg D H h26 hHG hGH p hp
      (by omega)
    letI : Subsingleton (physicalChargeFiber D H h26 hHG hGH p) := by
      rw [hbot]
      infer_instance
    have hz : Module.finrank ℂ (physicalChargeFiber D H h26 hHG hGH p) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact_mod_cast hz

end OriginalPhysicalFiber
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalCharacter
