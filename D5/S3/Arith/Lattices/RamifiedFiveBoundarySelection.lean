/- GID: D5/S3/Arith/Lattices/RamifiedFiveBoundarySelection
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/RamifiedFiveBoundarySelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five is the unique ramified prime and the canonical lattice boundary modulus. -/

import D5.S0.Carrier.GoldenDiscriminant
import D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw
import D5.S3.PrimeForms.GoldenPrimeClassification

namespace D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection

open D5.S0.Carrier
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- **Ramified-five boundary selection.** The golden polynomial has discriminant five,
five is a square of its ramifying golden integer, and the associated quadratic character
vanishes at no other rational prime. The canonical mod-five lattice boundary therefore uses
the same unique prime and carries lattice energy to twice its residue. -/
theorem ramified_five_boundary_selection :
    ((-1 : Int) ^ 2 - 4 * 1 * (-1) = 5) ∧
      (5 : GoldenInt) = (-1 + 2 * phi) ^ 2 ∧
      (∀ p : Nat, p.Prime → (legendreSym 5 p = 0 ↔ p = 5)) ∧
      ∀ x : LatticeIndex → Int,
        boundaryQuadratic (boundaryProjection x) =
          2 * latticeEnergyModFive x := by
  refine ⟨golden_discriminant_spec.1, ?_, ?_, energy_boundary_selection_law⟩
  · rw [D5.S3.PrimeForms.GoldenPrimeClassification.golden_five_eq_ramified_square]
    congr 1
  · intro p hp
    rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro hdiv
      have hnat : 5 ∣ p := by
        exact_mod_cast hdiv
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hnat).symm
    · intro hfive
      subst p
      norm_num

#print axioms ramified_five_boundary_selection

end D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection
