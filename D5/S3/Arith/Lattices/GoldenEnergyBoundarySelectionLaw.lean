/- GID: D5/S3/Arith/Lattices/GoldenEnergyBoundarySelectionLaw
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/GoldenEnergyBoundarySelectionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden prime classes and ramification govern the lattice energy boundary. -/

import D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection

namespace D5.S3.Arith.Lattices.GoldenEnergyBoundarySelectionLaw

open D5.S0.Carrier
open D5.S3.Arith.GoldenPrimeSplitting
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open D5.S3.Arith.Lattices.EnergyBoundarySelectionLaw
open D5.S3.Arith.Lattices.RamifiedFiveBoundarySelection
open D5.S3.PrimeForms.GoldenPrimeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- **Golden energy-boundary selection law.** Lattice energy modulo five determines the
boundary quadratic type. Rational primes split or remain inert in the golden integers
according to their residue modulo five, while five is the unique ramified prime and is the
modulus used by the boundary law. -/
theorem golden_energy_boundary_selection_law :
    (forall x : LatticeIndex -> Int,
      boundaryQuadratic (boundaryProjection x) = 2 * latticeEnergyModFive x) ∧
    (forall x y : LatticeIndex -> Int,
      latticeEnergyModFive x = latticeEnergyModFive y ->
        boundaryQuadratic (boundaryProjection x) =
          boundaryQuadratic (boundaryProjection y)) ∧
    (forall p : Nat, p.Prime ->
      ((p % 5 = 1 ∨ p % 5 = 4) -> ¬ Prime (p : GoldenInt)) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) -> Prime (p : GoldenInt))) ∧
    ((5 : GoldenInt) = (-1 + 2 * phi) ^ 2 ∧ ¬ Prime (5 : GoldenInt)) ∧
    (forall p : Nat, p.Prime -> (legendreSym 5 p = 0 ↔ p = 5)) := by
  have hramified := ramified_five_boundary_selection
  refine ⟨hramified.2.2.2, ?_, ?_, ?_, hramified.2.2.1⟩
  · intro x y henergy
    rw [hramified.2.2.2 x, hramified.2.2.2 y, henergy]
  · intro p hp
    constructor
    · intro hsplit
      have hpNotFive : p ≠ 5 := by
        intro hpFive
        subst p
        norm_num at hsplit
      exact (golden_not_prime_iff_mod_five_eq_one_or_four hp hpNotFive).2 hsplit
    · intro hinert
      have hpNotFive : p ≠ 5 := by
        intro hpFive
        subst p
        norm_num at hinert
      exact (golden_prime_iff_mod_five_eq_two_or_three hp hpNotFive).2 hinert
  · exact ⟨hramified.2.1, golden_five_not_prime⟩

#print axioms golden_energy_boundary_selection_law

end D5.S3.Arith.Lattices.GoldenEnergyBoundarySelectionLaw
