/- GID: D5/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/ThreeQuarterCirculantConjecture24Refutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Refutes the literal degree-two quantifier of Conjecture 2.4 at k equals one. -/

import D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture24Refutation

/-
proof_shape: boundary_facts: content (the k=1 modular collision and surviving
  construction claims are explicit); result: content (the collision refutes claim)
escape_witness: the public conclusion is the one-neighbor counterexample to the
  source's degree-two graph condition
admission_basis: open-problem-resolution (preregistered issue #11225)
Direct frozen dependencies: none
-/

open D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture

/-- Conjecture 2.4 with the paper's set-of-arcs, degree-two digraph convention. -/
def claim : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    order k = k ^ 2 + 4 * k - 2 ∧
    (latticeFirst k).1 * (latticeSecond k).2 -
      (latticeSecond k).1 * (latticeFirst k).2 = (order k : ℤ) ∧
    integerKernel k = generatedLattice k ∧
    (∀ z : ZMod (order k), sector k k z) ∧
    ¬ sector k (k - 1) (k : ZMod (order k)) ∧
    ∀ z : ZMod (order k),
      ({z + 1, z + stepB k} : Finset (ZMod (order k))).card = 2

/-- The degenerate degree at `k=1` leaves the lattice and sector formulas intact. -/
theorem boundary_facts :
    order 1 = 3 ∧
    stepB 1 = (1 : ZMod (order 1)) ∧
    (∀ z : ZMod (order 1),
      ({z + 1, z + stepB 1} : Finset (ZMod (order 1))).card = 1) ∧
    (∀ z : ZMod (order 1), sector 1 1 z) ∧
    ¬ sector 1 0 (1 : ZMod (order 1)) ∧
    integerKernel 1 = generatedLattice 1 := by
  have hstep : stepB 1 = (1 : ZMod (order 1)) := by decide
  refine ⟨by decide, hstep, ?_, sector_cover 1 (by decide), ?_, ?_⟩
  · intro z
    simp [hstep]
  · simpa using sector_radius_lower 1 (by decide)
  · exact (kernel_eq_generated 1 (by decide)).2.2

/-- At `k=1`, the two displayed steps coincide modulo three, giving one arc from each
vertex. The sector and lattice assertions are separate and survive this boundary. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨_, _, _, _, _, hdegree⟩ := h 1 (by decide)
  have hsame : (1 : ZMod (order 1)) = stepB 1 := by decide
  have hcard :
      ({(0 : ZMod (order 1)) + 1, (0 : ZMod (order 1)) + stepB 1} :
        Finset (ZMod (order 1))).card = 1 := by
    rw [← hsame]
    simp
  have htwo := hdegree 0
  omega

end D5.S3.Arith.Covering.ThreeQuarterCirculantConjecture24Refutation
