/- GID: D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/RamifiedFiveDissection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Six-state 5-dissection with a nonzero isotropic residual channel. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * Repository searches found no existing OACTC declaration for the lattice map rho_5,
     the quadratic form q_R, or the six-state 5-dissection.
   * Pinned Mathlib supplies finite inductive cardinality and ZMod/matrix primitives, but
     no theorem packaging this dissection; the proof below uses those primitives directly.
   * The source objects and the energy congruence are the definitions and result in §§68,
     73, and 74 of OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.RamifiedFiveDissection

/-- The three-dimensional boundary carrier over the ramified residue field. -/
abbrev RamifiedBoundary := Fin 3 → ZMod 5

/-- The symmetric matrix H used by the source's boundary quadratic form q_R. -/
def ramifiedFormMatrix : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![1, 2, 3; 2, 1, 2; 3, 2, 1]

/-- The source quadratic form q_R(v) = vᵀHv, written with finite sums. -/
def qR (v : RamifiedBoundary) : ZMod 5 :=
  ∑ i, v i * ∑ j, ramifiedFormMatrix i j * v j

/-- Five ordinary energy residues together with one extra ramification channel. -/
inductive RamifiedFiveState where
  | ordinary (residue : Fin 5)
  | ramificationResidual
  deriving DecidableEq, Fintype

/-- The ordinary residue observation n mod 5, represented in Fin 5. -/
def ordinaryResidue (n : ℕ) : Fin 5 :=
  ⟨n % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Existing OACTC data: a lattice carrier, its energy, the fixed rho_5 map, the
energy-boundary congruence, and witnesses for the zero and nonzero isotropic branches.
The witnesses encode the nonempty O_0 and isotropic boundary orbits from source §73. -/
structure RamifiedFiveDissectionData where
  L : Type*
  energy : L → ℕ
  rho5 : L → RamifiedBoundary
  energy_boundary : ∀ x,
    qR (rho5 x) = (2 : ZMod 5) * ((energy x % 5 : ℕ) : ZMod 5)
  zeroWitness : L
  zero_energy_mod_five : energy zeroWitness % 5 = 0
  zero_boundary : rho5 zeroWitness = 0
  residualWitness : L
  residual_energy_mod_five : energy residualWitness % 5 = 0
  residual_boundary_ne_zero : rho5 residualWitness ≠ 0

/-- The six-state observer label attached to an energy/boundary pair. -/
def stateOf (d : RamifiedFiveDissectionData) (x : d.L) : RamifiedFiveState :=
  if hEnergy : d.energy x % 5 = 0 then
    if hBoundary : d.rho5 x = 0 then
      .ordinary ⟨0, by norm_num⟩
    else
      .ramificationResidual
  else
    .ordinary (ordinaryResidue (d.energy x))

/-- The six labels are exactly the five ordinary residues plus one residual label. -/
theorem ramified_state_card : Fintype.card RamifiedFiveState = 6 := by
  decide

/--
The ramified five-dissection has six observable states.  The ordinary branch records
the residue modulo five; at zero residue the supplied source witnesses occupy the
zero and nonzero isotropic branches, whose labels are distinct.  The final clause
records that the residual label is an additional channel rather than an ordinary
residue label.
-/
theorem six_state_ramified_five_dissection (d : RamifiedFiveDissectionData) :
    6 = 5 + 1 ∧
      (∀ x : d.L, d.energy x % 5 ≠ 0 →
        stateOf d x = .ordinary (ordinaryResidue (d.energy x))) ∧
      d.rho5 d.zeroWitness = 0 ∧
      d.rho5 d.residualWitness ≠ 0 ∧
      qR (d.rho5 d.residualWitness) = 0 ∧
      stateOf d d.zeroWitness ≠ stateOf d d.residualWitness ∧
      RamifiedFiveState.ramificationResidual ∉
        Set.range (fun r : Fin 5 => RamifiedFiveState.ordinary r) := by
  have hResidualIsotropic : qR (d.rho5 d.residualWitness) = 0 := by
    simpa [d.residual_energy_mod_five] using
      d.energy_boundary d.residualWitness
  refine ⟨by norm_num, ?_, d.zero_boundary, d.residual_boundary_ne_zero,
    hResidualIsotropic, ?_, ?_⟩
  · intro x hx
    simp [stateOf, hx]
  · intro hStates
    have hZero : stateOf d d.zeroWitness =
        .ordinary ⟨0, by norm_num⟩ := by
      simp [stateOf, d.zero_energy_mod_five, d.zero_boundary]
    have hResidual : stateOf d d.residualWitness =
        .ramificationResidual := by
      simp [stateOf, d.residual_energy_mod_five,
        d.residual_boundary_ne_zero]
    rw [hZero, hResidual] at hStates
    cases hStates
  · intro hRange
    rcases hRange with ⟨r, hEq⟩
    cases hEq

/- Reverse probe: the public theorem yields the nontrivial state separation. -/
example (d : RamifiedFiveDissectionData) :
    stateOf d d.zeroWitness ≠ stateOf d d.residualWitness := by
  exact (six_state_ramified_five_dissection d).2.2.2.2.2.1

/- Trivialization probe: a Unit boundary has no possible nonzero residual witness. -/
example (rho : Unit → Unit) (w : Unit) : ¬rho w ≠ () := by
  intro h
  exact h rfl

#print axioms six_state_ramified_five_dissection

end D5.S3.Observer.ArithmeticTomography.RamifiedFiveDissection
