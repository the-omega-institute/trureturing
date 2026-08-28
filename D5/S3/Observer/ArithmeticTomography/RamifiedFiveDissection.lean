/- GID: D5/S3/Observer/ArithmeticTomography/RamifiedFiveDissection
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/RamifiedFiveDissection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete Lambda-square A4 five-dissection with a ramified jet channel. -/

import D5.S3.Arith.GoldenPrimeSplitting
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.RamifiedFiveDissection

open D5.S0.Carrier

/-- The source's coordinate realization of the lattice `Lambda^2 A4` in its fixed
six-vector basis. -/
@[ext]
structure ExteriorSquareA4 where
  coordinates : Fin 6 -> Int
  deriving DecidableEq

/-- The Gram matrix `G` displayed for `Lambda^2 A4` in source section 68. -/
def exteriorSquareA4Gram : Matrix (Fin 6) (Fin 6) Int :=
  !![3, 1, 1, -1, -1, 0;
     1, 3, 1, 1, 0, -1;
     1, 1, 3, 0, 1, 1;
     -1, 1, 0, 3, 1, -1;
     -1, 0, 1, 1, 3, 1;
     0, -1, 1, -1, 1, 3]

/-- The source energy `x^T G x` on the concrete `Lambda^2 A4` lattice. -/
def latticeEnergy (x : ExteriorSquareA4) : Int :=
  ∑ i, x.coordinates i * ∑ j, exteriorSquareA4Gram i j * x.coordinates j

/-- The three-dimensional boundary carrier over the ramified residue field. -/
abbrev RamifiedBoundary := Fin 3 -> ZMod 5

/-- The fixed matrix `R_5` of the source boundary map. -/
def rhoFiveMatrix : Matrix (Fin 3) (Fin 6) (ZMod 5) :=
  !![1, 0, 4, 0, 1, 0;
     0, 1, 4, 0, 0, 1;
     0, 0, 0, 1, 4, 1]

/-- The source's fixed boundary map `rho_5 : Lambda^2 A4 -> F_5^3`. -/
def rho5 (x : ExteriorSquareA4) : RamifiedBoundary := fun i =>
  ∑ j, rhoFiveMatrix i j * (x.coordinates j : ZMod 5)

/-- The symmetric matrix `H` used by the source boundary quadratic form. -/
def ramifiedFormMatrix : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![1, 2, 3; 2, 1, 2; 3, 2, 1]

/-- The source quadratic form `q_R(v) = v^T H v`. -/
def qR (v : RamifiedBoundary) : ZMod 5 :=
  ∑ i, v i * ∑ j, ramifiedFormMatrix i j * v j

/-- The fixed energy residue of a lattice point modulo five. -/
def energyResidue (x : ExteriorSquareA4) : ZMod 5 :=
  (latticeEnergy x : ZMod 5)

/-- Five ordinary energy residues together with one extra ramification channel. -/
inductive RamifiedFiveState where
  | ordinary (residue : Fin 5)
  | ramificationResidual
  deriving DecidableEq, Fintype

/-- The ordinary energy residue, represented in `Fin 5`. -/
def ordinaryResidue (x : ExteriorSquareA4) : Fin 5 :=
  ⟨(energyResidue x).val, ZMod.val_lt _⟩

/-- A point of the fixed coordinate lattice. -/
def latticePoint (coordinates : Fin 6 -> Int) : ExteriorSquareA4 :=
  ⟨coordinates⟩

/-- Concrete representatives of the five ordinary observable states. -/
def ordinaryWitness : Fin 5 -> ExteriorSquareA4 :=
  ![latticePoint ![0, 0, 0, 0, 0, 0],
    latticePoint ![-1, 0, 0, 0, 0, -1],
    latticePoint ![-1, -1, 1, 0, 0, 0],
    latticePoint ![-1, 0, 0, 0, 0, 0],
    latticePoint ![-1, 0, 0, -1, 0, 0]]

/-- The zero lattice point occupying the ordinary zero-boundary state. -/
def zeroWitness : ExteriorSquareA4 := ordinaryWitness 0

/-- The fixed lattice point representing the nonzero isotropic `R_5` branch. -/
def residualWitness : ExteriorSquareA4 :=
  latticePoint ![-1, 0, 0, -1, 0, -1]

/-- The six-state observer label attached to the source's fixed energy and boundary maps. -/
def stateOf (x : ExteriorSquareA4) : RamifiedFiveState :=
  if hEnergy : energyResidue x = 0 then
    if hBoundary : rho5 x = 0 then
      .ordinary ⟨0, by norm_num⟩
    else if hIsotropic : qR (rho5 x) = 0 then
      .ramificationResidual
    else
      .ordinary ⟨0, by norm_num⟩
  else
    .ordinary (ordinaryResidue x)

/-- The six labels are exactly the five ordinary residues plus one residual label. -/
theorem ramified_state_card : Fintype.card RamifiedFiveState = 6 := by
  decide

private theorem stateOf_ordinaryWitness (r : Fin 5) :
    stateOf (ordinaryWitness r) = .ordinary r := by
  fin_cases r <;> decide

private theorem stateOf_residualWitness :
    stateOf residualWitness = .ramificationResidual := by
  decide

private theorem stateOf_surjective : Function.Surjective stateOf := by
  intro state
  cases state with
  | ordinary r => exact ⟨ordinaryWitness r, stateOf_ordinaryWitness r⟩
  | ramificationResidual => exact ⟨residualWitness, stateOf_residualWitness⟩

/-- Square roots of five in the concrete golden integer ring. Membership carries the
ramification certificate rather than accepting it as a theorem premise. -/
def RamifiedFiveRoot :=
  {root : GoldenInt // (5 : GoldenInt) = root ^ 2}

/-- The source ramifying element `-1 + 2 phi`, using the repository's exact certificate. -/
def ramifiedFiveRoot : RamifiedFiveRoot :=
  ⟨⟨-1, 2⟩, D5.S3.Arith.GoldenPrimeSplitting.golden_five_eq_ramified_square⟩

/-- The ideal `(5)` defining the first-order ramified fiber. -/
def goldenFiveIdeal : Ideal GoldenInt :=
  Ideal.span {(5 : GoldenInt)}

/-- Since `5 = ramifiedFiveRoot^2`, this quotient is the first-order neighborhood
of the ramified golden prime. -/
abbrev GoldenFirstOrderNeighborhoodAtFive :=
  GoldenInt ⧸ goldenFiveIdeal

/-- The first-order jet left by a certified ramifying square root of five. -/
def firstOrderJetAtFive (root : RamifiedFiveRoot) :
    GoldenFirstOrderNeighborhoodAtFive :=
  Ideal.Quotient.mk goldenFiveIdeal root.1

theorem ramified_five_first_order_jet_ne_zero :
    firstOrderJetAtFive ramifiedFiveRoot ≠ 0 := by
  intro hZero
  change Ideal.Quotient.mk goldenFiveIdeal ramifiedFiveRoot.1 = 0 at hZero
  have hMem : ramifiedFiveRoot.1 ∈ goldenFiveIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hZero
  rw [goldenFiveIdeal, Ideal.mem_span_singleton] at hMem
  rcases hMem with ⟨y, hy⟩
  have hb := congrArg GoldenInt.b hy
  have hRootB : ramifiedFiveRoot.1.b = 2 := rfl
  have hFiveA : (5 : GoldenInt).a = 5 := rfl
  have hFiveB : (5 : GoldenInt).b = 0 := rfl
  rw [hRootB, b_mul, hFiveA, hFiveB] at hb
  omega

/-- Ordinary states have zero first-order jet; the residual state retains the
nonzero jet of the certified ramifying root. -/
def firstOrderJetObservation : RamifiedFiveState ->
    GoldenFirstOrderNeighborhoodAtFive
  | .ordinary _ => 0
  | .ramificationResidual => firstOrderJetAtFive ramifiedFiveRoot

/--
The concrete ramified five-dissection observes all six labels of `Lambda^2 A4`.
Its ordinary branch records the energy residue, the two fixed witnesses occupy
the two isotropic zero-residue branches, and the last clause
identifies their separation with the nonzero first-order jet of the ramified
golden prime.
-/
theorem six_state_ramified_five_dissection :
    (Set.range stateOf).ncard = Fintype.card RamifiedFiveState ∧
      (∀ x : ExteriorSquareA4, energyResidue x ≠ 0 ->
        stateOf x = .ordinary (ordinaryResidue x)) ∧
      rho5 zeroWitness = 0 ∧
      rho5 residualWitness ≠ 0 ∧
      qR (rho5 residualWitness) = 0 ∧
      stateOf zeroWitness ≠ stateOf residualWitness ∧
      firstOrderJetObservation .ramificationResidual ∉
        Set.range (fun r : Fin 5 => firstOrderJetObservation (.ordinary r)) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · rw [stateOf_surjective.range_eq]
    simp [Nat.card_eq_fintype_card]
  · intro x hx
    simp [stateOf, hx]
  · intro hRange
    rcases hRange with ⟨r, hEq⟩
    apply ramified_five_first_order_jet_ne_zero
    simpa [firstOrderJetObservation] using hEq.symm

/- Reverse probe for A1: the public cardinality equality forces full observability. -/
example : Set.range stateOf = Set.univ := by
  apply (Set.eq_univ_iff_ncard _).2
  simpa [Nat.card_eq_fintype_card] using
    six_state_ramified_five_dissection.1

/- Reverse probe for A6: the public theorem separates the fixed zero and residual points. -/
example : stateOf zeroWitness ≠ stateOf residualWitness := by
  exact six_state_ramified_five_dissection.2.2.2.2.2.1

/- Reverse probe for A7: jet separation implies the old constructor-level separation. -/
example : RamifiedFiveState.ramificationResidual ∉
    Set.range (fun r : Fin 5 => RamifiedFiveState.ordinary r) := by
  intro hRange
  rcases hRange with ⟨r, hEq⟩
  apply six_state_ramified_five_dissection.2.2.2.2.2.2
  exact ⟨r, congrArg firstOrderJetObservation hEq⟩

/- Trivialization probe for A7: a zero jet makes the public separation false. -/
example (hZero : firstOrderJetAtFive ramifiedFiveRoot = 0) :
    ¬firstOrderJetObservation .ramificationResidual ∉
      Set.range (fun r : Fin 5 => firstOrderJetObservation (.ordinary r)) := by
  intro hOutside
  apply hOutside
  refine ⟨0, ?_⟩
  simp [firstOrderJetObservation, hZero]

#print axioms six_state_ramified_five_dissection

end D5.S3.Observer.ArithmeticTomography.RamifiedFiveDissection
