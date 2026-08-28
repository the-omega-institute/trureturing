/- GID: D5/S3/Arith/Lattices/RamifiedFiveDissection
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/RamifiedFiveDissection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five energy residues plus one nonzero isotropic zero-fiber state form six readouts. -/

/- Library-search audit trail (2026-08-28):
* Repository name, matrix, and body-shape searches found no existing boundary reduction,
  boundary quadratic form, ramification residual, or six-state image theorem. They did find the
  canonical `LatticeIndex` and `integralGramMatrix` in `ExactDualLatticeFormula`, which are
  imported here instead of being redeclared.
* Primitive-before-definition searches covered matrix-vector reduction over `ZMod 5`, quadratic
  dot products, paired Boolean readouts, and integer-coordinate reduction. No canonical D5
  primitive with one of these bodies exists.
* Pinned Mathlib supplies the exact `Matrix.mulVec`, `dotProduct`, `ZMod`, and finite set-cardinal
  infrastructure used below, but no theorem states this concrete ramified five-dissection.
-/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula
import Mathlib.Data.ZMod.Basic

namespace D5.S3.Arith.Lattices.RamifiedFiveDissection

open D5.S3.Arith.Lattices.ExactDualLatticeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Coordinate indices for the three-dimensional boundary space over `ZMod 5`. -/
abbrev BoundaryIndex := Fin 3

/-- The reduction modulo five of the source lattice's six integral coordinates. -/
abbrev ReducedCoordinates := LatticeIndex -> ZMod 5

/-- Coordinatewise reduction of an integral lattice vector modulo five. -/
def integerReduction (x : LatticeIndex -> Int) : ReducedCoordinates :=
  fun i => (x i : ZMod 5)

/-- The source's explicit three-by-six boundary matrix `R_5`. -/
def boundaryMatrix : Matrix BoundaryIndex LatticeIndex (ZMod 5) :=
  !![1, 0, 4, 0, 1, 0;
     0, 1, 4, 0, 0, 1;
     0, 0, 0, 1, 4, 1]

/-- The symmetric matrix defining the boundary quadratic form. -/
def boundaryQuadraticMatrix : Matrix BoundaryIndex BoundaryIndex (ZMod 5) :=
  !![1, 2, 3;
     2, 1, 2;
     3, 2, 1]

/-- The reduction map from six lattice coordinates to the three-dimensional boundary. -/
def boundaryReduction (x : ReducedCoordinates) : BoundaryIndex -> ZMod 5 :=
  Matrix.mulVec boundaryMatrix x

/-- The source quadratic form `q_R(v) = v^T H v`. -/
def boundaryQuadratic (v : BoundaryIndex -> ZMod 5) : ZMod 5 :=
  dotProduct v (Matrix.mulVec boundaryQuadraticMatrix v)

/-- The lattice energy computed with the canonical Gram matrix and reduced modulo five. -/
def energyResidue (x : ReducedCoordinates) : ZMod 5 :=
  dotProduct x
    (Matrix.mulVec
      (integralGramMatrix.map (Int.castRingHom (ZMod 5))) x)

/-- The additional bit is present exactly on the nonzero isotropic part of the zero fiber. -/
def ramificationResidual (x : ReducedCoordinates) : Bool :=
  decide (boundaryReduction x ≠ 0 ∧ boundaryQuadratic (boundaryReduction x) = 0)

/-- The ordinary energy residue paired with its source-derived ramification residual. -/
def ramifiedReadout (x : ReducedCoordinates) : ZMod 5 × Bool :=
  (energyResidue x, ramificationResidual x)

private theorem reduced_selection_law :
    ∀ x : ReducedCoordinates,
      boundaryQuadratic (boundaryReduction x) = 2 * energyResidue x := by
  intro x
  simp [boundaryQuadratic, boundaryReduction, boundaryQuadraticMatrix,
    boundaryMatrix, energyResidue, integralGramMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring_nf
  rw [show (24 : ZMod 5) = 4 by decide,
    show (26 : ZMod 5) = 1 by decide,
    show (10 : ZMod 5) = 0 by decide,
    show (6 : ZMod 5) = 1 by decide,
    show (184 : ZMod 5) = 4 by decide,
    show (64 : ZMod 5) = 4 by decide,
    show (40 : ZMod 5) = 0 by decide,
    show (96 : ZMod 5) = 1 by decide,
    show (20 : ZMod 5) = 0 by decide,
    show (34 : ZMod 5) = 4 by decide,
    show (14 : ZMod 5) = 4 by decide,
    show (41 : ZMod 5) = 1 by decide,
    show (4 : ZMod 5) = -1 by decide]
  ring

private theorem reduced_readout_classification :
    ∀ x : ReducedCoordinates,
      (∃ r : ZMod 5, ramifiedReadout x = (r, false)) ∨
        ramifiedReadout x = (0, true) := by
  intro x
  by_cases hResidual :
      boundaryReduction x ≠ 0 ∧ boundaryQuadratic (boundaryReduction x) = 0
  · right
    have hTwice : 2 * energyResidue x = 0 := by
      rw [← reduced_selection_law x, hResidual.2]
    have hEnergy : energyResidue x = 0 := by
      calc
        energyResidue x = 1 * energyResidue x := by simp
        _ = (3 * 2) * energyResidue x := by congr 1
        _ = 3 * (2 * energyResidue x) := by rw [mul_assoc]
        _ = 0 := by rw [hTwice, mul_zero]
    have hResidualBool : ramificationResidual x = true := by
      simp [ramificationResidual, hResidual]
    simp [ramifiedReadout, hResidualBool, hEnergy]
  · left
    have hResidualBool : ramificationResidual x = false := by
      simp [ramificationResidual, hResidual]
    exact ⟨energyResidue x, by simp [ramifiedReadout, hResidualBool]⟩

private theorem zmod_five_cases :
    ∀ r : ZMod 5, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by
  decide

private theorem reduced_ordinary_states :
    ∀ r : ZMod 5, ∃ x : ReducedCoordinates, ramifiedReadout x = (r, false) := by
  intro r
  rcases zmod_five_cases r with rfl | rfl | rfl | rfl | rfl
  · refine Exists.intro ![0, 0, 0, 0, 0, 0] ?_
    decide
  · refine Exists.intro ![3, 1, 0, 0, 0, 0] ?_
    decide
  · refine Exists.intro ![2, 0, 0, 0, 0, 0] ?_
    decide
  · refine Exists.intro ![1, 0, 0, 0, 0, 0] ?_
    decide
  · refine Exists.intro ![2, 1, 0, 0, 0, 0] ?_
    decide

private theorem reduced_residual_state :
    ∃ x : ReducedCoordinates, ramifiedReadout x = (0, true) := by
  refine Exists.intro ![2, 1, 0, 1, 0, 0] ?_
  decide

private theorem integer_reduction_surjective :
    Function.Surjective integerReduction := by
  intro x
  refine Exists.intro (fun i => (x i).val) ?_
  funext i
  exact ZMod.natCast_zmod_val (x i)

private theorem integer_readout_range_eq_reduced :
    Set.range (fun x : LatticeIndex -> Int => ramifiedReadout (integerReduction x)) =
      Set.range ramifiedReadout := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨integerReduction x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := integer_reduction_surjective x
    exact ⟨z, congrArg ramifiedReadout hz⟩

private theorem reduced_readout_range :
    Set.range ramifiedReadout =
      Set.range (fun r : ZMod 5 => (r, false)) ∪ {(0, true)} := by
  ext y
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rcases reduced_readout_classification x with ⟨r, hr⟩ | hr
    · exact Or.inl ⟨r, hr.symm⟩
    · exact Or.inr hr
  · rintro (⟨r, rfl⟩ | rfl)
    · obtain ⟨x, hx⟩ := reduced_ordinary_states r
      exact ⟨x, hx⟩
    · obtain ⟨x, hx⟩ := reduced_residual_state
      exact ⟨x, hx⟩

/- **Six-state ramified five-dissection.** The concrete boundary form obeys the selection law.
On the exact integral lattice carrier, its source-derived readout has precisely the five ordinary
energy residues with a false residual bit and one additional true residual state over zero. -/
theorem ramified_five_dissection :
    (∀ x : LatticeIndex -> Int,
      boundaryQuadratic (boundaryReduction (integerReduction x)) =
        2 * energyResidue (integerReduction x)) ∧
    Set.range (fun x : LatticeIndex -> Int => ramifiedReadout (integerReduction x)) =
      Set.range (fun r : ZMod 5 => (r, false)) ∪ {(0, true)} ∧
    (Set.range
      (fun x : LatticeIndex -> Int =>
        ramifiedReadout (integerReduction x))).ncard = 6 := by
  constructor
  · intro x
    exact reduced_selection_law (integerReduction x)
  constructor
  · exact integer_readout_range_eq_reduced.trans reduced_readout_range
  · rw [integer_readout_range_eq_reduced, reduced_readout_range]
    rw [Set.ncard_union_eq]
    · rw [Set.ncard_range_of_injective]
      · simp
      · intro a b h
        exact congrArg Prod.fst h
    · simp only [Set.disjoint_singleton_right, Set.mem_range, Prod.mk.injEq,
        Bool.false_eq_true, and_false, exists_false, not_false_eq_true]

-- The source's nonzero isotropic state is realized on the exact reduced lattice carrier.
example :
    boundaryReduction ![2, 1, 0, 1, 0, 0] ≠ 0 ∧
      boundaryQuadratic (boundaryReduction ![2, 1, 0, 1, 0, 0]) = 0 := by
  decide

#print axioms ramified_five_dissection

end D5.S3.Arith.Lattices.RamifiedFiveDissection
