/- GID: D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite four-current cycle traces and the bounded labeled partial-matching coefficient.
-/

import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator
open MvPolynomial

namespace D5.S3.VertexAlgebra.LatticeFourCurrentTrace
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter LatticeTwoCurrentTrace

abbrev Four := Fin 4

/-- The ten labeled partial matchings of four ordered slots. -/
inductive PM4 where
  | empty
  | p12 | p13 | p14 | p23 | p24 | p34
  | p12_34 | p13_24 | p14_23
  deriving DecidableEq, Fintype

private def e12 : Four × Four := (0, 1)
private def e13 : Four × Four := (0, 2)
private def e14 : Four × Four := (0, 3)
private def e23 : Four × Four := (1, 2)
private def e24 : Four × Four := (1, 3)
private def e34 : Four × Four := (2, 3)

/-- The labeled edge set of a partial matching. -/
def PM4.edges : PM4 → Finset (Four × Four)
  | .empty => ∅
  | .p12 => {e12}
  | .p13 => {e13}
  | .p14 => {e14}
  | .p23 => {e23}
  | .p24 => {e24}
  | .p34 => {e34}
  | .p12_34 => {e12, e34}
  | .p13_24 => {e13, e24}
  | .p14_23 => {e14, e23}

private abbrev edgeParam (M : PM4) := M.edges

private def PM4.unpaired (M : PM4) : Finset Four :=
  Finset.univ.filter fun j =>
    ∀ e ∈ M.edges, j ≠ e.1 ∧ j ≠ e.2

private def arcMem (e : Four × Four) (j : Four) : Prop :=
  e.1.1 < j.1 ∧ j.1 ≤ e.2.1

private def sideMem (ε : Fin 2) (e : Four × Four) (j : Four) : Prop :=
  if ε.1 = 0 then arcMem e j else ¬ arcMem e j

private def min4 (n : Four → ℕ) : ℕ :=
  min (min (n 0) (n 1)) (min (n 2) (n 3))

private def max4 (n : Four → ℕ) : ℕ :=
  max (max (n 0) (n 1)) (max (n 2) (n 3))

private def gradeShift (D : LatticeData) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (j : Four) : ℕ := by
  classical
  exact ∑ e : edgeParam M,
    (ell e).1 * ((k e).1 +
      if sideMem (ε e) e.1 j then 1 else 0)

/-- The literal finite trace of the original four current blocks. -/
def actualFourCurrentCycleTrace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) : ℂ := by
  letI := grade_finiteDimensional D hD (n 0 : ℤ)
  exact LinearMap.trace ℂ (grade D (n 0 : ℤ))
    ((actualCurrentBlock D (i 0) (n 0) (n 1)).comp
      ((actualCurrentBlock D (i 1) (n 1) (n 2)).comp
        ((actualCurrentBlock D (i 2) (n 2) (n 3)).comp
          (actualCurrentBlock D (i 3) (n 3) (n 0)))))

private def chargeWeight (D : LatticeData) (i : Four → Fin D.rank) (n : Four → ℕ)
    (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (t : Fin (min4 n + 1)) : ℂ := by
  classical
  exact if (∀ j : Four,
        n j = (chargeEnergy D β).toNat + t.1 +
          gradeShift D n β M ell ε k j) ∧
      (∀ e : edgeParam M, 0 < (ell e).1) then
    (Nat.card (IntegerFiber D t.1) : ℂ) *
      (∏ j ∈ M.unpaired, (bilinear D (unitCharge D (i j)) β : ℂ)) *
      ∏ e : edgeParam M,
        ((ell e).1 : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)
  else 0

/-- Explicit bounded ten-matching coefficient, with labeled repeated-frequency slots. -/
def boundedFourCurrentCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) : ℂ := by
  classical
  exact ∑ β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ),
    ∑ M : PM4,
      ∑ ell : edgeParam M → Fin (max4 n + 1),
        ∑ ε : edgeParam M → Fin 2,
          ∑ k : edgeParam M → Fin (min4 n + 1),
            ∑ t : Fin (min4 n + 1), chargeWeight D i n β M ell ε k t

/-- There are exactly ten labeled partial matchings; in particular the empty assignment is unique. -/
private theorem pm4_card : Fintype.card PM4 = 10 := by decide

private theorem pm4_empty_edges : PM4.empty.edges = ∅ := rfl

private theorem pm4_empty_unpaired : PM4.empty.unpaired = Finset.univ := by
  classical
  ext j
  simp [PM4.unpaired, PM4.edges]

private theorem projection_basis (D : LatticeData) (n : ℤ) (a : Label D)
    (ha : energy D a = n) : gradeProjection D n (carrierBasis D a) = carrierBasis D a := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext b
  rw [gradeProjection_coeff]
  change (if energy D b = n then Finsupp.single a (1 : ℂ) b else 0) =
    Finsupp.single a (1 : ℂ) b
  by_cases h : a = b
  · subst b
    simp [ha]
  · simp [Finsupp.single_apply, h]

private theorem basis_value (D : LatticeData) (n : ℤ) (a : EnergyFiber D n) :
    (gradeBasis D n a : Carrier D) = carrierBasis D a.1 := by
  run_tac
    let supplier := (Lean.Name.num
      `_private.D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades 0).append
      `D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades.gradeBasis_coe
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($(Lean.mkIdent supplier)) _ _ _))

private theorem block_zero_basis (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (a : EnergyFiber D (n : ℤ)) :
    actualCurrentBlock D i n n (gradeBasis D (n : ℤ) a) =
      (bilinear D (unitCharge D i) a.1.1 : ℂ) • gradeBasis D (n : ℤ) a := by
  apply Subtype.ext
  change gradeProjection D (n : ℤ) (((Y D (currentState D i))[[ (n : ℤ) - n ]])
    (gradeBasis D (n : ℤ) a)) = _
  rw [basis_value, current_state_field, neutralField_ncoeff, sub_self,
    carrierBasis_apply, neutralMode_single]
  simp only [neutralPolynomialMode, lt_self_iff_false, ↓reduceIte,
    LinearMap.smul_apply, LinearMap.id_apply, ← Finsupp.smul_single, map_smul]
  rw [← carrierBasis_apply, projection_basis D _ _ a.2]
  rw [Submodule.coe_smul, basis_value]

private theorem zero_diag (D : LatticeData) (n : ℕ) (i : Four → Fin D.rank)
    (a : EnergyFiber D (n : ℤ)) :
    (gradeBasis D (n : ℤ)).repr
      (((actualCurrentBlock D (i 0) n n).comp
        ((actualCurrentBlock D (i 1) n n).comp
          ((actualCurrentBlock D (i 2) n n).comp
            (actualCurrentBlock D (i 3) n n))))
        (gradeBasis D (n : ℤ) a)) a =
      ∏ j : Four, (bilinear D (unitCharge D (i j)) a.1.1 : ℂ) := by
  classical
  simp [LinearMap.comp_apply, block_zero_basis, map_smul, smul_eq_mul,
    Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm]
  ring

/-- The equal-grade specialization is the literal four zero-mode trace on the original basis.
This is the finite source bridge used by the full signed-mode induction. -/
private theorem actual_four_zero_grade_trace
    (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : ℕ) [Finite (EnergyFiber D (n : ℤ))] :
    letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
    actualFourCurrentCycleTrace D hD i (fun _ => n) =
      ∑ a : EnergyFiber D (n : ℤ),
        ∏ j : Four, (bilinear D (unitCharge D (i j)) a.1.1 : ℂ) := by
  classical
  letI := grade_finiteDimensional D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  rw [actualFourCurrentCycleTrace,
    LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D (n : ℤ))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, zero_diag]

end D5.S3.VertexAlgebra.LatticeFourCurrentTrace
