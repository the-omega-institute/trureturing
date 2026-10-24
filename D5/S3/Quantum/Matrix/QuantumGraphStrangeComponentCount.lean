/- GID: D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quantum graph components equal graph components plus loop-free isolated strange edges. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Matrix.RecordCapacity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Matrix.Basis

/-! # The component count of diagonal-orthogonal quantum graphs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount

open scoped BigOperators
open _root_.Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The realigned projector, with the diagonal-coordinate block diagonal. -/
def realignedProjector {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q =>
    if p.1 = p.2 then
      if q = (p.1, p.1) then d p.1 else 0
    else if q = p then A p.1 p.2
    else if q = (p.2, p.1) then C p.1 p.2 else 0

/-- Realignment reads the first and third indices as output indices. -/
def adjacency {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : Mat n →ₗ[ℂ] Mat n where
  toFun Z i k := ∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * Z j l
  map_add' X Y := by
    ext i k
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by
    ext i k
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- A self-adjoint idempotent matrix. -/
def IsOrthogonalProjector {n : ℕ} (P : Mat n) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- Removing the diagonal gives the matrix governing undirectedness. -/
def offDiagonal {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => if i = j then 0 else A i j

/-- Nonzero projectors resolving the identity and separating left multiplication. -/
def HasComponents {n : ℕ} (G : Mat n →ₗ[ℂ] Mat n) (k : ℕ) : Prop :=
  ∃ P : Fin k → Mat n,
    (∀ s, IsOrthogonalProjector (P s) ∧ P s ≠ 0) ∧
    (∑ s, P s) = 1 ∧
    ∀ s t, s ≠ t → ∀ Z, P s * G (P t * Z) = 0

/-- The simple graph records exactly the nonzero off-diagonal two-by-two blocks. -/
def underlyingGraph {n : ℕ} (A C : Mat n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0 ∨ C i j ≠ 0 ∨ C j i ≠ 0)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨by intro i; simp⟩

/-- A two-vertex component whose strange edge has no loop at either endpoint. -/
def IsLoopFreeStrangeComponent {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ Q.supp = {i, j} ∧
    (underlyingGraph A C).Adj i j ∧ A i j = (1 / 2 : ℂ) ∧ d i = 0 ∧ d j = 0

/-- The number of connected components of the underlying simple graph. -/
def graphComponentCount {n : ℕ} (A C : Mat n) : ℕ := by
  classical
  exact Fintype.card (underlyingGraph A C).ConnectedComponent

/-- The number of loop-free isolated strange edges, counted as components. -/
def loopFreeStrangeComponentCount {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : ℕ := by
  classical
  exact Fintype.card {Q : (underlyingGraph A C).ConnectedComponent //
    IsLoopFreeStrangeComponent A C d Q}

/-- The exact count, for arbitrary size, phase, and common diagonal. -/
def claim : Prop :=
  ∀ (n : ℕ) (A C : Mat n) (d : Fin n → ℂ),
    (∀ i, A i i = d i) → (∀ i, C i i = d i) →
    (realignedProjector A C d).IsHermitian →
    realignedProjector A C d * realignedProjector A C d = realignedProjector A C d →
    (offDiagonal A).IsHermitian →
    IsGreatest {k | HasComponents (adjacency A C d) k}
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d)

private def column {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (q : Fin n × Fin n) : Mat n :=
  fun i j => realignedProjector A C d (i, j) q

private def CommutantResolution {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) (k : ℕ) : Prop :=
  ∃ P : Fin k → Mat n,
    (∀ s, IsOrthogonalProjector (P s) ∧ P s ≠ 0) ∧
    (∑ s, P s) = 1 ∧
    ∀ s q, P s * column A C d q = column A C d q * P s

private theorem commutant_reduction {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (k : ℕ) :
    HasComponents (adjacency A C d) k ↔ CommutantResolution A C d k := by
  sorry

private theorem commutant_upper_bound {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hA : ∀ i, A i i = d i) (hC : ∀ i, C i i = d i)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (k : ℕ)
    (h : CommutantResolution A C d k) :
    k ≤ graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
  sorry

private theorem commutant_attainment {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hA : ∀ i, A i i = d i) (hC : ∀ i, C i i = d i)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) :
    CommutantResolution A C d
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d) := by
  sorry

theorem result : claim := by
  intro n A C d hA hC hH hI hU
  constructor
  · exact (commutant_reduction A C d hH hI _).mpr
      (commutant_attainment A C d hA hC hH hI hU)
  · intro k hk
    exact commutant_upper_bound A C d hA hC hH hI hU k
      ((commutant_reduction A C d hH hI k).mp hk)

end D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
