/- GID: D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.claim; result=D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result; claim=D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.claim
   digest: The edgeless graph has diminished Sombor energy zero, an integer. -/

/-
proof_shape: result: bind-only (the zero-matrix spectral theorem and normalization).
escape_witness: none
admission_basis: open-problem-resolution (#13380; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DiminishedSomborEnergyRefutation

/-- Movahedi's diminished Sombor matrix, with the quotient evaluated only on edges. -/
noncomputable def diminishedSomborMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if G.Adj i j then
    Real.sqrt ((G.degree i : ℝ) ^ 2 + (G.degree j : ℝ) ^ 2) /
      ((G.degree i : ℝ) + (G.degree j : ℝ))
    else 0

/-- The sum of the absolute values of the real Hermitian eigenvalues. -/
noncomputable def diminishedSomborEnergy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : ℝ := by
  have h : (diminishedSomborMatrix G).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    simp only [Matrix.transpose_apply, diminishedSomborMatrix, G.adj_comm, add_comm]
  exact ∑ i, |h.eigenvalues i|

/-- "There does not exist a graph whose diminished Sombor energy is an integer value." -/
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬ ∃ z : ℤ, diminishedSomborEnergy G = (z : ℝ)

/-- The edgeless graph on one vertex refutes the conjecture. -/
theorem result : ¬ claim := by
  have matrix_zero (n : ℕ) : diminishedSomborMatrix (⊥ : SimpleGraph (Fin n)) = 0 := by
    ext i j
    simp only [diminishedSomborMatrix, SimpleGraph.bot_adj, ite_false, Matrix.zero_apply]
  have energy_zero (n : ℕ) : diminishedSomborEnergy (⊥ : SimpleGraph (Fin n)) = 0 := by
    unfold diminishedSomborEnergy
    have h : (diminishedSomborMatrix (⊥ : SimpleGraph (Fin n))).IsHermitian := by
      rw [matrix_zero n]
      exact Matrix.isHermitian_zero
    have eigenvalues_zero : h.eigenvalues = 0 := h.eigenvalues_eq_zero_iff.mpr (matrix_zero n)
    change ∑ i, |h.eigenvalues i| = 0
    simp only [eigenvalues_zero, Pi.zero_apply, abs_zero, Finset.sum_const_zero]
  intro h
  exact h 1 (by decide) ⊥ ⟨0, by simpa only [Int.cast_zero] using energy_zero 1⟩

end D5.S3.Combinatorics.Graph.DiminishedSomborEnergyRefutation
