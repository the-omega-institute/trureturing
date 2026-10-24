/- GID: D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every positive Gibbs weight vector admits a stochastic matrix with simple spectrum. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Stochastic
import D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum

open Matrix Finset
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence

/-- Column stochasticity and preservation of the Gibbs weights. -/
def IsGibbsStochastic {n : ℕ} (d : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P ∈ Matrix.colStochastic ℝ (Fin n) ∧ P *ᵥ d = d

/-- Every complex eigenvalue has algebraic multiplicity one. -/
def HasSimpleEigenvalues {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ((P.map (algebraMap ℝ ℂ)).charpoly.roots).Nodup

/-- A simple-spectrum Gibbs-stochastic matrix exists for every positive Gibbs vector. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∃ P : Matrix (Fin n) (Fin n) ℝ, IsGibbsStochastic d P ∧ HasSimpleEigenvalues P

private noncomputable def weights {n : ℕ} (d : Fin n → ℝ) : Fin n → ℝ :=
  fun i => d i / ∑ j, d j

private def adjacent {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

private noncomputable def transition {n : ℕ} (g : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then 1 - ∑ k, if adjacent k j then g k / 2 else 0
  else if adjacent i j then g i / 2 else 0

private noncomputable def symmetrization {n : ℕ} (g : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => (Real.sqrt (g i))⁻¹) * transition g * diagonal (fun i => Real.sqrt (g i))

private lemma weights_positive {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < weights d i := by
  sorry

private lemma weights_sum {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∑ i, weights d i = 1 := by
  sorry

private lemma transition_stochastic {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsum : ∑ i, g i ≤ 1) :
    transition g ∈ Matrix.colStochastic ℝ (Fin n) := by
  sorry

private lemma transition_stationary {n : ℕ} (g : Fin n → ℝ) :
    transition g *ᵥ g = g := by
  sorry

private lemma transition_preserves_weights {m : ℕ} (d : Fin (m + 1) → ℝ)
    (hd : ∀ i, 0 < d i) : transition (weights d) *ᵥ d = d := by
  sorry

private lemma symmetrization_charpoly {n : ℕ} (g : Fin n → ℝ) (hg : ∀ i, 0 < g i) :
    (transition g).charpoly = (symmetrization g).charpoly := by
  sorry

private lemma symmetrization_jacobi {m : ℕ} (g : Fin (m + 1) → ℝ)
    (hg : ∀ i, 0 < g i) :
    ∃ a e : Fin (m + 1) → ℝ,
      (∀ t : Fin m, e t.castSucc ≠ 0) ∧ symmetrization g = jacobiMatrix m a e := by
  sorry

private lemma jacobi_simple (m : ℕ) (a e : Fin (m + 1) → ℝ)
    (he : ∀ t : Fin m, e t.castSucc ≠ 0) :
    HasSimpleEigenvalues (jacobiMatrix m a e) := by
  sorry

private lemma empty_case (d : Fin 0 → ℝ) :
    ∃ P : Matrix (Fin 0) (Fin 0) ℝ, IsGibbsStochastic d P ∧ HasSimpleEigenvalues P := by
  sorry

theorem result : claim := by
  intro n d hd
  cases n with
  | zero => exact empty_case d
  | succ m =>
    have hg := weights_positive d hd
    obtain ⟨a, e, he, hS⟩ := symmetrization_jacobi (weights d) hg
    refine ⟨transition (weights d), ⟨?_, transition_preserves_weights d hd⟩, ?_⟩
    · exact transition_stochastic (weights d) (fun i => (hg i).le) (weights_sum d hd).le
    · unfold HasSimpleEigenvalues at *
      rw [Matrix.charpoly_map, symmetrization_charpoly (weights d) hg, hS,
        ← Matrix.charpoly_map]
      exact jacobi_simple m a e he

end D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
