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

open _root_.Matrix Finset
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
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j =>
  if i = j then 1 - ∑ k, if adjacent k j then g k / 2 else 0
  else if adjacent i j then g i / 2 else 0

private noncomputable def symmetrization {n : ℕ} (g : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => (Real.sqrt (g i))⁻¹) * transition g * diagonal (fun i => Real.sqrt (g i))

private lemma weights_positive {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < weights d i := by
  have hs : 0 < ∑ j, d j := sum_pos (fun j _ => hd j) univ_nonempty
  intro i
  exact div_pos (hd i) hs

private lemma weights_sum {m : ℕ} (d : Fin (m + 1) → ℝ) (hd : ∀ i, 0 < d i) :
    ∑ i, weights d i = 1 := by
  have hs : 0 < ∑ j, d j := sum_pos (fun j _ => hd j) univ_nonempty
  unfold weights
  rw [← sum_div, div_self hs.ne']

private lemma transition_columns {n : ℕ} (g : Fin n → ℝ) (j : Fin n) :
    ∑ i, transition g i j = 1 := by
  classical
  have hj : ¬ adjacent j j := by unfold adjacent; omega
  have entry (i : Fin n) : transition g i j =
      (if i = j then 1 - ∑ k, if adjacent k j then g k / 2 else 0 else 0) +
      (if adjacent i j then g i / 2 else 0) := by
    by_cases h : i = j
    · subst i
      simp only [transition, if_pos rfl, if_neg hj, add_zero]
    · simp only [transition, if_neg h, zero_add]
  simp_rw [entry]
  rw [sum_add_distrib]
  simp

private lemma transition_stochastic {n : ℕ} (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsum : ∑ i, g i ≤ 1) :
    transition g ∈ Matrix.colStochastic ℝ (Fin n) := by
  classical
  rw [Matrix.mem_colStochastic_iff_sum]
  refine ⟨?_, transition_columns g⟩
  intro i j
  by_cases h : i = j
  · subst i
    have hb : (∑ k, if adjacent k j then g k / 2 else 0) ≤ (∑ k, g k) / 2 := by
      rw [sum_div]
      apply sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hg k) (by norm_num)
    rw [transition, if_pos rfl]
    linarith
  · rw [transition, if_neg h]
    split_ifs
    · exact div_nonneg (hg i) (by norm_num)
    · exact le_rfl

private lemma transition_stationary {n : ℕ} (g : Fin n → ℝ) :
    transition g *ᵥ g = g := by
  classical
  have balance (i j : Fin n) : transition g i j * g j = transition g j i * g i := by
    by_cases h : i = j
    · subst i; rfl
    · have ha : adjacent i j ↔ adjacent j i := by unfold adjacent; exact or_comm
      by_cases hij : adjacent i j
      · simp only [transition, if_neg h, if_neg (Ne.symm h), if_pos hij, if_pos (ha.mp hij)]
        ring
      · simp only [transition, if_neg h, if_neg (Ne.symm h), if_neg hij,
          if_neg (fun hji => hij (ha.mpr hji)), zero_mul]
  ext i
  change (∑ j, transition g i j * g j) = g i
  simp_rw [balance i]
  rw [← sum_mul, transition_columns, one_mul]

private lemma transition_preserves_weights {m : ℕ} (d : Fin (m + 1) → ℝ)
    (hd : ∀ i, 0 < d i) : transition (weights d) *ᵥ d = d := by
  have hs : (∑ j, d j) ≠ 0 := ne_of_gt (sum_pos (fun j _ => hd j) univ_nonempty)
  have hdg : d = (∑ j, d j) • weights d := by
    funext i
    dsimp [weights]
    field_simp [hs]
  calc
    transition (weights d) *ᵥ d = transition (weights d) *ᵥ ((∑ j, d j) • weights d) :=
      congrArg (fun v => transition (weights d) *ᵥ v) hdg
    _ = (∑ j, d j) • weights d := by rw [mulVec_smul, transition_stationary]
    _ = d := hdg.symm

private lemma symmetrization_charpoly {n : ℕ} (g : Fin n → ℝ) (hg : ∀ i, 0 < g i) :
    (transition g).charpoly = (symmetrization g).charpoly := by
  have hcancel : diagonal (fun i => Real.sqrt (g i)) *
      diagonal (fun i => (Real.sqrt (g i))⁻¹) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hg i)).ne'
  unfold symmetrization
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hcancel, one_mul]

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
  refine ⟨1, ⟨(Matrix.colStochastic ℝ (Fin 0)).one_mem, ?_⟩, ?_⟩
  · exact one_mulVec d
  · unfold HasSimpleEigenvalues
    rw [Matrix.charpoly_isEmpty, Polynomial.roots_one]
    exact Multiset.nodup_zero

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
