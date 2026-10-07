/- GID: D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.claim; result=D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result; claim=D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.claim
   digest: Three four-cycles sharing one vertex have Sombor energy 48. -/

/-
proof_shape: result: bind-only (finite matrix identities and pinned spectral identities).
escape_witness: none
admission_basis: open-problem-resolution (#13388; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

open Matrix Finset Polynomial

namespace D5.S3.Combinatorics.Graph.SomborEnergyIntegerRefutation

/-- The literal Sombor matrix: degree weights on adjacent pairs and zero elsewhere. -/
noncomputable def somborMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if G.Adj i j then Real.sqrt ((G.degree i : ℝ)^2 + (G.degree j : ℝ)^2) else 0

/-- Ghanbari's Conjecture 3.8: “There is no graph with integer-valued Sombor energy.” -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let hA : (somborMatrix G).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [somborMatrix, star_trivial, G.adj_comm, add_comm]
    ∀ z : ℤ, (∑ i, |hA.eigenvalues i|) ≠ (z : ℝ)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
/-- The bouquet of three four-cycles has integer Sombor energy 48. -/
theorem result : ¬ claim := by
  let r : Fin 10 → Fin 10 → Prop := fun i j =>
    (i.val = 0 ∧ (j.val = 1 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 9)) ∨
    (i.val = 2 ∧ (j.val = 1 ∨ j.val = 3)) ∨
    (i.val = 5 ∧ (j.val = 4 ∨ j.val = 6)) ∨
    (i.val = 8 ∧ (j.val = 7 ∨ j.val = 9))
  let : DecidableRel r := by dsimp [r]; infer_instance
  let G : SimpleGraph (Fin 10) := SimpleGraph.fromRel r
  let : DecidableRel G.Adj := inferInstance
  have hdeg (i : Fin 10) : G.degree i = if i = 0 then 6 else 2 := by
    revert i
    decide
  have hadj (i j : Fin 10) : G.Adj i j ↔
      (!![0, 1, 0, 1, 1, 0, 1, 1, 0, 1;
      1, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
      1, 0, 0, 0, 0, 0, 0, 0, 1, 0] : Matrix (Fin 10) (Fin 10) ℕ) i j = 1 := by
    fin_cases i <;> fin_cases j <;> decide
  classical
  let a : ℝ := Real.sqrt 40
  let b : ℝ := Real.sqrt 8
  have ha : a^2 = 40 := Real.sq_sqrt (by norm_num)
  have hb : b^2 = 8 := Real.sq_sqrt (by norm_num)
  have hmatrix : somborMatrix G =
    !![0, a, 0, a, a, 0, a, a, 0, a;
    a, 0, b, 0, 0, 0, 0, 0, 0, 0;
    0, b, 0, b, 0, 0, 0, 0, 0, 0;
    a, 0, b, 0, 0, 0, 0, 0, 0, 0;
    a, 0, 0, 0, 0, b, 0, 0, 0, 0;
    0, 0, 0, 0, b, 0, b, 0, 0, 0;
    a, 0, 0, 0, 0, b, 0, 0, 0, 0;
    a, 0, 0, 0, 0, 0, 0, 0, b, 0;
    0, 0, 0, 0, 0, 0, 0, b, 0, b;
    a, 0, 0, 0, 0, 0, 0, 0, b, 0] := by
    ext i j
    simp only [somborMatrix, hdeg, hadj]
    fin_cases i <;> fin_cases j <;> norm_num [a, b]
  let P : Matrix (Fin 10) (Fin 10) ℝ :=
    !![3*a, -3*a, 0, 0, 0, 0, 0, 0, 0, b;
    8, 8, 2, 2, 2, 2, 1, 0, 0, 0;
    b, -b, b, -b, b, -b, 0, 0, 0, -a;
    8, 8, 2, 2, 2, 2, -1, 0, 0, 0;
    8, 8, -2, -2, 2, 2, 0, 1, 0, 0;
    b, -b, -b, b, b, -b, 0, 0, 0, -a;
    8, 8, -2, -2, 2, 2, 0, -1, 0, 0;
    8, 8, 0, 0, -4, -4, 0, 0, 1, 0;
    b, -b, 0, 0, -2*b, 2*b, 0, 0, 0, -a;
    8, 8, 0, 0, -4, -4, 0, 0, -1, 0]
  let d : Fin 10 → ℝ := ![16, -16, 4, -4, 4, -4, 0, 0, 0, 0]
  let norms : Fin 10 → ℝ := ![768, 768, 32, 32, 96, 96, 2, 2, 2, 128]
  have horth : Pᵀ * P = Matrix.diagonal norms := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, P, norms,
        Matrix.diagonal_apply] <;> ring_nf <;> norm_num [ha, hb]
  let Q : Matrix (Fin 10) (Fin 10) ℝ := Matrix.diagonal (fun i => (norms i)⁻¹) * Pᵀ
  have hqp : Q * P = 1 := by
    dsimp [Q]
    rw [Matrix.mul_assoc, horth, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [norms, Matrix.diagonal_apply]
  have hpq : P * Q = 1 := mul_eq_one_comm.mp hqp
  have heigen : somborMatrix G * P = P * Matrix.diagonal d := by
    rw [hmatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, P, d, Matrix.diagonal_apply] <;>
      ring_nf <;> norm_num [ha, hb]
  have hchar : (somborMatrix G).charpoly = ∏ i, (X - C (d i)) := by
    have hsim : somborMatrix G = (P * Matrix.diagonal d) * Q := by
      rw [← heigen, Matrix.mul_assoc, hpq, Matrix.mul_one]
    rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hqp,
      Matrix.one_mul, Matrix.charpoly_diagonal]
  have hfactor : (somborMatrix G).charpoly =
      X^4 * (X - C 16) * (X + C 16) * (X - C 4)^2 * (X + C 4)^2 := by
    rw [hchar]
    norm_num [Fin.prod_univ_succ, d]
    ring
  have hA : (somborMatrix G).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [somborMatrix, star_trivial, G.adj_comm, add_comm]
  have hroots : Multiset.map hA.eigenvalues Finset.univ.val =
      Multiset.map d Finset.univ.val := by
    have hr := hA.roots_charpoly_eq_eigenvalues
    have hproduct : X^4 * (X - C 16) * (X + C 16) * (X - C 4)^2 * (X + C 4)^2 =
        ∏ i, (X - C (d i)) := by
      norm_num [Fin.prod_univ_succ, d]
      ring
    rw [hfactor, hproduct, Polynomial.roots_prod] at hr
    · simpa using hr.symm
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have henergy : (∑ i, |hA.eigenvalues i|) = 48 := by
    have hs := congrArg (fun s : Multiset ℝ => (s.map abs).sum) hroots
    calc
      (∑ i, |hA.eigenvalues i|) = ∑ i, |d i| := by
        simpa only [Multiset.map_map, Function.comp_def, Finset.sum] using hs
      _ = 48 := by norm_num [Fin.sum_univ_succ, d]

  intro h
  exact h 10 G 48 henergy

end D5.S3.Combinatorics.Graph.SomborEnergyIntegerRefutation
