/- GID: D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.claim; result=D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result; claim=D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.claim
   digest: Two four-cycles sharing a vertex have elliptic Sombor energy 144. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#13389; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.NormNum.RealSqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Matrix BigOperators
open Matrix Polynomial

namespace D5.S3.Combinatorics.Graph.EllipticSomborEnergyIntegerRefutation

/-- The literal degree-weighted matrix in the source's definition. -/
def ellipticSomborMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if G.Adj i j then
    ((G.degree i : ℝ) + (G.degree j : ℝ)) *
      Real.sqrt ((G.degree i : ℝ) ^ 2 + (G.degree j : ℝ) ^ 2)
    else 0

/-- Conjecture 3.9: "There is no graph with integer-valued elliptic Sombor energy."
The Hermitian proof supplies Mathlib's eigenvalue indexing, with multiplicity. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (ellipticSomborMatrix G).IsHermitian) (z : ℤ),
    (∑ i, |hA.eigenvalues i|) ≠ (z : ℝ)

private def bouquet : SimpleGraph (Fin 7) := {
  Adj := fun i j =>
    (i.val = 0 ∧ (j.val = 1 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 6)) ∨
    (j.val = 0 ∧ (i.val = 1 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 6)) ∨
    (i.val = 2 ∧ (j.val = 1 ∨ j.val = 3)) ∨ (j.val = 2 ∧ (i.val = 1 ∨ i.val = 3)) ∨
    (i.val = 5 ∧ (j.val = 4 ∨ j.val = 6)) ∨ (j.val = 5 ∧ (i.val = 4 ∨ i.val = 6))
  symm := ⟨by intro i j; tauto⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩ }

private def witnessMatrix (a b : ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![
  0, 12*b, 0, 12*b, 12*b, 0, 12*b;
  12*b, 0, 8*a, 0, 0, 0, 0;
  0, 8*a, 0, 8*a, 0, 0, 0;
  12*b, 0, 8*a, 0, 0, 0, 0;
  12*b, 0, 0, 0, 0, 8*a, 0;
  0, 0, 0, 0, 8*a, 0, 8*a;
  12*b, 0, 0, 0, 0, 8*a, 0]

private def changeBasis (a b : ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![
  -6*b/7, 0, 0, -2*a*b/15, 0, 0, 6*b/7;
  1, -1, -1, 0, 0, -1, 1;
  -2*a/7, a, 0, 1, 0, -a, 2*a/7;
  1, -1, 1, 0, 0, -1, 1;
  1, 1, 0, 0, -1, 1, 1;
  -2*a/7, -a, 0, 1, 0, a, 2*a/7;
  1, 1, 0, 0, 1, 1, 1]

private def inverseBasis (a b : ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![
  -3*b/28, 1/8, -a/28, 1/8, 1/8, -a/28, 1/8;
  0, -1/8, a/8, -1/8, 1/8, -a/8, 1/8;
  0, -1/2, 0, 1/2, 0, 0, 0;
  -3*a*b/49, 0, 45/98, 0, 0, 45/98, 0;
  0, 0, 0, 0, -1/2, 0, 1/2;
  0, -1/8, -a/8, -1/8, 1/8, a/8, 1/8;
  3*b/28, 1/8, a/28, 1/8, 1/8, a/28, 1/8]

/-- The two squares 0–1–2–3–0 and 0–4–5–6–0 have energy 144. -/
theorem result : ¬ claim := by
  let G := bouquet
  let : DecidableRel G.Adj := by
    dsimp [G, bouquet]
    infer_instance
  have hu : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  have hd : ∀ i : Fin 7, G.degree i = if i.val = 0 then 4 else 2 := by
    norm_num (config := { decide := true }) [Fin.forall_fin_succ, SimpleGraph.degree,
      SimpleGraph.neighborFinset_eq_filter, G, bouquet, hu, Fin.reduceEq, Fin.reduceFinMk]
  let a : ℝ := Real.sqrt 2
  let b : ℝ := Real.sqrt 5
  have ha : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : b ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs8 : Real.sqrt 8 = 2 * a := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num [a]
  have hs20 : Real.sqrt 20 = 2 * b := by
    rw [show (20 : ℝ) = 4 * 5 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num [b]
  let A := witnessMatrix a b
  have hAeq : ellipticSomborMatrix G = A := by
    apply Matrix.ext
    simp only [ellipticSomborMatrix, hd]
    norm_num (config := { decide := true }) [Fin.forall_fin_succ, G, bouquet,
      A, witnessMatrix, hs8, hs20, Fin.reduceEq, Fin.reduceFinMk, ← mul_assoc]
  have hA : (ellipticSomborMatrix G).IsHermitian := by
    rw [hAeq]
    apply Matrix.IsHermitian.ext
    norm_num [Fin.forall_fin_succ, A, witnessMatrix]
  let values : Fin 7 → ℝ := ![-56, -16, 0, 0, 0, 16, 56]
  let P := changeBasis a b
  let Q := inverseBasis a b
  have hQP : Q * P = 1 := by
    apply Matrix.ext
    norm_num (config := { decide := true }) [Fin.forall_fin_succ, Q, P, inverseBasis,
      changeBasis, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.reduceEq, Fin.reduceFinMk]
    repeat' apply And.intro
    all_goals ring_nf <;> simp only [ha, hb]
    all_goals ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hAP : A * P = P * diagonal values := by
    apply Matrix.ext
    simp only [Matrix.mul_diagonal]
    norm_num [Fin.forall_fin_succ, A, P, witnessMatrix, changeBasis, values,
      Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_succ]
    repeat' apply And.intro
    all_goals ring_nf <;> try simp only [ha, hb]
    all_goals ring
  have hc : (ellipticSomborMatrix G).charpoly = (diagonal values).charpoly := by
    rw [hAeq, ← Matrix.mul_one A, ← hPQ, ← Matrix.mul_assoc, hAP,
      Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hpoly : (ellipticSomborMatrix G).charpoly =
      X ^ 3 * (X - C 56) * (X + C 56) * (X - C 16) * (X + C 16) := by
    rw [hc, Matrix.charpoly_diagonal]
    simp [values, Fin.prod_univ_succ]
    ring
  have hroots : (ellipticSomborMatrix G).charpoly.roots =
      Finset.univ.val.map values := by
    rw [hpoly]
    have h0 : (X : ℝ[X]) ^ 3 ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    have h1 := mul_ne_zero h0 (Polynomial.X_sub_C_ne_zero (56 : ℝ))
    have h2 := mul_ne_zero h1 (Polynomial.X_add_C_ne_zero (56 : ℝ))
    have h3 := mul_ne_zero h2 (Polynomial.X_sub_C_ne_zero (16 : ℝ))
    have h4 := mul_ne_zero h3 (Polynomial.X_add_C_ne_zero (16 : ℝ))
    rw [Polynomial.roots_mul h4, Polynomial.roots_mul h3, Polynomial.roots_mul h2,
      Polynomial.roots_mul h1, Polynomial.roots_X_pow, Polynomial.roots_X_sub_C,
      Polynomial.roots_X_add_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_add_C,
      Fin.univ_val_map]
    change 3 • ({0} : Multiset ℝ) + {56} + {-56} + {16} + {-16} =
      ({-56, -16, 0, 0, 0, 16, 56} : Multiset ℝ)
    simp only [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]
    change _ = ({-56} + ({-16} + ({0} + ({0} + ({0} + ({16} + {56}))))): Multiset ℝ)
    ac_rfl
  have heigen : Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map values := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.roots_charpoly_eq_eigenvalues.symm.trans hroots
  have henergy : (∑ i, |hA.eigenvalues i|) = 144 := by
    have he := congrArg (fun s : Multiset ℝ => (s.map abs).sum) heigen
    norm_num [Multiset.map_map, Function.comp_def, values, Fin.sum_univ_succ] at he ⊢
    exact he
  intro h
  exact h 7 G hA (144 : ℤ) (by simpa using henergy)

end D5.S3.Combinatorics.Graph.EllipticSomborEnergyIntegerRefutation
