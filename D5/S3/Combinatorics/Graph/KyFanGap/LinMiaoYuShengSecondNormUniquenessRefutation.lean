/- GID: D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.claim; result=D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.result; claim=D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.claim
   digest: A six-vertex counterexample to second Ky Fan norm uniqueness. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#21801; Refuted).
Direct frozen dependencies: kyFan from D5/S3/Combinatorics/Graph/KyFanGap/Defs;
declaration statement_id: sha256:01812327c4b72d417e2b26b3b13afdb69463ea68f5dfbc02710356632018d17c.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
LI, Gmn and claim preserve the source expressions fixed by issue #21801.
H is the concrete graph with a universal vertex and disjoint extra edges {1,2}, {3,4}.
All private theorems below have proof_shape: bind-only and escape_witness: none:
h_degree: consumers h_not_iso, h_lap; direct frozen dependencies none.
b_degree: consumers h_not_iso, b_lap; direct frozen dependencies none.
h_edges: consumers h_norm, result; direct frozen dependencies none.
b_edges: consumer b_norm; direct frozen dependencies none.
h_connected: consumer result; direct frozen dependencies none.
h_not_iso: consumer result; direct frozen dependencies none.
h_lap: consumer h_norm; direct frozen dependencies none.
b_lap: consumer b_norm; direct frozen dependencies none.
kyFan_two_diagonalized: consumers h_norm, b_norm; direct frozen dependency kyFan.
h_norm: consumer result; direct frozen dependency kyFan.
b_norm: consumer result; direct frozen dependency kyFan.
Definitions have proof_shape: not-applicable and escape_witness: none.
Adjacency decidability uses the existing SimpleGraph.fromRel instance.
No non-bind-only content or all-order family theorem is asserted.
-/

import D5.S3.Combinatorics.Graph.KyFanGap.Defs
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-! Binding definitions for Conjecture 5.11 of arXiv:2012.11162v2.
The two norms are each asserted to have the stated unique maximizer.
The source's intended n-vertex, m-edge graph is encoded by its Figure 1;
the printed pendant count 2n-m+3 is inconsistent with those cardinalities.
-/

noncomputable section

namespace D5.S3.Combinatorics.Graph.KyFanGap.LinMiaoYuShengSecondNormUniquenessRefutation

open D5.S3.Combinatorics.Graph.KyFanGap

/-- LI(G) = L(G) - (2 |E(G)| / n) I_n; L is Mathlib's D-A. -/
def LI {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  letI : DecidableRel G.Adj := Classical.decRel _
  G.lapMatrix ℝ - ((2 * (Nat.card G.edgeSet : ℝ)) / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- On n ≤ m and m + 3 ≤ 2n, G_{m,n} has universal vertex 0, and vertex 1 is joined to
vertices 2 through m-n+2. Thus m-n+1 triangles share edge {0,1}.
The remaining 2n-m-3 vertices are pendant at vertex 0. -/
@[reducible]
def Gmn (n m : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v =>
    u.val = 0 ∨ (u.val = 1 ∧ 2 ≤ v.val ∧ v.val < m - n + 3)

/-- Conjecture 5.11, with a separate unique maximum for each of k=2 and k=3.
The edge-range upper bound is written m+3 ≤ 2n to avoid truncated subtraction. -/
def claim : Prop :=
  ∀ (n : ℕ) (m : ℕ), n ≤ m → m + 3 ≤ 2 * n →
    ∀ G : SimpleGraph (Fin n), G.Connected → Nat.card G.edgeSet = m →
      ∀ k : ℕ, (k = 2 ∨ k = 3) →
        kyFan k (LI G) ≤ kyFan k (LI (Gmn n m)) ∧
          (kyFan k (LI G) = kyFan k (LI (Gmn n m)) ↔
            Nonempty (G ≃g Gmn n m))

open Matrix
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[reducible]
private def H : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    u.val = 0 ∨ (u.val = 1 ∧ v.val = 2) ∨ (u.val = 3 ∧ v.val = 4)


private theorem h_degree : ∀ i : Fin 6, H.degree i = ![5,2,2,2,2,1] i := by
  decide

private theorem b_degree : ∀ i : Fin 6, (Gmn 6 7).degree i = ![5,3,2,2,1,1] i := by
  decide

private theorem h_edges : Nat.card H.edgeSet = 7 := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  decide

private theorem b_edges : Nat.card (Gmn 6 7).edgeSet = 7 := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  decide

private theorem h_connected : H.Connected := by
  apply SimpleGraph.Connected.of_isUniversal (v := 0)
  intro w hw
  simp [H, SimpleGraph.fromRel_adj, hw]

private theorem h_not_iso : ¬ Nonempty (H ≃g Gmn 6 7) := by
  rintro ⟨e⟩
  have he := e.symm.degree_eq (1 : Fin 6)
  rw [h_degree, b_degree] at he
  have hn : ∀ i : Fin 6, (![5,2,2,2,2,1] : Fin 6 → ℕ) i ≠ 3 := by decide
  exact hn _ he

private theorem h_lap [inst : DecidableRel (H).Adj] :
    (H).lapMatrix ℝ = !![5, -1, -1, -1, -1, -1; -1, 2, -1, 0, 0, 0; -1, -1, 2, 0, 0, 0; -1, 0, 0, 2, -1, 0; -1, 0, 0, -1, 2, 0; -1, 0, 0, 0, 0, 1] := by
  have heq : inst = (instDecidableRelAdjFromRelOfDecidableEq
      (fun u v : Fin 6 =>
        u.val = 0 ∨ (u.val = 1 ∧ v.val = 2) ∨ (u.val = 3 ∧ v.val = 4))) :=
    Subsingleton.elim _ _
  subst inst
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      h_degree, H, Gmn, SimpleGraph.fromRel_adj]

private theorem b_lap [inst : DecidableRel (Gmn 6 7).Adj] :
    (Gmn 6 7).lapMatrix ℝ = !![5, -1, -1, -1, -1, -1; -1, 3, -1, -1, 0, 0; -1, -1, 2, 0, 0, 0; -1, -1, 0, 2, 0, 0; -1, 0, 0, 0, 1, 0; -1, 0, 0, 0, 0, 1] := by
  have heq : inst = (instDecidableRelAdjFromRelOfDecidableEq
      (fun u v : Fin 6 =>
        u.val = 0 ∨ (u.val = 1 ∧ 2 ≤ v.val ∧ v.val < 7 - 6 + 3))) :=
    Subsingleton.elim _ _
  subst inst
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      b_degree, Gmn, SimpleGraph.fromRel_adj]

open Polynomial

private theorem kyFan_two_diagonalized (M P R : Matrix (Fin 6) (Fin 6) ℝ)
    (d : Fin 6 → ℝ) (hM : M.IsSymm) (hPR : P * R = 1)
    (hMP : M * P = P * diagonal d) (hd : Antitone fun i => d i ^ 2) :
    D5.S3.Combinatorics.Graph.KyFanGap.kyFan 2 M = |d 0| + |d 1| := by
  classical
  let A := Matrix.toEuclideanLin M
  let Q := LinearMap.adjoint A ∘ₗ A
  have hQ : Q.IsSymmetric := A.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 6)) = 6 := finrank_euclideanSpace_fin
  have hP : P.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hPR
  have hGram : (Mᵀ * M) * P = P * diagonal (fun i => d i ^ 2) := by
    rw [hM, Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hMP, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    simp [pow_two]
  have hchar : Q.charpoly = ∏ i, (X - C (d i ^ 2)) := by
    have hmap : Q = Matrix.toEuclideanLin (Mᵀ * M) := by
      dsimp only [Q, A]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint M]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.toLpLin_mul_same 2 M.conjTranspose M).symm
    rw [hmap, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin,
      Matrix.charpoly_eq_of_mul_eq_mul hP hGram, Matrix.charpoly_diagonal]
  have hroots : Q.charpoly.roots =
      Multiset.map (fun i => d i ^ 2) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod _ _ (by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact Polynomial.X_sub_C_ne_zero (d i ^ 2))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have heig : hQ.eigenvalues hn = fun i => d i ^ 2 := by
    rw [← List.ofFn_inj, ← hQ.sort_roots_charpoly_eq_eigenvalues hn]
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, Multiset.coe_sort]
    convert! List.mergeSort_of_pairwise ?_
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hd.sortedGE_ofFn
  have hsing (i : Fin 6) : A.singularValues i = |d i| := by
    rw [A.singularValues_fin hn i]
    change Real.sqrt (hQ.eigenvalues hn i) = _
    rw [heig]
    exact Real.sqrt_sq_eq_abs _
  change (∑ i : Fin 2, A.singularValues (i : ℕ)) = _
  simp only [Fin.sum_univ_two]
  exact congrArg₂ (· + ·) (hsing 0) (hsing 1)

private theorem h_norm : D5.S3.Combinatorics.Graph.KyFanGap.kyFan 2 (LI (H)) = 6 := by
  let P : Matrix (Fin 6) (Fin 6) ℝ := !![-5, 1, 0, 0, 0, 0; 1, 1, -1, -1, -1, 0; 1, 1, -1, -1, 1, 0; 1, 1, 1, 0, 0, -1; 1, 1, 1, 0, 0, 1; 1, 1, 0, 2, 0, 0]
  let R : Matrix (Fin 6) (Fin 6) ℝ := !![-1/6, 1/30, 1/30, 1/30, 1/30, 1/30; 1/6, 1/6, 1/6, 1/6, 1/6, 1/6; 0, -1/5, -1/5, 3/10, 3/10, -1/5; 0, -1/10, -1/10, -1/10, -1/10, 2/5; 0, -1/2, 1/2, 0, 0, 0; 0, 0, 0, -1/2, 1/2, 0]
  let d : Fin 6 → ℝ := ![11/3, -7/3, -4/3, -4/3, 2/3, 2/3]
  have hPR : P * R = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, R, Matrix.mul_apply, Fin.sum_univ_succ]
  have hM : (LI (H)).IsSymm := by
    unfold LI
    letI : DecidableRel (H).Adj := Classical.decRel _
    exact (SimpleGraph.isSymm_lapMatrix ℝ (H)).sub
      (Matrix.isSymm_one.smul (2 * (Nat.card (H).edgeSet : ℝ) / (6 : ℝ)))
  have hMP : LI (H) * P = P * diagonal d := by
    rw [LI, h_edges, @h_lap (Classical.decRel _)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, d, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hd : Antitone fun i => d i ^ 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [d] at *
  have h := kyFan_two_diagonalized (LI (H)) P R d hM hPR hMP hd
  norm_num [d] at h
  exact h

private theorem b_norm : D5.S3.Combinatorics.Graph.KyFanGap.kyFan 2 (LI (Gmn 6 7)) = 6 := by
  let P : Matrix (Fin 6) (Fin 6) ℝ := !![-5, 1, 0, 0, 0, 0; 1, 1, -2, -1, -1, 0; 1, 1, 1, -1, -1, -1; 1, 1, 1, -1, -1, 1; 1, 1, 0, 3, 0, 0; 1, 1, 0, 0, 3, 0]
  let R : Matrix (Fin 6) (Fin 6) ℝ := !![-1/6, 1/30, 1/30, 1/30, 1/30, 1/30; 1/6, 1/6, 1/6, 1/6, 1/6, 1/6; 0, -1/3, 1/6, 1/6, 0, 0; 0, -1/15, -1/15, -1/15, 4/15, -1/15; 0, -1/15, -1/15, -1/15, -1/15, 4/15; 0, 0, -1/2, 1/2, 0, 0]
  let d : Fin 6 → ℝ := ![11/3, -7/3, 5/3, -4/3, -4/3, -1/3]
  have hPR : P * R = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, R, Matrix.mul_apply, Fin.sum_univ_succ]
  have hM : (LI (Gmn 6 7)).IsSymm := by
    unfold LI
    letI : DecidableRel (Gmn 6 7).Adj := Classical.decRel _
    exact (SimpleGraph.isSymm_lapMatrix ℝ (Gmn 6 7)).sub
      (Matrix.isSymm_one.smul (2 * (Nat.card (Gmn 6 7).edgeSet : ℝ) / (6 : ℝ)))
  have hMP : LI (Gmn 6 7) * P = P * diagonal d := by
    rw [LI, b_edges, @b_lap (Classical.decRel _)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, d, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hd : Antitone fun i => d i ^ 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [d] at *
  have h := kyFan_two_diagonalized (LI (Gmn 6 7)) P R d hM hPR hMP hd
  norm_num [d] at h
  exact h

theorem result : ¬ claim := by
  intro h
  have hc := (h 6 7 (by decide) (by decide) H h_connected h_edges 2 (Or.inl rfl)).2
  exact h_not_iso (hc.mp (h_norm.trans b_norm.symm))

end D5.S3.Combinatorics.Graph.KyFanGap.LinMiaoYuShengSecondNormUniquenessRefutation
