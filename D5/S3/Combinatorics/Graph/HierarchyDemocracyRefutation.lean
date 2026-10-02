/- GID: D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HierarchyDemocracyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.claim; result=D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result; claim=D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.claim
   digest: A weakly connected digraph has forward democracy coefficient 901/898 (1908.04358). -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit graph and level
  vector: the residual identity from the normal equations, the kernel of `M` and the coefficient
  value by `norm_num`/`ring`/`linarith`, and five explicit adjacencies for weak connectivity)
escape_witness: null
admission_basis: open-problem-resolution (issue #11800; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation

/-!
G. Moutsinas, C. Shuaib, W. Guo, S. Jarvis, *Graph Hierarchy: A novel approach to understanding
hierarchical structures in complex networks*, arXiv:1908.04358 (Sci. Rep. 11 (2021) 13943),
Conjecture 3.6: for a weakly connected weighted simple directed graph, the forward democracy
coefficient `η_f = 1 − Mean(g_j − g_i)`, the mean over the arcs `i → j` weighted by `a_ij`, is at
most `1`, where the forward hierarchical levels `g` are the minimum-norm minimizer of `‖M x − d‖₂`
for the in-degree vector `d` and `M = (diag d − A)ᵀ`. A six-vertex graph gives `η_f = 901/898`.
-/

open Matrix

/-- Weighted in-degree `d_j = ∑_i a_ij`. -/
def indeg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ := ∑ i, A i j

/-- `M = Lᵀ` for the in-degree Laplacian `L = diag(d) − A`. -/
def lapT {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.diagonal (indeg A) - A)ᵀ

/-- The Euclidean residual `‖M x − d‖₂`. -/
noncomputable def residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (lapT A *ᵥ x - indeg A) : EuclideanSpace ℝ (Fin n))‖

/-- Definition 3.1: `g` minimizes `‖M x − d‖₂`, and among the minimizers it has the least
Euclidean norm `‖x‖₂`. -/
def IsForwardLevels {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) : Prop :=
  (∀ x, residual A g ≤ residual A x) ∧
    ∀ x, (∀ y, residual A x ≤ residual A y) →
      ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

/-- The forward democracy coefficient `1 − Mean(g_j − g_i)` over the arcs, weighted by `a_ij`. -/
noncomputable def forwardDemocracy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) : ℝ :=
  1 - (∑ i, ∑ j, A i j * (g j - g i)) / ∑ i, ∑ j, A i j

/-- The underlying undirected graph of the arcs `a_ij > 0` is connected. -/
def WeaklyConnected {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (SimpleGraph.fromRel fun i j : Fin n => 0 < A i j).Connected

/-- Conjecture 3.6, first bullet, forward half: every weakly connected weighted simple directed
graph has forward democracy coefficient at most `1`. -/
def claim : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ A i j) → (∀ i, A i i = 0) →
    WeaklyConnected A → ∀ g, IsForwardLevels A g → forwardDemocracy A g ≤ 1

-- `result` is one declaration that contains every lemma of the proof as a local `have`.
/-- Conjecture 3.6 fails: the unweighted graph with arcs `1→4, 1→5, 2→6, 3→6, 4→5, 4→6, 5→1, 5→2,
5→3, 5→4, 6→1, 6→5` is weakly connected, has forward levels
`(227, −991, −991, 329, 767, 659)/2694`, and forward democracy coefficient `901/898`. -/
theorem result : ¬ claim := by
  intro h
  let A : Matrix (Fin 6) (Fin 6) ℝ :=
    !![0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 1, 1; 1, 1, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0]
  let g : Fin 6 → ℝ :=
    ![227 / 2694, -991 / 2694, -991 / 2694, 329 / 2694, 767 / 2694, 659 / 2694]
  have hnn : ∀ i j, 0 ≤ A i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [A]
  have hdiag : ∀ i, A i i = 0 := by
    intro i; fin_cases i <;> simp [A]
  have hd : indeg A = ![2, 1, 1, 2, 3, 3] := by
    funext j; fin_cases j <;> simp [indeg, A, Fin.sum_univ_six] <;> norm_num
  have hL : lapT A = !![2, 0, 0, 0, -1, -1; 0, 1, 0, 0, -1, 0; 0, 0, 1, 0, -1, 0;
      -1, 0, 0, 2, -1, 0; -1, 0, 0, -1, 3, -1; 0, -1, -1, -1, 0, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lapT, hd, A, Matrix.transpose_apply]
  -- Euclidean norms as square roots of sums of squares.
  have hnormv : ∀ v : Fin 6 → ℝ,
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 6))‖ = √(∑ i, v i ^ 2) := by
    intro v
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  set Sq : (Fin 6 → ℝ) → ℝ := fun x => ∑ i, ((lapT A *ᵥ x) i - indeg A i) ^ 2 with hSq
  have hnormr : ∀ x, residual A x = √(Sq x) := by
    intro x
    rw [residual, hnormv]
    simp [hSq]
  -- `‖M x − d‖² = ‖M g − d‖² + ‖M (x − g)‖²`, from `Mᵀ (M g − d) = 0`
  have hres : ∀ x : Fin 6 → ℝ, Sq x = Sq g + ∑ i, ((lapT A *ᵥ (x - g)) i) ^ 2 := by
    intro x
    simp only [hSq, hL, hd]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, g]
    ring
  have hlev : IsForwardLevels A g := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [hnormr, hnormr]
      apply Real.sqrt_le_sqrt
      rw [hres x]
      linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        sq_nonneg ((lapT A *ᵥ (x - g)) i))]
    have hle := hx g
    rw [hnormr, hnormr, Real.sqrt_le_sqrt_iff (Finset.sum_nonneg fun i _ => sq_nonneg _),
      hres x] at hle
    have hzero : ∀ i, (lapT A *ᵥ (x - g)) i = 0 := by
      have hsum : ∑ i, ((lapT A *ᵥ (x - g)) i) ^ 2 = 0 := by
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
          sq_nonneg ((lapT A *ᵥ (x - g)) i))
        linarith
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hsum i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have e0 := hzero 0
    have e1 := hzero 1
    have e2 := hzero 2
    have e3 := hzero 3
    have e4 := hzero 4
    have e5 := hzero 5
    simp [hL, Matrix.mulVec, dotProduct, Fin.sum_univ_six, g] at e0 e1 e2 e3 e4 e5
    rw [hnormv, hnormv]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_six]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, g]
    have h1 : x 1 = x 4 + (-991 / 2694 - 767 / 2694) := by linarith
    have h2 : x 2 = x 4 + (-991 / 2694 - 767 / 2694) := by linarith
    have h0 : x 0 = x 4 + (227 / 2694 - 767 / 2694) := by linarith
    have h3 : x 3 = x 4 + (329 / 2694 - 767 / 2694) := by linarith
    have h5 : x 5 = x 4 + (659 / 2694 - 767 / 2694) := by linarith
    rw [h0, h1, h2, h3, h5]
    nlinarith [sq_nonneg (x 4 - 767 / 2694)]
  have hconn : WeaklyConnected A := by
    have adj : ∀ i j : Fin 6, 0 < A i j →
        (SimpleGraph.fromRel fun i j : Fin 6 => 0 < A i j).Adj i j :=
      fun i j hij => by
        rw [SimpleGraph.fromRel_adj]
        refine ⟨fun hne => ?_, Or.inl hij⟩
        subst hne; rw [hdiag] at hij; exact lt_irrefl _ hij
    have r : ∀ i j : Fin 6, 0 < A i j →
        (SimpleGraph.fromRel fun i j : Fin 6 => 0 < A i j).Reachable i j :=
      fun i j hij => (adj i j hij).reachable
    have r03 := r 0 3 (by simp [A])
    have r04 := r 0 4 (by simp [A])
    have r41 := r 4 1 (by simp [A])
    have r42 := r 4 2 (by simp [A])
    have r40 := r 4 0 (by simp [A])
    have r05 : (SimpleGraph.fromRel fun i j : Fin 6 => 0 < A i j).Reachable 0 5 :=
      (r 5 0 (by simp [A])).symm
    refine ⟨fun i j => ?_⟩
    have hall : ∀ k : Fin 6, (SimpleGraph.fromRel fun i j : Fin 6 => 0 < A i j).Reachable 0 k := by
      intro k
      fin_cases k
      · exact SimpleGraph.Reachable.refl _
      · exact r04.trans r41
      · exact r04.trans r42
      · exact r03
      · exact r04
      · exact r05
    exact (hall i).symm.trans (hall j)
  have hval : forwardDemocracy A g = 901 / 898 := by
    simp [forwardDemocracy, A, g, Fin.sum_univ_six]
    norm_num
  have := h 6 A hnn hdiag hconn g hlev
  rw [hval] at this
  norm_num at this

end D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
