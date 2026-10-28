/- GID: D5/S3/Quantum/LaPianaGraphQuantumMagicSquares
   generality: I
   mirror-B: D5/B/S3/Quantum/LaPianaGraphQuantumMagicSquares
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The C5 graph quantum magic squares strictly contain the permutation hull. -/

/-
admission_basis: open-problem-resolution (#19303; Proved)
escape_witness: none
proof_shape: IsQMS: bind-only; consumers: IsGraphQMS
Direct frozen dependencies: IsQMS: none
proof_shape: IsGraphQMS: bind-only; consumers: M, P, cycle_relation, commute_propagation
Direct frozen dependencies: IsGraphQMS: none
proof_shape: M: bind-only; consumers: claim, matrix_convex_M, hull_subset_M, witness_mem_M
Direct frozen dependencies: M: none
proof_shape: P: bind-only; consumers: claim, hull_subset_M, projection_of_P, row_orthogonal_P, first_rows_support, first_rows_offdiagonal, first_rows_commute, entries_commute, P_dihedral, hull_dihedral
Direct frozen dependencies: P: none
proof_shape: IsMatrixConvex: bind-only; consumers: mconv, matrix_convex_M, matrix_convex_dihedral
Direct frozen dependencies: IsMatrixConvex: none
proof_shape: mconv: bind-only; consumers: claim, hull_subset_M, hull_dihedral
Direct frozen dependencies: mconv: none
proof_shape: claim: bind-only; consumers: result
Direct frozen dependencies: claim: none
proof_shape: matrix_convex_M: bind-only; consumers: hull_subset_M
Direct frozen dependencies: matrix_convex_M: none
proof_shape: hull_subset_M: bind-only; consumers: result
Direct frozen dependencies: hull_subset_M: none
proof_shape: row_orthogonal: bind-only; consumers: row_orthogonal_P
Direct frozen dependencies: row_orthogonal: none
proof_shape: projection_of_P: bind-only; consumers: row_orthogonal_P, first_rows_support, P_dihedral
Direct frozen dependencies: projection_of_P: none
proof_shape: row_orthogonal_P: bind-only; consumers: first_rows_support, first_rows_offdiagonal, entries_commute, P_dihedral
Direct frozen dependencies: row_orthogonal_P: none
proof_shape: cycle_neighbors: bind-only; consumers: cycle_relation, witness_mem_M
Direct frozen dependencies: cycle_neighbors: none
proof_shape: cycle_neighbors_distinct: bind-only; consumers: cycle_relation, first_rows_support, P_dihedral, witness_mem_M
Direct frozen dependencies: cycle_neighbors_distinct: none
proof_shape: cycle_relation: bind-only; consumers: first_rows_support, commute_propagation, P_dihedral
Direct frozen dependencies: cycle_relation: none
proof_shape: first_rows_support: bind-only; consumers: first_rows_offdiagonal, P_dihedral
Direct frozen dependencies: first_rows_support: none
proof_shape: common_neighbor_unique: bind-only; consumers: first_rows_offdiagonal
Direct frozen dependencies: common_neighbor_unique: none
proof_shape: first_rows_offdiagonal: bind-only; consumers: first_rows_commute
Direct frozen dependencies: first_rows_offdiagonal: none
proof_shape: first_rows_commute: bind-only; consumers: entries_commute
Direct frozen dependencies: first_rows_commute: none
proof_shape: commute_propagation: bind-only; consumers: entries_commute
Direct frozen dependencies: commute_propagation: none
proof_shape: entries_commute: bind-only; consumers: P_dihedral
Direct frozen dependencies: entries_commute: none
proof_shape: IsDihedral: bind-only; consumers: P_dihedral, matrix_convex_dihedral, hull_dihedral, witness_not_dihedral
Direct frozen dependencies: IsDihedral: none
proof_shape: neighbor_symm: bind-only; consumers: P_dihedral
Direct frozen dependencies: neighbor_symm: none
proof_shape: P_dihedral: content; consumers: hull_dihedral
Direct frozen dependencies: P_dihedral: none
proof_shape: matrix_convex_dihedral: bind-only; consumers: hull_dihedral
Direct frozen dependencies: matrix_convex_dihedral: none
proof_shape: hull_dihedral: content; consumers: result
Direct frozen dependencies: hull_dihedral: none
proof_shape: aval: bind-only; consumers: numerator, numerator_psd, witness_mem_M, witness_not_dihedral
Direct frozen dependencies: aval: none
proof_shape: bval: bind-only; consumers: numerator, numerator_psd, witness_mem_M, witness_not_dihedral
Direct frozen dependencies: bval: none
proof_shape: numerator: bind-only; consumers: F, numerator_psd, witness_mem_M, witness_not_dihedral
Direct frozen dependencies: numerator: none
proof_shape: F: bind-only; consumers: witness, witness_mem_M, witness_not_dihedral
Direct frozen dependencies: F: none
proof_shape: witness: bind-only; consumers: witness_mem_M, witness_not_dihedral, result
Direct frozen dependencies: witness: none
proof_shape: numerator_psd: bind-only; consumers: witness_mem_M
Direct frozen dependencies: numerator_psd: none
proof_shape: witness_mem_M: bind-only; consumers: result
Direct frozen dependencies: witness_mem_M: none
proof_shape: positive_summand_kernel: bind-only; consumers: witness_not_dihedral
Direct frozen dependencies: positive_summand_kernel: K1
proof_shape: zero_of_two_kernels: bind-only; consumers: witness_not_dihedral
Direct frozen dependencies: zero_of_two_kernels: none
proof_shape: witness_not_dihedral: bind-only; consumers: result
Direct frozen dependencies: witness_not_dihedral: K1
proof_shape: result: content; consumers: settling result
Direct frozen dependencies: result: K1
K1: owner GID: D5/S3/Quantum/Measurement/AntidistinguishabilityGram
  declaration: D5.S3.Quantum.Measurement.AntidistinguishabilityGram.psd_summand_kills_kernel
  baseline private declaration statement_id: sha256:29aff5e7fc0604a3cc45e6eb9d34e66bc3fa4f8c521ba7ad954e527b5ccb265d
The public claim uses the matrix-convex and graph magic relations of arXiv:2512.08797v3.
External and internal indices use Fin n and Fin s; the harmless zero-size level is included.
The block-matrix type is written directly, without a forwarding type definition.
The general odd-cycle claim is not asserted here.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19372.
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace D5.S3.Quantum.LaPianaGraphQuantumMagicSquares

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

/-! Binding conventions for F. La Piana, "Graph Quantum Magic Squares and Free Spectrahedra", arXiv:2512.08797v3:
quantum magic squares (Definition 2.1), matrix convexity and the matrix convex hull (Definition 2.3), graph quantum
magic squares and graph quantum permutation matrices (Definitions 3.1–3.2), Question 1.3 and the conjectured strict
inclusion mconv(P^(Γ)) ⊊ M^(Γ) of Section 4.1 for the named candidate Γ = C₅. -/

/-- Definition 2.1: every block is positive semidefinite and every row and column sums to `I_s`. -/
def IsQMS {n s : ℕ} (A : (Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ)) : Prop :=
  (∀ i j, (A i j).PosSemidef) ∧ (∀ i, ∑ k, A i k = 1) ∧ (∀ j, ∑ k, A k j = 1)

/-- Definition 3.1 in block form: `Σ_{k∼j} X_ik = Σ_{k∼i} X_kj` for all `i, j`. -/
def IsGraphQMS {n s : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : (Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ)) : Prop :=
  IsQMS X ∧ ∀ i j, ∑ k ∈ Finset.univ.filter (G.Adj · j), X i k = ∑ k ∈ Finset.univ.filter (G.Adj · i), X k j

/-- Definition 3.2: `M^(Γ)_s`. -/
def M {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ) : Set ((Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ)) :=
  {X | IsGraphQMS G X}

/-- Definition 3.2: `P^(Γ)_s`, the graph quantum permutation matrices, `X_ij² = X_ij = X_ij*`. -/
def P {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ) : Set ((Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ)) :=
  {X | IsGraphQMS G X ∧ ∀ i j, X i j * X i j = X i j ∧ (X i j)ᴴ = X i j}

/-- Definition 2.3: a family `{R_s}` is matrix convex if it is closed under `Σ_i V_i* A^(i) V_i` (blockwise) for
`A^(i) ∈ R_{s_i}`, `V_i ∈ Mat_{s_i, t}(ℂ)` and `Σ_i V_i* V_i = I_t`. -/
def IsMatrixConvex {n : ℕ} (R : (s : ℕ) → Set ((Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ))) : Prop :=
  ∀ (k : ℕ) (sz : Fin k → ℕ) (A : (l : Fin k) → (Fin n → Fin n → Matrix (Fin (sz l)) (Fin (sz l)) ℂ)), (∀ l, A l ∈ R (sz l)) →
    ∀ (t : ℕ) (V : (l : Fin k) → Matrix (Fin (sz l)) (Fin t) ℂ), ∑ l, (V l)ᴴ * V l = 1 →
      (fun i j => ∑ l, (V l)ᴴ * A l i j * V l) ∈ R t

/-- Definition 2.3: `mconv(S)`, the smallest matrix convex family containing `S`. -/
def mconv {n : ℕ} (S : (s : ℕ) → Set ((Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ))) (s : ℕ) : Set ((Fin n → Fin n → Matrix (Fin s) (Fin s) ℂ)) :=
  {X | ∀ R : (t : ℕ) → Set ((Fin n → Fin n → Matrix (Fin t) (Fin t) ℂ)), IsMatrixConvex R → (∀ t, S t ⊆ R t) → X ∈ R s}

/-- Section 4.1 for `Γ = C₅`: `mconv(P^(C₅)) ⊊ M^(C₅)`, i.e. the hull is contained in `M^(C₅)` at every internal size and
some graph quantum magic square of `C₅` lies outside it. -/
def claim : Prop :=
  (∀ s, mconv (P (SimpleGraph.cycleGraph 5)) s ⊆ M (SimpleGraph.cycleGraph 5) s) ∧
    ∃ s, ∃ X ∈ M (SimpleGraph.cycleGraph 5) s, X ∉ mconv (P (SimpleGraph.cycleGraph 5)) s

private theorem matrix_convex_M {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsMatrixConvex (M G) := by
  intro k sz A hA t V hV
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    exact posSemidef_sum _ (fun l _ => ((hA l).1.1 i j).conjTranspose_mul_mul_same (V l))
  · intro i
    rw [Finset.sum_comm]
    simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum, (hA _).1.2.1 i, Matrix.mul_one]
    exact hV
  · intro j
    rw [Finset.sum_comm]
    simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum, (hA _).1.2.2 j, Matrix.mul_one]
    exact hV
  · intro i j
    dsimp only
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    rw [(hA l).2 i j]

private theorem hull_subset_M {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ) :
    mconv (P G) s ⊆ M G s := by
  intro X hX
  exact hX (M G) (matrix_convex_M G) (fun _ _ h => h.1)

private theorem row_orthogonal {s : ℕ} (p : Fin 5 → Matrix (Fin s) (Fin s) ℂ)
    (hp : ∀ a, IsStarProjection (p a)) (hs : ∑ a, p a = 1) (a b : Fin 5) (hab : a ≠ b) :
    p a * p b = 0 := by
  have hle : p a ≤ 1 - p b := by
    calc
      p a ≤ ∑ k ∈ Finset.univ.erase b, p k :=
        Finset.single_le_sum (fun k _ => (hp k).nonneg) (by simp [hab])
      _ = 1 - p b := eq_sub_of_add_eq ((Finset.sum_erase_add _ _ (Finset.mem_univ b)).trans hs)
  have hmul := ((hp a).le_iff_mul_eq_left (hp b).one_sub).mp hle
  simpa only [mul_sub, mul_one, sub_eq_self] using hmul

private theorem projection_of_P {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (i j : Fin 5) : IsStarProjection (X i j) :=
  ⟨(hX.2 i j).1, (hX.2 i j).2⟩

private theorem row_orthogonal_P {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (i a b : Fin 5) (hab : a ≠ b) :
    X i a * X i b = 0 :=
  row_orthogonal (X i) (projection_of_P hX i) (hX.1.1.2.1 i) a b hab

private theorem cycle_neighbors (a : Fin 5) :
    Finset.univ.filter ((SimpleGraph.cycleGraph 5).Adj · a) = {a-1,a+1} := by
  simpa only [SimpleGraph.neighborFinset_eq_filter, SimpleGraph.adj_comm] using
    (SimpleGraph.cycleGraph_neighborFinset (n := 3) (v := a))

private theorem cycle_neighbors_distinct (a : Fin 5) : a-1 ≠ a+1 := by
  apply Finset.card_pair_eq_two_iff.mp
  rw [← SimpleGraph.cycleGraph_neighborFinset, ← SimpleGraph.degree]
  exact SimpleGraph.cycleGraph_degree_three_le

private theorem cycle_relation {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : IsGraphQMS (SimpleGraph.cycleGraph 5) X) (i j : Fin 5) :
    X i (j-1) + X i (j+1) = X (i-1) j + X (i+1) j := by
  have h := hX.2 i j
  simpa only [cycle_neighbors, Finset.sum_pair (cycle_neighbors_distinct j), Finset.sum_pair (cycle_neighbors_distinct i)] using h

private theorem first_rows_support {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (a b : Fin 5)
    (ha : a ≠ b-1 ∧ a ≠ b+1) : X 0 a * X 1 b = 0 := by
  let e := X 0 (b-1) + X 0 (b+1)
  have he : IsStarProjection e := (projection_of_P hX 0 (b-1)).add
    (projection_of_P hX 0 (b+1)) (row_orthogonal_P hX 0 _ _ (cycle_neighbors_distinct b))
  have hle : X 1 b ≤ e := by
    have hr := cycle_relation hX.1 0 b
    change e = X 4 b + X 1 b at hr
    rw [hr]
    exact le_add_of_nonneg_left (hX.1.1.1 4 b).nonneg
  have hmul := ((projection_of_P hX 1 b).le_iff_mul_eq_right he).mp hle
  calc
    X 0 a * X 1 b = X 0 a * (e * X 1 b) := by rw [hmul]
    _ = 0 := by
      rw [← Matrix.mul_assoc]
      dsimp only [e]
      rw [Matrix.mul_add, row_orthogonal_P hX 0 _ _ ha.1,
        row_orthogonal_P hX 0 _ _ ha.2, add_zero, Matrix.zero_mul]

private theorem common_neighbor_unique : ∀ a c b l : Fin 5, a ≠ c →
    (a = b-1 ∨ a = b+1) → (c = b-1 ∨ c = b+1) →
    (a = l-1 ∨ a = l+1) → (c = l-1 ∨ c = l+1) → b = l := by decide

private theorem first_rows_offdiagonal {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (a c b : Fin 5) (hac : a ≠ c) :
    X 0 a * X 1 b * X 0 c = 0 := by
  have left_zero (l : Fin 5) (ha : a ≠ l-1 ∧ a ≠ l+1) :
      X 0 a * X 1 l * X 0 c = 0 := by rw [first_rows_support hX a l ha, Matrix.zero_mul]
  have right_zero (l : Fin 5) (hc : c ≠ l-1 ∧ c ≠ l+1) :
      X 0 a * X 1 l * X 0 c = 0 := by
    have h := congrArg Matrix.conjTranspose (first_rows_support hX c l hc)
    simp only [Matrix.conjTranspose_mul, (hX.2 0 c).2, (hX.2 1 l).2,
      Matrix.conjTranspose_zero] at h
    rw [Matrix.mul_assoc, h, Matrix.mul_zero]
  by_cases ha : a = b-1 ∨ a = b+1
  · by_cases hc : c = b-1 ∨ c = b+1
    · have hall : ∑ l, X 0 a * X 1 l * X 0 c = 0 := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, hX.1.1.2.1 1,
          Matrix.mul_one, row_orthogonal_P hX 0 a c hac]
      have hsingle : ∑ l, X 0 a * X 1 l * X 0 c = X 0 a * X 1 b * X 0 c := by
        apply Finset.sum_eq_single b
        · intro l _ hl
          by_cases hal : a = l-1 ∨ a = l+1
          · have hcl : ¬(c = l-1 ∨ c = l+1) := fun h => hl (common_neighbor_unique a c b l hac ha hc hal h).symm
            exact right_zero l (not_or.mp hcl)
          · exact left_zero l (not_or.mp hal)
        · simp
      exact hsingle.symm.trans hall
    · exact right_zero b (not_or.mp hc)
  · exact left_zero b (not_or.mp ha)

private theorem first_rows_commute {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (a b : Fin 5) :
    X 0 a * X 1 b = X 1 b * X 0 a := by
  have hd : X 0 a * X 1 b = X 0 a * X 1 b * X 0 a := by
    calc
      X 0 a * X 1 b = X 0 a * X 1 b * (∑ c, X 0 c) := by rw [hX.1.1.2.1 0, Matrix.mul_one]
      _ = ∑ c, X 0 a * X 1 b * X 0 c := Matrix.mul_sum _ _ _
      _ = X 0 a * X 1 b * X 0 a := by
        apply Finset.sum_eq_single a
        · intro c _ hc
          exact first_rows_offdiagonal hX a c b hc.symm
        · simp
  have hs := congrArg Matrix.conjTranspose hd
  simp only [Matrix.conjTranspose_mul, (hX.2 0 a).2, (hX.2 1 b).2] at hs
  calc
    X 0 a * X 1 b = X 0 a * X 1 b * X 0 a := hd
    _ = X 0 a * (X 1 b * X 0 a) := Matrix.mul_assoc _ _ _
    _ = X 1 b * X 0 a := hs.symm

private theorem commute_propagation {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : IsGraphQMS (SimpleGraph.cycleGraph 5) X) (z : Matrix (Fin s) (Fin s) ℂ)
    (h0 : ∀ j, Commute (X 0 j) z) (h1 : ∀ j, Commute (X 1 j) z) :
    ∀ i j, Commute (X i j) z := by
  have step (i : Fin 5) (hp : ∀ j, Commute (X (i-1) j) z) (hc : ∀ j, Commute (X i j) z) :
      ∀ j, Commute (X (i+1) j) z := by
    intro j
    have he : X (i+1) j = X i (j-1) + X i (j+1) - X (i-1) j := by
      apply eq_sub_of_add_eq
      rw [add_comm]
      exact (cycle_relation hX i j).symm
    rw [he]
    exact ((hc (j-1)).add_left (hc (j+1))).sub_left (hp j)
  have h2 := step 1 h0 h1
  have h3 := step 2 h1 h2
  have h4 := step 3 h2 h3
  intro i j
  fin_cases i
  · exact h0 j
  · exact h1 j
  · exact h2 j
  · exact h3 j
  · exact h4 j

private theorem entries_commute {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) (i j k l : Fin 5) :
    X i j * X k l = X k l * X i j := by
  have same (r a b : Fin 5) : Commute (X r a) (X r b) := by
    by_cases h : a = b
    · subst b; exact Commute.refl _
    · show X r a * X r b = X r b * X r a
      rw [row_orthogonal_P hX r a b h, row_orthogonal_P hX r b a (Ne.symm h)]
  have h0 (a : Fin 5) : ∀ i j, Commute (X i j) (X 0 a) :=
    commute_propagation hX.1 (X 0 a) (same 0 · a)
      (fun b => (show Commute (X 0 a) (X 1 b) from first_rows_commute hX a b).symm)
  have h1 (b : Fin 5) : ∀ i j, Commute (X i j) (X 1 b) :=
    commute_propagation hX.1 (X 1 b)
      (fun a => first_rows_commute hX a b) (same 1 · b)
  exact (commute_propagation hX.1 (X k l)
    (fun a => (h0 a k l).symm) (fun b => (h1 b k l).symm) i j).eq

private def IsDihedral {s : ℕ} (X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)) : Prop :=
  ∃ R S : Fin 5 → Matrix (Fin s) (Fin s) ℂ,
    (∀ r, (R r).PosSemidef) ∧ (∀ r, (S r).PosSemidef) ∧
    ∀ i j, X i j = R (i-j) + S (i+j)

private theorem neighbor_symm : ∀ a b : Fin 5,
    (a = b-1 ∨ a = b+1) ↔ (b = a-1 ∨ b = a+1) := by decide

private theorem P_dihedral {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ P (SimpleGraph.cycleGraph 5) s) : IsDihedral X := by
  let R : Fin 5 → Matrix (Fin s) (Fin s) ℂ := fun r => X 0 (-r) * X 1 (1-r)
  let S : Fin 5 → Matrix (Fin s) (Fin s) ℂ := fun r => X 0 r * X 1 (r-1)
  let Y : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ) := fun i j => R (i-j) + S (i+j)
  have hpos (a b : Fin 5) : (X 0 a * X 1 b).PosSemidef := by
    exact ((projection_of_P hX 0 a).mul (projection_of_P hX 1 b)
      (entries_commute hX 0 a 1 b)).nonneg.posSemidef
  have hrow0 : ∀ j, X 0 j = Y 0 j := by
    intro j
    have hs : X 0 j = ∑ b, X 0 j * X 1 b := by rw [← Matrix.mul_sum, hX.1.1.2.1 1, Matrix.mul_one]
    have hcut : ∑ b, X 0 j * X 1 b = ∑ b ∈ ({j-1,j+1} : Finset (Fin 5)), X 0 j * X 1 b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      apply first_rows_support hX j b
      have hh : ¬ (b = j-1 ∨ b = j+1) := by simpa using hb
      exact not_or.mp (fun h => hh ((neighbor_symm j b).mp h))
    rw [hcut, Finset.sum_pair (cycle_neighbors_distinct j)] at hs
    have hiAll : ∀ j : Fin 5, -(0-j) = j ∧ 1-(0-j) = j+1 ∧ 0+j = j ∧ (0+j)-1 = j-1 := by decide
    have hi := hiAll j
    have hy : Y 0 j = X 0 j * X 1 (j+1) + X 0 j * X 1 (j-1) := by
      dsimp only [Y, R, S]
      rw [hi.1, hi.2.1, hi.2.2.2, hi.2.2.1]
    rw [hy]
    exact hs.trans (add_comm _ _)
  have hrow1 : ∀ j, X 1 j = Y 1 j := by
    intro j
    let e := X 0 (j-1) + X 0 (j+1)
    have he : IsStarProjection e := (projection_of_P hX 0 (j-1)).add
      (projection_of_P hX 0 (j+1)) (row_orthogonal_P hX 0 _ _ (cycle_neighbors_distinct j))
    have hle : X 1 j ≤ e := by
      have hr := cycle_relation hX.1 0 j
      change e = X 4 j + X 1 j at hr
      rw [hr]
      exact le_add_of_nonneg_left (hX.1.1.1 4 j).nonneg
    have hm := ((projection_of_P hX 1 j).le_iff_mul_eq_right he).mp hle
    have hh : e * X 1 j = Y 1 j := by
      dsimp only [e]
      rw [Matrix.add_mul]
      have hiAll : ∀ j : Fin 5, -(1-j) = j-1 ∧ 1-(1-j) = j ∧ 1+j = j+1 ∧ (1+j)-1 = j := by decide
      have hi := hiAll j
      dsimp only [Y, R, S]
      rw [hi.1, hi.2.1, hi.2.2.2, hi.2.2.1]
    exact hm.symm.trans hh
  have hY : ∀ i j, Y i (j-1) + Y i (j+1) = Y (i-1) j + Y (i+1) j := by
    intro i j
    have hind : (i-(j-1) = (i+1)-j) ∧ (i+(j-1) = (i-1)+j) ∧
        (i-(j+1) = (i-1)-j) ∧ (i+(j+1) = (i+1)+j) := by
      revert i j
      decide
    dsimp only [Y]
    rw [hind.1, hind.2.1, hind.2.2.1, hind.2.2.2]
    abel
  have step (i : Fin 5) (hp : ∀ j, X (i-1) j = Y (i-1) j) (hc : ∀ j, X i j = Y i j) :
      ∀ j, X (i+1) j = Y (i+1) j := by
    intro j
    have hh := cycle_relation hX.1 i j
    rw [hp j, hc (j-1), hc (j+1)] at hh
    exact add_left_cancel (hh.symm.trans (hY i j))
  have hrow2 := step 1 hrow0 hrow1
  have hrow3 := step 2 hrow1 hrow2
  have hrow4 := step 3 hrow2 hrow3
  refine ⟨R, S, fun r => hpos _ _, fun r => hpos _ _, ?_⟩
  intro i j
  fin_cases i
  · exact hrow0 j
  · exact hrow1 j
  · exact hrow2 j
  · exact hrow3 j
  · exact hrow4 j

private theorem matrix_convex_dihedral : IsMatrixConvex (fun s => {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ) | IsDihedral X}) := by
  intro k sz A hA t V hV
  choose R S hR hS hform using hA
  refine ⟨fun r => ∑ l, (V l)ᴴ * R l r * V l, fun r => ∑ l, (V l)ᴴ * S l r * V l, ?_, ?_, ?_⟩
  · intro r
    exact posSemidef_sum _ (fun l _ => (hR l r).conjTranspose_mul_mul_same (V l))
  · intro r
    exact posSemidef_sum _ (fun l _ => (hS l r).conjTranspose_mul_mul_same (V l))
  · intro i j
    simp_rw [hform, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

private theorem hull_dihedral {s : ℕ} {X : (Fin 5 → Fin 5 → Matrix (Fin s) (Fin s) ℂ)}
    (hX : X ∈ mconv (P (SimpleGraph.cycleGraph 5)) s) : IsDihedral X := by
  exact hX _ matrix_convex_dihedral (fun _ _ h => P_dihedral h)

private def aval : Fin 5 → ℝ := ![3,-3,0,0,0]
private def bval : Fin 5 → ℝ := ![4,-4,0,0,0]
private def numerator (r c : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((5 + aval r : ℝ) : ℂ), (bval c : ℂ); (bval c : ℂ), ((5 - aval r : ℝ) : ℂ)]
private noncomputable def F (r c : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ := (1/25 : ℝ) • numerator r c

private noncomputable def witness : (Fin 5 → Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) := fun i j => F (i-j) (i+j)

private theorem numerator_psd (r c : Fin 5) : (numerator r c).PosSemidef := by
  let v : Fin 2 → ℂ := ![((5 + aval r : ℝ) : ℂ), (bval c : ℂ)]
  have he : numerator r c = (1/(5+aval r) : ℝ) • vecMulVec v (star v) +
      diagonal ![(0 : ℂ), (((25-(aval r)^2-(bval c)^2)/(5+aval r) : ℝ) : ℂ)] := by
    ext i j
    fin_cases r <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
      norm_num [numerator, v, aval, bval, vecMulVec_apply, diagonal_apply,
        Matrix.smul_apply, Complex.real_smul, Pi.star_apply, -cons_vecMulVec, -vecMulVec_cons]
  rw [he]
  apply PosSemidef.add
  · apply (posSemidef_vecMulVec_self_star v).smul
    fin_cases r <;> norm_num [aval]
  · apply PosSemidef.diagonal
    intro i
    fin_cases i <;> fin_cases r <;> fin_cases c <;> norm_num [aval, bval, Complex.nonneg_iff]

private theorem witness_mem_M : witness ∈ M (SimpleGraph.cycleGraph 5) 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    exact (numerator_psd _ _).smul (by norm_num : (0 : ℝ) ≤ 1/25)
  · intro i
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      norm_num [witness, F, numerator, aval, bval, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.smul_apply, Complex.real_smul, Matrix.one_apply]
  · intro j
    ext a b
    fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [witness, F, numerator, aval, bval, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.smul_apply, Complex.real_smul, Matrix.one_apply]
  · intro i j
    rw [cycle_neighbors j, cycle_neighbors i, Finset.sum_pair (cycle_neighbors_distinct j), Finset.sum_pair (cycle_neighbors_distinct i)]
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [witness, F, numerator, aval, bval, Matrix.smul_apply, Complex.real_smul,
        Fin.neg_def, Fin.sub_def, Fin.add_def]

private theorem positive_summand_kernel {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (v : Fin 2 → ℂ)
    (hz : (A+B) *ᵥ v = 0) : A *ᵥ v = 0 := by
  have hp : ∀ i : Fin 2, (![A,B] i).PosSemidef := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  have hs : (∑ i : Fin 2, ![A,B] i) *ᵥ v = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hz
  exact D5.S3.Quantum.Measurement.AntidistinguishabilityGram.psd_summand_kills_kernel ![A,B] hp v hs 0

private theorem zero_of_two_kernels {A : Matrix (Fin 2) (Fin 2) ℂ} (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hm : A *ᵥ ![u,-v] = 0) (hp : A *ᵥ ![u,v] = 0) : A = 0 := by
  ext i j
  have h1 := congrFun hm i
  have h2 := congrFun hp i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at h1 h2
  have h0 : A i 0 * u = 0 := by
    exact add_self_eq_zero.mp (by
      simpa only [← sub_eq_zero.mp (by simpa only [mul_neg, ← sub_eq_add_neg] using h1)] using h2)
  have h3 : A i 1 * v = 0 := by exact (eq_zero_iff_eq_zero_of_add_eq_zero h2).mp h0
  fin_cases j
  · exact (mul_eq_zero.mp h0).resolve_right hu
  · exact (mul_eq_zero.mp h3).resolve_right hv

private theorem witness_not_dihedral : ¬ IsDihedral witness := by
  rintro ⟨R,S,hR,hS,h⟩
  have hf : ∀ r c, R r + S c = F r c := by
    intro r c
    have hh := h (3*(r+c)) (3*(c-r))
    change F (3*(r+c)-3*(c-r)) (3*(r+c)+3*(c-r)) =
      R (3*(r+c)-3*(c-r)) + S (3*(r+c)+3*(c-r)) at hh
    have hidx : 3*(r+c)-3*(c-r) = r ∧ 3*(r+c)+3*(c-r) = c := by
      fin_cases r <;> fin_cases c <;> decide
    rw [hidx.1,hidx.2] at hh
    exact hh.symm
  have hzero0 : R 0 = 0 := by
    apply zero_of_two_kernels 1 2 (by norm_num) (by norm_num)
    · apply positive_summand_kernel (hR 0) (hS 0)
      rw [hf]
      ext i
      fin_cases i <;> norm_num [F,numerator,aval,bval,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Matrix.smul_apply,Complex.real_smul]
    · apply positive_summand_kernel (hR 0) (hS 1)
      rw [hf]
      ext i
      fin_cases i <;> norm_num [F,numerator,aval,bval,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Matrix.smul_apply,Complex.real_smul]
  have hzero1 : R 1 = 0 := by
    apply zero_of_two_kernels 2 1 (by norm_num) (by norm_num)
    · apply positive_summand_kernel (hR 1) (hS 0)
      rw [hf]
      ext i
      fin_cases i <;> norm_num [F,numerator,aval,bval,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Matrix.smul_apply,Complex.real_smul]
    · apply positive_summand_kernel (hR 1) (hS 1)
      rw [hf]
      ext i
      fin_cases i <;> norm_num [F,numerator,aval,bval,Matrix.mulVec,dotProduct,
        Fin.sum_univ_two,Matrix.smul_apply,Complex.real_smul]
  have he : F 0 0 = F 1 0 := by
    rw [← hf 0 0, ← hf 1 0, hzero0, hzero1]
  have hv := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).re) he
  norm_num [F,numerator,aval,bval,Matrix.smul_apply,Complex.real_smul] at hv

theorem result : claim := by
  refine ⟨hull_subset_M _, 2, witness, witness_mem_M, ?_⟩
  intro h
  exact witness_not_dihedral (hull_dihedral h)

end D5.S3.Quantum.LaPianaGraphQuantumMagicSquares
