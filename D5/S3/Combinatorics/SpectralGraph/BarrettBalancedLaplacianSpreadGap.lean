/- GID: D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Balanced digraphs have no Laplacian spread strictly between zero and one. -/

/-
proof_shape: all theorem declarations: bind-only.
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22040
admission_basis: open-problem-resolution (#21873; Proved)
Direct frozen dependencies (declaration statement_id):
  D5/S1/Dynamics/Symbolic/FiniteGraphEntropy.adjacency: sha256:333274b8af876930296e18e1a33684b7a225e27fb0b15298aee0f7a8ed138cd0
  D5/S3/Weil/ZetaLinear/PosIndex.frobSq: sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116
  D5/S3/Weil/ZetaLinear/PosIndex.frobSq_hermitian_eq_sum_sq_eigenvalues: sha256:8517f9a9ec34b3ab0b7f30f5025ab007ce87f585c396c39fa4b953498c3fd325
Declaration classification and consumers:
  claim: definition; consumers: result
  quadratic_bounds: bind-only; consumers: degree_rayleigh_bounds, symAdj_centered_bound, symAdj_pair_bounds
  mulVec_const: bind-only; consumers: quad_sub_const_of_zero_sums
  const_dot_mulVec: bind-only; consumers: quad_sub_const_of_zero_sums
  quad_sub_const_of_zero_sums: bind-only; consumers: centered_full_bound, quad_single_of_zero_sums
  projected_sum: bind-only; consumers: centered_full_bound, projected_single
  projected_norm: bind-only; consumers: centered_full_bound, projected_single
  projected_single: bind-only; consumers: degree_rayleigh_bounds
  quad_single_of_zero_sums: bind-only; consumers: degree_rayleigh_bounds
  laplacian_row_sum: bind-only; consumers: degree_rayleigh_bounds
  laplacian_col_sum: bind-only; consumers: degree_rayleigh_bounds
  laplacian_diag: bind-only; consumers: degree_rayleigh_bounds
  outDegree_nat: bind-only; consumers: regular_of_spread_le_one, result
  degree_rayleigh_bounds: bind-only; consumers: regular_of_spread_le_one
  regular_of_spread_le_one: bind-only; consumers: result
  pair_sum_norm: bind-only; consumers: matching_bound_impossible, quadraticValues_nonempty, symAdj_pair_bounds
  pair_quad: bind-only; consumers: matching_bound_impossible, symAdj_pair_bounds
  quadraticValues_nonempty: bind-only; consumers: extrema_attained
  extrema_attained: bind-only; consumers: spread_zero_of_scalar
  symAdj: definition; consumers: laplacian_symAdj_quad, result, symAdj_centered_bound, symAdj_diag, symAdj_entries, symAdj_entry_dichotomy, symAdj_hermitian, symAdj_pair_bounds, symAdj_rows, symAdj_scalar_implies_zero
  symAdj_hermitian: bind-only; consumers: result
  symAdj_entries: bind-only; consumers: symAdj_entry_dichotomy
  symAdj_diag: bind-only; consumers: result, symAdj_entry_dichotomy
  symAdj_rows: bind-only; consumers: result
  laplacian_symAdj_quad: bind-only; consumers: symAdj_centered_bound, symAdj_scalar_implies_zero
  symAdj_pair_bounds: bind-only; consumers: symAdj_entry_dichotomy
  symAdj_entry_dichotomy: bind-only; consumers: result
  symAdj_centered_bound: bind-only; consumers: result
  interior_scalar_contradiction: bind-only; consumers: interior_variance_impossible
  frob_bound_of_quad_bound: bind-only; consumers: interior_variance_impossible
  centered: definition; consumers: centered_frob, centered_full_bound, centered_hermitian, centered_quad, centered_row_sum, interior_variance_impossible
  centered_hermitian: bind-only; consumers: centered_frob, centered_full_bound, interior_variance_impossible
  centered_row_sum: bind-only; consumers: centered_full_bound
  centered_quad: bind-only; consumers: centered_full_bound
  centered_full_bound: bind-only; consumers: interior_variance_impossible
  centered_frob: bind-only; consumers: interior_variance_impossible
  interior_variance_impossible: bind-only; consumers: even_regular_narrow_scalar
  unique_one_of_row_one: bind-only; consumers: matching_bound_impossible
  matching_bound_impossible: bind-only; consumers: even_regular_narrow_scalar
  adjacency_complement_sum: bind-only; consumers: complement_quad, complement_rows, even_regular_narrow_scalar
  complete_quad: bind-only; consumers: complement_quad, result, scalar_of_extreme
  complement_quad: bind-only; consumers: even_regular_narrow_scalar
  offDiagonal_sum: bind-only; consumers: complement_rows, degree_le_order_sub_one, result
  complement_rows: bind-only; consumers: even_regular_narrow_scalar
  adj_zero_of_rows_zero: bind-only; consumers: even_regular_narrow_scalar
  adj_regular_of_rows: bind-only; consumers: even_regular_narrow_scalar
  even_regular_narrow_scalar: bind-only; consumers: result
  spread_zero_of_scalar: bind-only; consumers: symAdj_scalar_implies_zero
  degree_le_order_sub_one: bind-only; consumers: result
  symAdj_scalar_implies_zero: bind-only; consumers: result
  scalar_of_extreme: bind-only; consumers: result
  result: bind-only; consumers: settling result
-/

import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation
import D5.S3.Weil.ZetaLinear.PosIndex
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
open Matrix
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.BarrettBalancedLaplacianSpreadGap
open D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation

/-- Conjecture 14 over every order with a nonempty constrained unit sphere. -/
def claim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (Γ : Digraph (Fin n)),
    (∀ i : Fin n, ¬ Γ.Adj i i) →
    Balanced Γ → ¬ (0 < spread Γ ∧ spread Γ < 1)

private lemma quadratic_bounds {n : ℕ} (Γ : Digraph (Fin n)) (x : Fin n → ℝ)
    (hs : ∑ i, x i = 0) :
    alpha Γ * (x ⬝ᵥ x) ≤ (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) ∧
    (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) ≤ beta Γ * (x ⬝ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hd : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (Matrix.dotProduct_star_self_pos_iff (v := x)).mpr hx
  have hm := rayleigh_mem Γ x hs hx
  exact ⟨(le_div_iff₀ hd).mp (csInf_le (quadraticValues_isCompact Γ).bddBelow hm),
    (div_le_iff₀ hd).mp (le_csSup (quadraticValues_isCompact Γ).bddAbove hm)⟩

private lemma mulVec_const {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    A *ᵥ (fun _ => c) = fun i => (∑ j, A i j) * c := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_mul]

private lemma const_dot_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (x : Fin n → ℝ) :
    (fun _ => c) ⬝ᵥ (A *ᵥ x) = c * ∑ j, (∑ i, A i j) * x j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma quad_sub_const_of_zero_sums {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, ∑ j, A i j = 0) (hc : ∀ j, ∑ i, A i j = 0)
    (x : Fin n → ℝ) (c : ℝ) :
    ((x - fun _ => c) ⬝ᵥ (A *ᵥ (x - fun _ => c))) = (x ⬝ᵥ (A *ᵥ x)) := by
  have hz : A *ᵥ (fun _ => c) = 0 := by
    rw [mulVec_const]
    ext i
    simp [hr]
  have hz' : (fun _ => c) ⬝ᵥ (A *ᵥ x) = 0 := by
    simp [const_dot_mulVec, hc]
  simp [Matrix.mulVec_sub, hz, sub_dotProduct, hz']

private lemma projected_sum {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - (∑ j, x j) / n) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [Finset.sum_sub_distrib, hn', mul_div_cancel₀]

private lemma projected_norm {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (fun i => x i - (∑ j, x j) / n) ⬝ᵥ (fun i => x i - (∑ j, x j) / n) =
      x ⬝ᵥ x - (∑ i, x i) ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [dotProduct]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma projected_single {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∑ j : Fin n, ((Pi.single i (1 : ℝ) : Fin n → ℝ) j - 1 / n)) = 0 ∧
    (fun j => (Pi.single i (1 : ℝ) : Fin n → ℝ) j - 1 / n) ⬝ᵥ
      (fun j => (Pi.single i (1 : ℝ) : Fin n → ℝ) j - 1 / n) = (n - 1 : ℝ) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : ∑ j : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) j = 1 := by
    exact Fintype.sum_pi_single' i 1
  have hq : (Pi.single i (1 : ℝ)) ⬝ᵥ Pi.single i (1 : ℝ) = 1 := by simp
  constructor
  · simpa [hs] using projected_sum hn (Pi.single i (1 : ℝ))
  · have h := projected_norm hn (Pi.single i (1 : ℝ))
    rw [hs, hq] at h
    simp only [one_pow] at h
    rw [h]
    field_simp

private lemma quad_single_of_zero_sums {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hr : ∀ i, ∑ j, A i j = 0) (hc : ∀ j, ∑ i, A i j = 0)
    (i : Fin n) (c : ℝ) :
    ((fun j => (Pi.single i (1 : ℝ) : Fin n → ℝ) j - c) ⬝ᵥ (A *ᵥ (fun j => (Pi.single i (1 : ℝ) : Fin n → ℝ) j - c))) = A i i := by
  change (((Pi.single i (1:ℝ) : Fin n → ℝ) - fun _ => c) ⬝ᵥ (A *ᵥ ((Pi.single i (1:ℝ) : Fin n → ℝ) - fun _ => c))) = A i i
  rw [quad_sub_const_of_zero_sums A hr hc]
  simp [Matrix.mulVec_single, single_dotProduct]

private lemma laplacian_row_sum {n : ℕ} (Γ : Digraph (Fin n)) (i : Fin n) :
    ∑ j, laplacian Γ i j = 0 := by
  simp [laplacian, Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.diagonal_apply,
    outDegree]

private lemma laplacian_col_sum {n : ℕ} (Γ : Digraph (Fin n)) (hb : Balanced Γ) (j : Fin n) :
    ∑ i, laplacian Γ i j = 0 := by
  simp [laplacian, Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.diagonal_apply,
    hb j, inDegree]

private lemma laplacian_diag {n : ℕ} (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (i : Fin n) :
    laplacian Γ i i = outDegree Γ i := by
  simp [laplacian, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, hl]

private lemma outDegree_nat {n : ℕ} (Γ : Digraph (Fin n)) (i : Fin n) :
    ∃ d : ℕ, outDegree Γ i = d := by
  classical
  refine ⟨(Finset.univ.filter (Γ.Adj i)).card, ?_⟩
  simp only [outDegree, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency,
    Matrix.map_apply, apply_ite, Nat.cast_one, Nat.cast_zero]
  change (∑ j : Fin n, if Γ.Adj i j then (1:ℝ) else 0) =
    ((Finset.univ.filter (Γ.Adj i)).card : ℝ)
  rw [Finset.card_filter]
  push_cast
  try rfl

private lemma degree_rayleigh_bounds {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (hb : Balanced Γ) (i : Fin n) :
    alpha Γ * ((n - 1 : ℝ) / n) ≤ outDegree Γ i ∧
    outDegree Γ i ≤ beta Γ * ((n - 1 : ℝ) / n) := by
  have hp := projected_single (by omega : 0 < n) i
  have hq := quad_single_of_zero_sums (laplacian Γ)
    (laplacian_row_sum Γ) (laplacian_col_sum Γ hb) i (1 / n)
  have h := quadratic_bounds Γ (fun j => (Pi.single i (1 : ℝ) : Fin n → ℝ) j - 1 / n) hp.1
  rwa [hp.2, hq, laplacian_diag Γ hl i] at h

private lemma regular_of_spread_le_one {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (hb : Balanced Γ) (hw : spread Γ ≤ 1) :
    ∀ i j, outDegree Γ i = outDegree Γ j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : 0 < (n - 1 : ℝ) / n := by
    apply div_pos _ hn0
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk1 : (n - 1 : ℝ) / n < 1 := (div_lt_one hn0).mpr (by linarith)
  have hw' : beta Γ - alpha Γ ≤ 1 := hw
  have diff (i j : Fin n) : outDegree Γ i - outDegree Γ j < 1 := by
    have hi := degree_rayleigh_bounds hn Γ hl hb i
    have hj := degree_rayleigh_bounds hn Γ hl hb j
    have := mul_le_mul_of_nonneg_right hw' hk0.le
    nlinarith
  intro i j
  obtain ⟨di, hdi⟩ := outDegree_nat Γ i
  obtain ⟨dj, hdj⟩ := outDegree_nat Γ j
  have h1 := diff i j
  have h2 := diff j i
  rw [hdi, hdj] at h1 h2 ⊢
  have hij : di ≤ dj := by
    by_contra h
    have h' : dj + 1 ≤ di := by omega
    have h'' : (dj : ℝ) + 1 ≤ di := by exact_mod_cast h'
    linarith
  have hji : dj ≤ di := by
    by_contra h
    have h' : di + 1 ≤ dj := by omega
    have h'' : (di : ℝ) + 1 ≤ dj := by exact_mod_cast h'
    linarith
  exact_mod_cast Nat.le_antisymm hij hji

private lemma pair_sum_norm {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ k, ((Pi.single i (1 : ℝ) : Fin n → ℝ) k - (Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = 0 ∧
    ((Pi.single i (1 : ℝ) : Fin n → ℝ) - (Pi.single j (1 : ℝ) : Fin n → ℝ)) ⬝ᵥ
      ((Pi.single i (1 : ℝ) : Fin n → ℝ) - (Pi.single j (1 : ℝ) : Fin n → ℝ)) = 2 := by
  constructor
  · simp [Finset.sum_sub_distrib]
  · norm_num [sub_dotProduct, dotProduct_sub, hij, Ne.symm hij]

private lemma pair_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((Pi.single i 1 - Pi.single j 1) ⬝ᵥ (A *ᵥ (Pi.single i 1 - Pi.single j 1))) = A i i + A j j - A i j - A j i := by
  simp [Matrix.mulVec_sub, Matrix.mulVec_single, sub_dotProduct,
    dotProduct_sub, single_dotProduct]
  ring

private lemma quadraticValues_nonempty {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n)) :
    (quadraticValues Γ).Nonempty := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by exact not_eq_of_beq_eq_false rfl
  have hp := pair_sum_norm i j hij
  have hx : (Pi.single i (1 : ℝ) : Fin n → ℝ) - (Pi.single j (1 : ℝ) : Fin n → ℝ) ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hij] at this
  exact ⟨_, rayleigh_mem Γ _ hp.1 hx⟩

private lemma extrema_attained {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n)) :
  alpha Γ ∈ quadraticValues Γ ∧ beta Γ ∈ quadraticValues Γ := by
  have hc := quadraticValues_isCompact Γ
  have hne := quadraticValues_nonempty hn Γ
  exact ⟨hc.sInf_mem hne, hc.sSup_mem hne⟩

private abbrev symAdj {n : ℕ} (Γ : Digraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) + (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ))).transpose

private lemma symAdj_hermitian {n : ℕ} (Γ : Digraph (Fin n)) : (symAdj Γ).IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr (Matrix.isSymm_add_transpose_self _)

private lemma symAdj_entries {n : ℕ} (Γ : Digraph (Fin n)) (i j : Fin n) :
    symAdj Γ i j = 0 ∨ symAdj Γ i j = 1 ∨ symAdj Γ i j = 2 := by
  classical
  by_cases h : Γ.Adj i j <;> by_cases h' : Γ.Adj j i <;>
    norm_num [symAdj, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, h, h']

private lemma symAdj_diag {n : ℕ} (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (i : Fin n) : symAdj Γ i i = 0 := by
  simp [symAdj, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, hl]

private lemma symAdj_rows {n : ℕ} (Γ : Digraph (Fin n)) (hb : Balanced Γ)
    (d : ℝ) (hr : ∀ i, outDegree Γ i = d) (i : Fin n) :
    ∑ j, symAdj Γ i j = 2*d := by
  change (∑ j, (((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) i j + ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) j i)) = _
  rw [Finset.sum_add_distrib]
  change outDegree Γ i + inDegree Γ i = _
  rw [← hb i, hr i]
  ring

private lemma laplacian_symAdj_quad {n : ℕ} (Γ : Digraph (Fin n))
    (d : ℝ) (hr : ∀ i, outDegree Γ i = d) (x : Fin n → ℝ) :
    2 * (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) = 2*d*(x ⬝ᵥ x) - (x ⬝ᵥ ((symAdj Γ) *ᵥ x)) := by
  have ht : (x ⬝ᵥ ((((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ))).transpose *ᵥ x)) = (x ⬝ᵥ ((((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ))) *ᵥ x)) :=
    dotProduct_transpose_mulVec _ _ _
  have hd : (x ⬝ᵥ ((Matrix.diagonal (outDegree Γ)) *ᵥ x)) = d*(x ⬝ᵥ x) := by
    simp [Matrix.mulVec_diagonal, hr, dotProduct, ← Finset.mul_sum, mul_assoc,
      mul_comm, mul_left_comm]
  simp only [laplacian, symAdj, Matrix.sub_mulVec, Matrix.add_mulVec,
    dotProduct_sub, dotProduct_add] at hd ht ⊢
  linarith

private lemma symAdj_pair_bounds {n : ℕ} (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (d : ℝ) (hr : ∀ i, outDegree Γ i = d)
    (i j : Fin n) (hij : i ≠ j) :
    2*alpha Γ ≤ 2*d+symAdj Γ i j ∧ 2*d+symAdj Γ i j ≤ 2*beta Γ := by
  have hp := pair_sum_norm i j hij
  let x : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  have h := quadratic_bounds Γ x hp.1
  have hnorm : x ⬝ᵥ x = 2 := hp.2
  have hq : (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) =
      2*d+symAdj Γ i j := by
    dsimp [x]
    rw [pair_quad]
    simp [laplacian_diag Γ hl, hr, laplacian, Matrix.diagonal_apply,
      hij, Ne.symm hij, symAdj, D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, hl]
    ring
  rw [hnorm, hq] at h
  constructor <;> linarith [h.1, h.2]

private lemma symAdj_entry_dichotomy {n : ℕ} (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (d : ℝ) (hr : ∀ i, outDegree Γ i = d)
    (hw : spread Γ < 1) :
    (∀ i j, symAdj Γ i j = 0 ∨ symAdj Γ i j = 1) ∨
    (∀ i j, i ≠ j → symAdj Γ i j = 1 ∨ symAdj Γ i j = 2) := by
  by_cases hex : ∃ i j, symAdj Γ i j = 2
  · right
    obtain ⟨i,j,hij⟩ := hex
    have hne : i ≠ j := by
      intro h; subst j
      rw [symAdj_diag Γ hl i] at hij
      norm_num at hij
    have hp := symAdj_pair_bounds Γ hl d hr i j hne
    rw [hij] at hp
    intro k l hkl
    rcases symAdj_entries Γ k l with hz | ho | ht
    · have hp' := symAdj_pair_bounds Γ hl d hr k l hkl
      rw [hz] at hp'
      unfold spread at hw
      linarith
    · exact Or.inl ho
    · exact Or.inr ht
  · left
    intro i j
    rcases symAdj_entries Γ i j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hex ⟨i,j,h⟩)

private lemma symAdj_centered_bound {n : ℕ} (Γ : Digraph (Fin n))
    (d : ℝ) (hr : ∀ i, outDegree Γ i = d) (x : Fin n → ℝ)
    (hx : ∑ i, x i = 0) :
    |(x ⬝ᵥ ((symAdj Γ) *ᵥ x)) - (2*d-alpha Γ-beta Γ)*(x ⬝ᵥ x)| ≤
      spread Γ*(x ⬝ᵥ x) := by
  have hb := quadratic_bounds Γ x hx
  have he := laplacian_symAdj_quad Γ d hr x
  rw [abs_le]
  unfold spread
  constructor <;> nlinarith [hb.1, hb.2]

private lemma interior_scalar_contradiction (N r c w : ℝ) (hN : 5 ≤ N)
    (hrlo : 2 ≤ r) (hrhi : r ≤ N-3) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hF : N*r-r^2+(N-1)*c^2+2*r*c ≤ N*w^2) : False := by
  have hN0 : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hrr : 0 ≤ N*((r-2)*(N-3-r)) :=
    mul_nonneg hN0.le (mul_nonneg (by linarith) (by linarith))
  have hnn : 0 ≤ N*(N-5) := mul_nonneg hN0.le (by linarith)
  have hc := sq_nonneg ((N-1)*c+r)
  have hw : w^2 < 1 := by exact (sq_lt_one_iff₀ hw0).mpr hw1
  have hp : N*w^2 < N := by exact mul_lt_of_lt_one_right hN0 hw
  have hupper := mul_le_mul_of_nonneg_left hF hNm.le
  have hstrict := mul_lt_mul_of_pos_left hp hNm
  nlinarith

private lemma frob_bound_of_quad_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (w : ℝ) (hw : 0 ≤ w)
    (hq : ∀ x : Fin n → ℝ, |(x ⬝ᵥ (M *ᵥ x))| ≤ w * (x ⬝ᵥ x)) :
    RHLinalg.frobSq M ≤ n * w ^ 2 := by
  rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hM]
  have he (i : Fin n) : (hM.eigenvalues i) ^ 2 ≤ w ^ 2 := by
    let v := hM.eigenvectorBasis i
    have hn : (fun j => v j) ⬝ᵥ (fun j => v j) = 1 := by
      have hvnorm : ‖v‖ = 1 := hM.eigenvectorBasis.norm_eq_one i
      simpa [dotProduct, pow_two, hvnorm] using
        (EuclideanSpace.real_norm_sq_eq v).symm
    have hv : (v ⬝ᵥ (M *ᵥ v)) = hM.eigenvalues i := by
      simpa only [star_trivial, RCLike.re_to_real] using (hM.eigenvalues_eq i).symm
    have h := hq v
    rw [hn, hv, mul_one] at h
    have hh := (sq_le_sq₀ (abs_nonneg _) hw).mpr h
    simpa only [sq_abs] using hh
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => he i)

-- B-cI with its constant direction removed.  On the zero-sum subspace it is exactly B-cI.
private def centered {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r c : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  B - Matrix.diagonal (fun _ => c) + Matrix.of (fun _ _ => (c-r) / n)

private lemma centered_hermitian {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (r c : ℝ) : (centered B r c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := hB.apply i j
  simpa [centered, Matrix.diagonal_apply, eq_comm] using
    congrArg (fun z : ℝ => z - (if i=j then c else 0) + (c-r)/n) h

private lemma centered_row_sum {n : ℕ} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℝ)
    (r c : ℝ) (hr : ∀ i, ∑ j, B i j = r) :
    ∀ i, ∑ j, centered B r c i j = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  intro i
  simp [centered, Matrix.diagonal_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hr, hn', mul_div_cancel₀]

private lemma centered_quad {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r c : ℝ)
    (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (x ⬝ᵥ ((centered B r c) *ᵥ x)) = (x ⬝ᵥ (B *ᵥ x)) - c * (x ⬝ᵥ x) := by
  have hm : centered B r c = B - Matrix.diagonal (fun _ => c) +
      (Matrix.of (fun _ _ : Fin n => (c-r)/n)) := by ext i j; simp [centered, Matrix.diagonal_apply]
  rw [hm]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add,
    dotProduct_sub, Matrix.diagonal_const_mulVec]
  have hz : (Matrix.of (fun _ _ : Fin n => (c-r)/n)) *ᵥ x = 0 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← Finset.mul_sum, hx]
  rw [hz, dotProduct_zero, add_zero]
  simp only [dotProduct_smul, smul_eq_mul]

private lemma centered_full_bound {n : ℕ} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (r c w : ℝ) (hr : ∀ i, ∑ j, B i j = r) (hw : 0 ≤ w)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |(x ⬝ᵥ (B *ᵥ x)) - c * (x ⬝ᵥ x)| ≤ w * (x ⬝ᵥ x)) :
    ∀ x : Fin n → ℝ, |(x ⬝ᵥ ((centered B r c) *ᵥ x))| ≤ w * (x ⬝ᵥ x) := by
  intro x
  let y : Fin n → ℝ := fun i => x i - (∑ j, x j) / n
  have hys : ∑ i, y i = 0 := projected_sum hn x
  have hrr := centered_row_sum hn B r c hr
  have hcc : ∀ j, ∑ i, centered B r c i j = 0 := by
    intro j
    have hs := (centered_hermitian B hB r c)
    calc
      ∑ i, centered B r c i j = ∑ i, centered B r c j i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [star_trivial] using hs.apply j i
      _ = 0 := hrr j
  have hxy : (y ⬝ᵥ ((centered B r c) *ᵥ y)) = (x ⬝ᵥ ((centered B r c) *ᵥ x)) :=
    quad_sub_const_of_zero_sums _ hrr hcc x _
  rw [← hxy, centered_quad B r c y hys]
  apply (hq y hys).trans
  apply mul_le_mul_of_nonneg_left _ hw
  have hp := projected_norm hn x
  change y ⬝ᵥ y = _ at hp
  rw [hp]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hn0)

private lemma centered_frob {n : ℕ} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (r c : ℝ) (hr : ∀ i, ∑ j, B i j = r)
    (hd : ∀ i, B i i = 0) (hb : ∀ i j, B i j = 0 ∨ B i j = 1) :
    RHLinalg.frobSq (centered B r c) =
      n * r - r ^ 2 + (n - 1 : ℝ) * c ^ 2 + 2 * r * c := by
  let t := (c-r)/(n:ℝ)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : (centered B r c).IsHermitian := centered_hermitian B hB r c
  have hentry (i j : Fin n) :
      centered B r c i j ^ 2 =
      B i j - 2*c*B i j*(if i=j then 1 else 0) +
      2*t*B i j + (if i=j then c^2 - 2*c*t else 0) + t^2 := by
    by_cases hij : i=j
    · subst j
      simp [centered, t, hd]
      ring
    · rcases hb i j with h | h <;>
        simp [centered, t, h, hij] <;> ring
  have hf : RHLinalg.frobSq (centered B r c) = ∑ i, ∑ j, centered B r c i j ^ 2 := by
    simp only [RHLinalg.frobSq, hs.eq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      RCLike.re_to_real]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hh := hs.apply i j
    simp only [star_trivial] at hh
    rw [hh, pow_two]
  rw [hf]
  simp_rw [hentry]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hr,
    Finset.sum_mul, mul_ite, ite_mul, hd, t]
  field_simp
  ring

private lemma interior_variance_impossible {n : ℕ} (hn : 5 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (r c w : ℝ) (hr : ∀ i, ∑ j, B i j = r)
    (hd : ∀ i, B i i = 0) (hb : ∀ i j, B i j = 0 ∨ B i j = 1)
    (hrlo : 2 ≤ r) (hrhi : r ≤ n-3) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |(x ⬝ᵥ (B *ᵥ x)) - c * (x ⬝ᵥ x)| ≤ w * (x ⬝ᵥ x)) : False := by
  have hn0 : 0 < n := by exact Nat.zero_lt_of_lt hn
  have hupper := frob_bound_of_quad_bound _ (centered_hermitian B hB r c) w hw0
    (centered_full_bound hn0 B hB r c w hr hw0 hq)
  rw [centered_frob hn0 B hB r c hr hd hb] at hupper
  exact interior_scalar_contradiction n r c w (by exact_mod_cast hn)
    hrlo hrhi hw0 hw1 hupper

private lemma unique_one_of_row_one {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsAdjMatrix) (hr : ∀ i, ∑ j, C i j = 1) (i : Fin n) :
    ∃! j, C i j = 1 := by
  classical
  have hd : hC.toGraph.degree i = 1 := by
    have h := SimpleGraph.adjMatrix_mulVec_const_apply (G := hC.toGraph) (a := (1:ℝ)) (v := i)
    rw [hC.adjMatrix_toGraph_eq] at h
    have h' : (hC.toGraph.degree i : ℝ) = 1 := by
      simpa [Matrix.mulVec, dotProduct, hr] using h.symm
    exact_mod_cast h'
  simpa using SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd

private lemma matching_bound_impossible {n : ℕ} (hn : 4 ≤ n) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsAdjMatrix) (hr : ∀ i, ∑ j, C i j = 1)
    (c w : ℝ) (hw : w < 1)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |(x ⬝ᵥ (C *ᵥ x)) - c*(x ⬝ᵥ x)| ≤ w*(x ⬝ᵥ x)) : False := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨j, hij, huj⟩ := unique_one_of_row_one C hC hr i
  have hji : C j i = 1 := by rw [hC.symm.apply i j]; exact hij
  have hne : i ≠ j := by
    intro h
    subst j
    rw [hC.apply_diag] at hij
    norm_num at hij
  have hcard : ({i,j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have h2 : ({i,j} : Finset (Fin n)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
  have hki : k ≠ i := hk'.1
  have hkj : k ≠ j := hk'.2
  obtain ⟨l, hkl, hul⟩ := unique_one_of_row_one C hC hr k
  have hlk : C l k = 1 := by rw [hC.symm.apply k l]; exact hkl
  have hklne : k ≠ l := by
    intro h
    subst l
    rw [hC.apply_diag] at hkl
    norm_num at hkl
  have hli : l ≠ i := by
    intro h
    subst l
    have hx : k = j := huj k hlk
    exact hkj hx
  have hlj : l ≠ j := by
    intro h
    subst l
    obtain ⟨_,_,hu⟩ := unique_one_of_row_one C hC hr j
    exact hki (hu k hlk |>.trans (hu i hji).symm)
  have hcross (a b : Fin n) (hab : a ≠ b) (ha : C a b = 1)
      (t : Fin n) (ht : t ≠ b) : C a t = 0 := by
    obtain ⟨_,_,hu⟩ := unique_one_of_row_one C hC hr a
    apply (hC.apply_ne_one_iff a t).mp
    intro h
    exact ht ((hu t h).trans (hu b ha).symm)
  have hik : C i k = 0 := hcross i j hne hij k hkj
  have hil : C i l = 0 := hcross i j hne hij l hlj
  have hjk : C j k = 0 := hcross j i hne.symm hji k hki
  have hjl : C j l = 0 := hcross j i hne.symm hji l hli
  have hki0 : C k i = 0 := (hC.symm.apply i k).trans hik
  have hli0 : C l i = 0 := (hC.symm.apply i l).trans hil
  have hkj0 : C k j = 0 := (hC.symm.apply j k).trans hjk
  have hlj0 : C l j = 0 := (hC.symm.apply j l).trans hjl
  let x : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  let y : Fin n → ℝ := Pi.single i 1 + Pi.single j 1 - Pi.single k 1 - Pi.single l 1
  have hxs : ∑ a, x a = 0 := (pair_sum_norm i j hne).1
  have hys : ∑ a, y a = 0 := by simp [y, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hxx : x ⬝ᵥ x = 2 := (pair_sum_norm i j hne).2
  have hyy : y ⬝ᵥ y = 4 := by
    norm_num [y, sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
      hne, Ne.symm hne, hki, Ne.symm hki, hkj, Ne.symm hkj,
      hli, Ne.symm hli, hlj, Ne.symm hlj, hklne, Ne.symm hklne]
  have hqx : (x ⬝ᵥ (C *ᵥ x)) = -2 := by
    rw [pair_quad]
    norm_num [hC.apply_diag, hij, hji]
  have hqy : (y ⬝ᵥ (C *ᵥ y)) = 4 := by
    norm_num [y, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_single,
      sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, single_dotProduct,
      hC.apply_diag, hij, hji, hkl, hlk, hik, hil, hjk, hjl,
      hki0, hli0, hkj0, hlj0]
  have hx := hq x hxs
  have hy := hq y hys
  rw [hxx, hqx, abs_le] at hx
  rw [hyy, hqy, abs_le] at hy
  linarith [hx.1, hy.2]

private lemma adjacency_complement_sum {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsAdjMatrix) : B + B.compl = ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) := by
  classical
  simpa only [hB.adjMatrix_toGraph_eq] using
    hB.toGraph.adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph ℝ

private lemma complete_quad {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (x ⬝ᵥ ((((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ)) *ᵥ x)) = -(x ⬝ᵥ x) := by
  have hm : ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) = (Matrix.of (fun _ _ : Fin n => (1:ℝ))) - 1 := by
    exact SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one (α := ℝ) (V := Fin n)
  rw [hm]
  have hz : (Matrix.of (fun _ _ : Fin n => (1:ℝ))) *ᵥ x = 0 := by
    ext i
    simp [Matrix.mulVec, dotProduct, hx]
  simp [Matrix.sub_mulVec, hz]

private lemma complement_quad {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsAdjMatrix) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    (x ⬝ᵥ (B.compl *ᵥ x)) = -(x ⬝ᵥ x) - (x ⬝ᵥ (B *ᵥ x)) := by
  have h := congrArg (fun A => (x ⬝ᵥ (A *ᵥ x))) (adjacency_complement_sum B hB)
  simp only [Matrix.add_mulVec, dotProduct_add] at h
  have hh := complete_quad x hx
  linarith

private lemma offDiagonal_sum {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if i = j then (0:ℝ) else 1) = n-1 := by
  classical
  calc
    _ = ∑ j : Fin n, ((1:ℝ) - if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> norm_num
    _ = n-1 := by rw [Finset.sum_sub_distrib]; simp

private lemma complement_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsAdjMatrix) (r : ℝ) (hr : ∀ i, ∑ j, B i j = r) (i : Fin n) :
    ∑ j, B.compl i j = (n-1:ℝ)-r := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => ∑ j, A i j)
    (adjacency_complement_sum B hB)
  simp [Finset.sum_add_distrib, hr, SimpleGraph.adjMatrix_apply] at h
  have hsum : (∑ j : Fin n, if i = j then (0:ℝ) else 1) = n-1 :=
    offDiagonal_sum i
  rw [hsum] at h
  linarith

private lemma adj_zero_of_rows_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsAdjMatrix) (hr : ∀ i, ∑ j, B i j = 0) : B = 0 := by
  ext i j
  apply (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => ?_)).mp
    (hr i) j (Finset.mem_univ j)
  rcases hB.zero_or_one i k with h | h <;> rw [h] <;> norm_num

private lemma adj_regular_of_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsAdjMatrix) (r : ℕ) (hr : ∀ i, ∑ j, B i j = r) :
    hB.toGraph.IsRegularOfDegree r := by
  classical
  intro i
  have h := SimpleGraph.adjMatrix_mulVec_const_apply (G := hB.toGraph) (a := (1:ℝ)) (v := i)
  rw [hB.adjMatrix_toGraph_eq] at h
  have hh : (hB.toGraph.degree i : ℝ) = r := by
    simpa [Matrix.mulVec, dotProduct, hr] using h.symm
  exact_mod_cast hh

private lemma even_regular_narrow_scalar {n : ℕ} (hn : 2 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsAdjMatrix)
    (r : ℕ) (he : Even r) (hr : ∀ i, ∑ j, B i j = r)
    (c w : ℝ) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |(x ⬝ᵥ (B *ᵥ x)) - c*(x ⬝ᵥ x)| ≤ w*(x ⬝ᵥ x)) :
    B = 0 ∨ B = ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) := by
  classical
  have hdeg := adj_regular_of_rows B hB r hr
  have hN : r < n := by
    have h := hB.toGraph.degree_lt_card_verts (⟨0,by omega⟩ : Fin n)
    simpa [hdeg.degree_eq] using h
  by_cases hz : r = 0
  · left
    apply adj_zero_of_rows_zero B hB
    simpa [hz] using hr
  by_cases ht : r = n-1
  · right
    have hrows : ∀ i, ∑ j, B.compl i j = 0 := by
      intro i
      have hh := complement_rows B hB r hr i
      have hcast : (r:ℝ) = n-1 := by rw [ht, Nat.cast_sub (by omega : 1 ≤ n)]; simp
      linarith
    have hc := adj_zero_of_rows_zero B.compl hB.compl hrows
    have hh := adjacency_complement_sum B hB
    simpa [hc] using hh
  have hlo : 2 ≤ r := by obtain ⟨k,hk⟩ := he; omega
  by_cases hm : r = n-2
  · have hn4 : 4 ≤ n := by omega
    have hrows : ∀ i, ∑ j, B.compl i j = 1 := by
      intro i
      have hh := complement_rows B hB r hr i
      have hcast : (r:ℝ) = n-2 := by rw [hm, Nat.cast_sub (by omega : 2 ≤ n)]; simp
      linarith
    have hqb : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
        |(x ⬝ᵥ (B.compl *ᵥ x)) - (-1-c)*(x ⬝ᵥ x)| ≤ w*(x ⬝ᵥ x) := by
      intro x hx
      rw [complement_quad B hB x hx]
      have heq : -(x ⬝ᵥ x) - (x ⬝ᵥ (B *ᵥ x)) - (-1-c)*(x ⬝ᵥ x) =
          -((x ⬝ᵥ (B *ᵥ x)) - c*(x ⬝ᵥ x)) := by ring
      rw [heq, abs_neg]
      exact hq x hx
    exact False.elim (matching_bound_impossible hn4 B.compl hB.compl hrows (-1-c) w hw1 hqb)
  have hhi : r ≤ n-3 := by omega
  have hn5 : 5 ≤ n := by omega
  have herm : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB.symm
  exact False.elim (interior_variance_impossible hn5 B herm r c w hr hB.apply_diag
    hB.zero_or_one (by exact_mod_cast hlo)
    (by exact_mod_cast (show r ≤ (n:ℤ)-3 by omega)) hw0 hw1 hq)

private lemma spread_zero_of_scalar {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n)) (k : ℝ)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      (x ⬝ᵥ ((laplacian Γ) *ᵥ x)) = k*(x ⬝ᵥ x)) : spread Γ = 0 := by
  have hs : quadraticValues Γ ⊆ {k} := by
    rintro t ⟨v, hv, hn, rfl⟩
    have he := hq v hv
    have hnorm : (fun i => v i) ⬝ᵥ (fun i => v i) = 1 := by
      simpa [dotProduct, pow_two, hn] using (EuclideanSpace.real_norm_sq_eq v).symm
    simpa only [Set.mem_singleton_iff, hnorm, mul_one] using he
  have he := extrema_attained hn Γ
  have ha : alpha Γ = k := Set.mem_singleton_iff.mp (hs he.1)
  have hb : beta Γ = k := Set.mem_singleton_iff.mp (hs he.2)
  simp [spread, ha, hb]

private lemma degree_le_order_sub_one {n : ℕ} (Γ : Digraph (Fin n))
    (hl : ∀ i, ¬ Γ.Adj i i) (i : Fin n) : outDegree Γ i ≤ (n-1:ℝ) := by
  have hs : ∑ j, ((D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency Γ.Adj).map (Nat.cast : ℕ → ℝ)) i j ≤ ∑ j : Fin n, if i=j then (0:ℝ) else 1 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : i=j
    · subst j
      simp [D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, hl]
    · classical
      by_cases ha : Γ.Adj i j <;> simp [D5.S1.Dynamics.Symbolic.FiniteGraphEntropy.adjacency, Matrix.map_apply, h, ha]
  have hsum : (∑ j : Fin n, if i = j then (0:ℝ) else 1) = n-1 :=
    offDiagonal_sum i
  simpa [outDegree, hsum] using hs

private lemma symAdj_scalar_implies_zero {n : ℕ} (hn : 2 ≤ n) (Γ : Digraph (Fin n))
    (d k : ℝ) (hr : ∀ i, outDegree Γ i = d)
    (hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      (x ⬝ᵥ ((symAdj Γ) *ᵥ x)) = k*(x ⬝ᵥ x)) : spread Γ = 0 := by
  apply spread_zero_of_scalar hn Γ (d-k/2)
  intro x hx
  have h := laplacian_symAdj_quad Γ d hr x
  rw [hq x hx] at h
  linarith

private lemma scalar_of_extreme {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (he : B = 0 ∨ B = ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ)) :
    ∃ k : ℝ, ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → (x ⬝ᵥ (B *ᵥ x)) = k*(x ⬝ᵥ x) := by
  rcases he with rfl | rfl
  · exact ⟨0, by intro x _; simp⟩
  · exact ⟨-1, by intro x hx; simpa using complete_quad x hx⟩


/-- No balanced loopless unweighted digraph has spread strictly between zero and one. -/
theorem result : claim := by
  intro n hn Γ hl hb hgap
  have hreg := regular_of_spread_le_one hn Γ hl hb hgap.2.le
  let i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨d, hd⟩ := outDegree_nat Γ i₀
  have hr : ∀ i, outDegree Γ i = (d:ℝ) := fun i => (hreg i i₀).trans hd
  have hdle : d ≤ n-1 := by
    have h := degree_le_order_sub_one Γ hl i₀
    rw [hd] at h
    have hcast : (n-1:ℝ) = ((n-1:ℕ):ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
    rw [hcast] at h
    exact_mod_cast h
  let c : ℝ := 2*d-alpha Γ-beta Γ
  let w : ℝ := spread Γ
  have hq : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
      |(x ⬝ᵥ ((symAdj Γ) *ᵥ x))-c*(x ⬝ᵥ x)| ≤ w*(x ⬝ᵥ x) :=
    fun x hx => symAdj_centered_bound Γ d hr x hx
  rcases symAdj_entry_dichotomy Γ hl d hr hgap.2 with hbits | hbits
  · have hB : (symAdj Γ).IsAdjMatrix :=
      ⟨hbits, (symAdj_hermitian Γ).isSymm, symAdj_diag Γ hl⟩
    have hrows : ∀ i, ∑ j, symAdj Γ i j = ((2*d:ℕ):ℝ) := by
      intro i
      simpa using symAdj_rows Γ hb d hr i
    have he := even_regular_narrow_scalar hn (symAdj Γ) hB (2*d) (by exact even_two_mul d)
      hrows c w hgap.1.le hgap.2 hq
    obtain ⟨k, hk⟩ := scalar_of_extreme (symAdj Γ) he
    have hz := symAdj_scalar_implies_zero hn Γ d k hr hk
    exact (ne_of_gt hgap.1) hz
  · let C : Matrix (Fin n) (Fin n) ℝ := (2 : ℝ) • ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) - symAdj Γ
    have hC : C.IsAdjMatrix := by
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        by_cases hij : i=j
        · subst j
          simp [C, symAdj_diag Γ hl]
        · rcases hbits i j hij with h | h <;>
            norm_num [C, SimpleGraph.adjMatrix_apply, hij, h]
      · change C.transpose = C
        ext i j
        have hb' := (symAdj_hermitian Γ).apply i j
        simp only [star_trivial] at hb'
        simp [C, SimpleGraph.adjMatrix_apply, eq_comm, hb']
      · intro i
        simp [C, symAdj_diag Γ hl]
    have hrows : ∀ i, ∑ j, C i j = ((2*(n-1-d):ℕ):ℝ) := by
      intro i
      have hB := symAdj_rows Γ hb d hr i
      have hncast : ((n-1:ℕ):ℝ) = n-1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
      have hdcast : ((n-1-d:ℕ):ℝ) = n-1-d := by rw [Nat.cast_sub hdle, hncast]
      have hsum : (∑ j : Fin n, if i = j then (0:ℝ) else 1) = n-1 :=
        offDiagonal_sum i
      have hK : ∑ j, ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) i j = (n-1:ℝ) := by
        simpa [SimpleGraph.adjMatrix_apply] using hsum
      change (∑ j, (2 * ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) i j - symAdj Γ i j)) = _
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hK, hB]
      push_cast
      rw [hdcast]
      ring
    have hqc (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
        (x ⬝ᵥ (C *ᵥ x)) = -2*(x ⬝ᵥ x)-(x ⬝ᵥ ((symAdj Γ) *ᵥ x)) := by
      simp only [C, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      have he := complete_quad x hx
      rw [he]
      ring
    have hqc' : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
        |(x ⬝ᵥ (C *ᵥ x))-(-2-c)*(x ⬝ᵥ x)| ≤ w*(x ⬝ᵥ x) := by
      intro x hx
      rw [hqc x hx]
      have he : -2*(x ⬝ᵥ x)-(x ⬝ᵥ ((symAdj Γ) *ᵥ x))-(-2-c)*(x ⬝ᵥ x) =
          -((x ⬝ᵥ ((symAdj Γ) *ᵥ x))-c*(x ⬝ᵥ x)) := by ring
      rw [he, abs_neg]
      exact hq x hx
    have he := even_regular_narrow_scalar hn C hC (2*(n-1-d))
      (by exact even_two_mul _) hrows (-2-c) w hgap.1.le hgap.2 hqc'
    obtain ⟨k, hk⟩ := scalar_of_extreme C he
    have hs : ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
        (x ⬝ᵥ ((symAdj Γ) *ᵥ x)) = (-2-k)*(x ⬝ᵥ x) := by
      intro x hx
      have h := hqc x hx
      rw [hk x hx] at h
      linarith
    have hz := symAdj_scalar_implies_zero hn Γ d (-2-k) hr hs
    exact (ne_of_gt hgap.1) hz

end D5.S3.Combinatorics.SpectralGraph.BarrettBalancedLaplacianSpreadGap
