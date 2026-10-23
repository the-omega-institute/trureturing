/- GID: D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Edge deletion strictly increases complete bipartite distance Seidel energy. -/

/-
Public theorem result:
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#19532; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19628.
All private theorems are bind-only auxiliary declarations; their consumers are
specified below. The graph and all-ones constructions use Mathlib directly.
The related Matrix.unitaryGroup_row_norm owner in D5/S3/Quantum/Foundation/FiniteDensityPurification
has no frozen state record; the real row identities use Mathlib matrix-product identities.
The source's matrix equation J - I - 2D fixes the diagonal at zero; its casewise
formula has a different diagonal. The alternative diagonal is not proved here.
Literature completeness: ASSUMED-UNVERIFIED.
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Chebyshev

namespace D5.S3.Combinatorics.Graph.KyFanGap.HarithaChithraDistanceSeidelEnergy

/-! Binding conventions for T. Haritha and A. V. Chithra, "Distance Seidel matrix of a connected graph",
arXiv:2210.05940v2 (published as "The distance Seidel matrix of connected graphs", DOI 10.1080/09728600.2025.2479147):
the distance Seidel matrix `D^S(G) = J − I − 2D` (`D` the distance matrix), its energy `E_{D^S}(G) = Σ |∂_r^S|`, and
Problem 5.1, "Let G = K_{a,b}, with a, b > 1. Is E_{D^S}(K_{a,b} − e) > E_{D^S}(K_{a,b}), for any edge e of K_{a,b}?". -/


open Matrix

/-- `D^S(G) = J − I − 2D`, with `D` the shortest-path distance matrix of `G`. -/
noncomputable def distSeidel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Matrix V V ℝ :=
  Matrix.of fun u v => 1 - (if u = v then 1 else 0) - 2 * (G.dist u v : ℝ)

/-- `E(M) = Σ_r |∂_r|`, the sum of the absolute values of the eigenvalues of a real symmetric matrix, counted with
multiplicity (the roots of its characteristic polynomial, which splits over `ℝ`). -/
noncomputable def energy {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ :=
  (M.charpoly.roots.map (fun x => |x|)).sum

/-- Problem 5.1, answered as the universal statement: for all `a, b ≥ 2` and every edge `e` of `K_{a,b}`, deleting `e`
strictly increases the distance Seidel energy. -/
def claim : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → ∀ e ∈ (completeBipartiteGraph (Fin a) (Fin b)).edgeSet,
    energy (distSeidel (completeBipartiteGraph (Fin a) (Fin b))) <
      energy (distSeidel ((completeBipartiteGraph (Fin a) (Fin b)).deleteEdges {e}))



open SimpleGraph

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- proof_shape: bind-only; consumers: complete_dist_inl, complete_dist_inr, deleted_dist_ll, deleted_dist_rr. -/
private theorem dist_two_of_common {V : Type*} (G : SimpleGraph V) {x y z : V}
    (hne : x ≠ y) (hnot : ¬G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.dist x y = 2 := by
  have h := G.edist_eq_two_iff.mpr ⟨hne, hnot, z, hxz, hyz⟩
  simp [SimpleGraph.dist, h]

/-- proof_shape: bind-only; consumers: deleted_dist_lr. -/
private theorem dist_three_of_walk {V : Type*} (G : SimpleGraph V) {x y : V}
    (p : G.Walk x y) (hp : p.length = 3) (hne : x ≠ y)
    (hnot : ¬G.Adj x y) (hcommon : ∀ z, ¬(G.Adj x z ∧ G.Adj y z)) :
    G.dist x y = 3 := by
  have hb : G.dist x y ≤ 3 := hp ▸ G.dist_le p
  have hr : G.Reachable x y := p.reachable
  have h0 := hr.pos_dist_of_ne hne
  have h1 : G.dist x y ≠ 1 := fun h => hnot (G.dist_eq_one_iff_adj.mp h)
  have h2 : G.dist x y ≠ 2 := by
    intro h
    have he : G.edist x y = 2 := by simpa [h] using hr.coe_dist_eq_edist.symm
    obtain ⟨z, hz⟩ := (G.edist_eq_two_iff.mp he).2.2
    exact hcommon z hz
  omega

/-- proof_shape: bind-only; consumers: baseline_matrix. -/
private theorem complete_dist_inl_inr (x : A) (y : B) :
    (completeBipartiteGraph A B).dist (.inl x) (.inr y) = 1 := by
  exact dist_eq_one_iff_adj.mpr (by simp [completeBipartiteGraph_adj])

/-- proof_shape: bind-only; consumers: baseline_matrix. -/
private theorem complete_dist_inl [Nonempty B] (x y : A) :
    (completeBipartiteGraph A B).dist (.inl x) (.inl y) = if x = y then 0 else 2 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨z⟩ := ‹Nonempty B›
    exact dist_two_of_common _ (by simpa) (by simp [completeBipartiteGraph_adj])
      (z := Sum.inr z) (by simp [completeBipartiteGraph_adj])
      (by simp [completeBipartiteGraph_adj])

/-- proof_shape: bind-only; consumers: baseline_matrix. -/
private theorem complete_dist_inr [Nonempty A] (x y : B) :
    (completeBipartiteGraph A B).dist (.inr x) (.inr y) = if x = y then 0 else 2 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨z⟩ := ‹Nonempty A›
    exact dist_two_of_common _ (by simpa) (by simp [completeBipartiteGraph_adj])
      (z := Sum.inl z) (by simp [completeBipartiteGraph_adj])
      (by simp [completeBipartiteGraph_adj])


/-- proof_shape: bind-only; consumers: deleted_dist_lr, deleted_dist_ll, deleted_dist_rr. -/
private theorem deleted_adj_lr (u x : A) (v y : B) :
    ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).Adj (.inl x) (.inr y) ↔ (x ≠ u ∨ y ≠ v) := by
  simp only [SimpleGraph.deleteEdges_adj, completeBipartiteGraph_adj]
  simp
  tauto

/-- proof_shape: bind-only; consumers: deleted_dist_ll. -/
private theorem deleted_not_ll (u x y : A) (v : B) :
    ¬((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).Adj (.inl x) (.inl y) := by
  simp [SimpleGraph.deleteEdges_adj, completeBipartiteGraph_adj]

/-- proof_shape: bind-only; consumers: deleted_dist_rr. -/
private theorem deleted_not_rr (u : A) (v x y : B) :
    ¬((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).Adj (.inr x) (.inr y) := by
  simp [SimpleGraph.deleteEdges_adj, completeBipartiteGraph_adj]

/-- proof_shape: bind-only; consumers: perturbation. -/
private theorem deleted_dist_lr [Nontrivial A] [Nontrivial B] (u x : A) (v y : B) :
    ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).dist (.inl x) (.inr y) = if x = u ∧ y = v then 3 else 1 := by
  classical
  by_cases h : x = u ∧ y = v
  · rcases h with ⟨hxu, hyv⟩
    subst x
    subst y
    rw [ite_eq_left ⟨rfl, rfl⟩]
    obtain ⟨u', hu'⟩ := exists_ne u
    obtain ⟨v', hv'⟩ := exists_ne v
    let p : ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).Walk (.inl u) (.inr v) :=
      .cons ((deleted_adj_lr u u v v').mpr (Or.inr hv'))
      (.cons (((deleted_adj_lr u u' v v').mpr (Or.inl hu')).symm)
      (.cons ((deleted_adj_lr u u' v v).mpr (Or.inl hu')) .nil))
    apply dist_three_of_walk _ p (by rfl) (by simp)
    · simp
    · intro z
      cases z with
      | inl z => simp
      | inr z => simp
  · rw [ite_eq_right h]
    apply dist_eq_one_iff_adj.mpr
    rw [deleted_adj_lr]
    tauto

/-- proof_shape: bind-only; consumers: perturbation. -/
private theorem deleted_dist_ll [Nontrivial B] (u x y : A) (v : B) :
    ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).dist (.inl x) (.inl y) = if x = y then 0 else 2 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨v', hv'⟩ := exists_ne v
    exact dist_two_of_common _ (by simpa) (deleted_not_ll u x y v)
      (z := Sum.inr v') ((deleted_adj_lr u x v v').mpr (Or.inr hv'))
      ((deleted_adj_lr u y v v').mpr (Or.inr hv'))

/-- proof_shape: bind-only; consumers: perturbation. -/
private theorem deleted_dist_rr [Nontrivial A] (u : A) (v x y : B) :
    ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}).dist (.inr x) (.inr y) = if x = y then 0 else 2 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨u', hu'⟩ := exists_ne u
    exact dist_two_of_common _ (by simpa) (deleted_not_rr u v x y)
      (z := Sum.inl u') (((deleted_adj_lr u u' v x).mpr (Or.inl hu')).symm)
      (((deleted_adj_lr u u' v y).mpr (Or.inl hu')).symm)



open Matrix Finset
namespace Trace
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- proof_shape: bind-only; consumers: Trace.diag_abs_le, Trace.offdiag_zero. -/
private theorem row_sq_sum {H : Matrix V V ℝ} (hs : H.IsSymm) (h2 : H * H = 1) (i : V) :
    ∑ j, H i j ^ 2 = 1 := by
  have h := congrFun (congrFun h2 i) i
  simpa only [Matrix.mul_apply, hs.apply, Matrix.one_apply_eq, pow_two] using h

/-- proof_shape: bind-only; consumers: Trace.weighted_sum_le, Trace.weighted_sum_eq_commute. -/
private theorem diag_abs_le {H : Matrix V V ℝ} (hs : H.IsSymm) (h2 : H * H = 1) (i : V) :
    |H i i| ≤ 1 := by
  have h := Finset.single_le_sum (f := fun j => H i j ^ 2)
    (fun j _ => sq_nonneg (H i j)) (Finset.mem_univ i)
  rw [row_sq_sum hs h2 i] at h
  exact (sq_le_one_iff_abs_le_one (H i i)).mp h

/-- proof_shape: bind-only; consumers: Trace.weighted_sum_eq_commute. -/
private theorem offdiag_zero {H : Matrix V V ℝ} (hs : H.IsSymm) (h2 : H * H = 1)
    {i j : V} (hij : i ≠ j) (hi : H i i ^ 2 = 1) : H i j = 0 := by
  have hsum : ∑ k ∈ Finset.univ.erase i, H i k ^ 2 = 0 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (fun k => H i k ^ 2) (Finset.mem_univ i)
    rw [row_sq_sum hs h2, hi] at h
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (H i k))).mp hsum
    j (by simp [Ne.symm hij])
  exact sq_eq_zero_iff.mp hz

/-- proof_shape: bind-only; consumers: Trace.weighted_sum_le, Trace.weighted_sum_eq_commute. -/
private theorem weight_le (x t : ℝ) (ht : |t| ≤ 1) : x * t ≤ |x| := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith
  · rw [abs_of_nonpos hx]; nlinarith

/-- proof_shape: bind-only; consumers: Trace.weighted_sum_eq_commute. -/
private theorem weight_eq_sq (x t : ℝ) (hx : x ≠ 0) (he : x * t = |x|) : t ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h] at he
    have : t = -1 := mul_left_cancel₀ (ne_of_lt h) (by simpa only [mul_neg_one] using he)
    rw [this]; norm_num
  · rw [abs_of_pos h] at he
    have : t = 1 := (mul_eq_left₀ (ne_of_gt h)).mp he
    rw [this]; norm_num

/-- proof_shape: bind-only; consumers: Trace.trace_le_energy. -/
private theorem weighted_sum_le (H : Matrix V V ℝ) (hs : H.IsSymm) (h2 : H * H = 1) (d : V → ℝ) :
    ∑ i, d i * H i i ≤ ∑ i, |d i| := by
  exact Finset.sum_le_sum fun i _ => weight_le _ _ (diag_abs_le hs h2 i)

/-- proof_shape: bind-only; consumers: Trace.trace_eq_energy_commute. -/
private theorem weighted_sum_eq_commute (H : Matrix V V ℝ) (hs : H.IsSymm) (h2 : H * H = 1)
    (d : V → ℝ) (he : ∑ i, d i * H i i = ∑ i, |d i|) :
    H * Matrix.diagonal d = Matrix.diagonal d * H := by
  have hpoint : ∀ i, d i * H i i = |d i| := by
    exact fun i => (Finset.sum_eq_sum_iff_of_le
      (fun i _ => weight_le _ _ (diag_abs_le hs h2 i))).mp he i (Finset.mem_univ i)
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j; ring
  by_cases hi : d i = 0
  · by_cases hj : d j = 0
    · rw [hi, hj]; ring
    · have hz := offdiag_zero hs h2 (Ne.symm hij) (weight_eq_sq _ _ hj (hpoint j))
      have hz' : H i j = 0 := by simpa only [hs.apply] using hz
      rw [hz']; ring
  · have hz := offdiag_zero hs h2 hij (weight_eq_sq _ _ hi (hpoint i))
    rw [hz]; ring

/-- proof_shape: bind-only; consumers: Trace.trace_le_energy, Trace.trace_eq_energy_commute. -/
private theorem orthogonal_conjugate {H U : Matrix V V ℝ} (hs : H.IsSymm) (h2 : H * H = 1)
    (hU : U ∈ Matrix.unitaryGroup V ℝ) :
    (Uᵀ * H * U).IsSymm ∧ (Uᵀ * H * U) * (Uᵀ * H * U) = 1 := by
  have huu : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff V ℝ).mp hU
  have hut : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' V ℝ).mp hU
  constructor
  · unfold Matrix.IsSymm
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs.eq, Matrix.mul_assoc]
  · calc
      _ = Uᵀ * H * (U * Uᵀ) * H * U := by noncomm_ring
      _ = Uᵀ * (H * H) * U := by rw [huu]; noncomm_ring
      _ = 1 := by rw [h2, Matrix.mul_one, hut]

/-- proof_shape: bind-only; consumers: Trace.trace_le_energy, Trace.trace_eq_energy_commute. -/
private theorem trace_diagonalized {H U : Matrix V V ℝ} (d : V → ℝ) :
    (H * (U * Matrix.diagonal d * Uᵀ)).trace = ∑ i, d i * (Uᵀ * H * U) i i := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- proof_shape: bind-only; consumers: Trace.trace_lt_energy. -/
private theorem trace_le_energy {X H : Matrix V V ℝ} (hX : X.IsHermitian)
    (hH : H.IsSymm) (h2 : H * H = 1) :
    (H * X).trace ≤ ∑ i, |hX.eigenvalues i| := by
  have hspec : X = (hX.eigenvectorUnitary : Matrix V V ℝ) *
      Matrix.diagonal hX.eigenvalues * (hX.eigenvectorUnitary : Matrix V V ℝ)ᵀ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hX.spectral_theorem
  conv_lhs => rw [hspec, trace_diagonalized]
  obtain ⟨hs, hh⟩ := orthogonal_conjugate hH h2 hX.eigenvectorUnitary.2
  exact weighted_sum_le _ hs hh _

/-- proof_shape: bind-only; consumers: Trace.trace_lt_energy. -/
private theorem trace_eq_energy_commute {X H : Matrix V V ℝ} (hX : X.IsHermitian)
    (hH : H.IsSymm) (h2 : H * H = 1)
    (he : (H * X).trace = ∑ i, |hX.eigenvalues i|) : H * X = X * H := by
  let U : Matrix V V ℝ := hX.eigenvectorUnitary
  have huu : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff V ℝ).mp hX.eigenvectorUnitary.2
  have hspec : X = U * Matrix.diagonal hX.eigenvalues * Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hX.spectral_theorem
  have he' : ∑ i, hX.eigenvalues i * (Uᵀ * H * U) i i = ∑ i, |hX.eigenvalues i| := by
    conv_lhs at he => rw [hspec, trace_diagonalized]
    exact he
  obtain ⟨hs, hh⟩ := orthogonal_conjugate hH h2 hX.eigenvectorUnitary.2
  have hc := weighted_sum_eq_commute (Uᵀ * H * U) hs hh hX.eigenvalues he'
  have hz := congrArg (fun Y => U * Y * Uᵀ) hc
  calc
    H * X = U * ((Uᵀ * H * U) * Matrix.diagonal hX.eigenvalues) * Uᵀ := by
      conv_lhs => rw [hspec]
      simp only [← Matrix.mul_assoc, huu, one_mul]
    _ = U * (Matrix.diagonal hX.eigenvalues * (Uᵀ * H * U)) * Uᵀ := hz
    _ = X * H := by
      conv_rhs => rw [hspec]
      simp only [Matrix.mul_assoc, huu, mul_one]

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem trace_lt_energy {X H : Matrix V V ℝ} (hX : X.IsHermitian)
    (hH : H.IsSymm) (h2 : H * H = 1) (hne : H * X ≠ X * H) :
    (H * X).trace < ∑ i, |hX.eigenvalues i| := by
  exact lt_of_le_of_ne (trace_le_energy hX hH h2)
    (fun h => hne (trace_eq_energy_commute hX hH h2 h))

end Trace

open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace Spectral
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- proof_shape: bind-only; consumers: Spectral.sign_energy. -/
private theorem sum_abs_eq_trace_sqrt {X : Matrix V V ℝ} (hX : X.IsHermitian) :
    (∑ i, |hX.eigenvalues i|) = (CFC.sqrt (Xᵀ * X)).trace := by
  let U : Matrix V V ℝ := hX.eigenvectorUnitary
  let d : V → ℝ := hX.eigenvalues
  let S : Matrix V V ℝ := U * diagonal (fun i => |d i|) * Uᵀ
  have huu : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff V ℝ).mp hX.eigenvectorUnitary.2
  have hut : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' V ℝ).mp hX.eigenvectorUnitary.2
  have hx : X = U * diagonal d * Uᵀ := by
    simpa [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hX.spectral_theorem
  have hp : S.PosSemidef := by
    simpa [S, Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.PosSemidef.diagonal (d := fun i => |d i|)
      (fun i => abs_nonneg (d i))).mul_mul_conjTranspose_same U
  have hsq : S * S = Xᵀ * X := by
    rw [hX.isSymm.eq]
    conv_rhs => rw [hx]
    have hd : diagonal (fun i => |d i|) * diagonal (fun i => |d i|) =
        diagonal d * diagonal d := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1; funext i; nlinarith only [sq_abs (d i)]
    calc
      S * S = U * (diagonal (fun i => |d i|) * diagonal (fun i => |d i|)) * Uᵀ := by
        dsimp [S]; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hut, one_mul]
      _ = U * (diagonal d * diagonal d) * Uᵀ := by rw [hd]
      _ = (U * diagonal d * Uᵀ) * (U * diagonal d * Uᵀ) := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hut, one_mul]
  rw [CFC.sqrt_unique hsq hp.nonneg]
  dsimp [S]
  rw [Matrix.trace_mul_cycle, hut, one_mul, Matrix.trace_diagonal]

/-- proof_shape: bind-only; consumers: baseline_energy. -/
private theorem sign_energy {X H : Matrix V V ℝ} (hX : X.IsHermitian) (hH : H.IsSymm)
    (h2 : H * H = 1) (hp : (H * X).PosSemidef) :
    (∑ i, |hX.eigenvalues i|) = (H * X).trace := by
  have hc : X * H = H * X := by
    have hs := hp.isHermitian.isSymm.eq
    simpa [Matrix.transpose_mul, hX.isSymm.eq, hH.eq] using hs
  have he : (H * X) * (H * X) = Xᵀ * X := by
    rw [hX.isSymm.eq]
    calc
      (H * X) * (H * X) = H * (X * H) * X := by noncomm_ring
      _ = H * (H * X) * X := by rw [hc]
      _ = X * X := by simp only [← Matrix.mul_assoc, h2, one_mul]
  rw [sum_abs_eq_trace_sqrt hX, CFC.sqrt_unique he hp.nonneg]

end Spectral

open Matrix Finset
noncomputable section
namespace Blocks


/-- proof_shape: bind-only; consumers: Blocks.M_symm, Blocks.H_mul_M, Blocks.M_mul_H, baseline_matrix, perturbation, baseline_energy, perturbation_trace, perturbation_commutator, deletion_increases. -/
private def M (a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  Matrix.fromBlocks ((3 : ℝ) • (1 - (Matrix.of (fun (_ : Fin a) (_ : Fin a) => (1 : ℝ))))) (-(Matrix.of (fun (_ : Fin a) (_ : Fin b) => (1 : ℝ)))) (-(Matrix.of (fun (_ : Fin b) (_ : Fin a) => (1 : ℝ)))) ((3 : ℝ) • (1 - (Matrix.of (fun (_ : Fin b) (_ : Fin b) => (1 : ℝ)))))

/-- proof_shape: bind-only; consumers: Blocks.H_symm, Blocks.H_sq, Blocks.H_mul_M, Blocks.M_mul_H, baseline_energy, perturbation_trace, perturbation_commutator, deletion_increases. -/
private def H (a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  Matrix.fromBlocks (1 - (2 / (a : ℝ)) • (Matrix.of (fun (_ : Fin a) (_ : Fin a) => (1 : ℝ)))) 0 0
    (1 - (2 / (b : ℝ)) • (Matrix.of (fun (_ : Fin b) (_ : Fin b) => (1 : ℝ))))

/-- proof_shape: bind-only; consumers: Blocks.S_symm, Blocks.H_mul_M, Blocks.M_mul_H, Blocks.S_quadratic, Blocks.S_posSemidef, Blocks.trace_S, baseline_energy, perturbation_commutator, deletion_increases. -/
private def S (a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  Matrix.fromBlocks ((3 : ℝ) • (1 : Matrix (Fin a) (Fin a) ℝ) + (3 - 6 / (a : ℝ)) • (Matrix.of (fun (_ : Fin a) (_ : Fin a) => (1 : ℝ))))
    ((Matrix.of (fun (_ : Fin a) (_ : Fin b) => (1 : ℝ)))) ((Matrix.of (fun (_ : Fin b) (_ : Fin a) => (1 : ℝ))))
    ((3 : ℝ) • (1 : Matrix (Fin b) (Fin b) ℝ) + (3 - 6 / (b : ℝ)) • (Matrix.of (fun (_ : Fin b) (_ : Fin b) => (1 : ℝ))))

/-- proof_shape: bind-only; consumers: Blocks.H_sq, Blocks.H_mul_M. -/
private theorem J_mul (a b c : ℕ) : (Matrix.of (fun (_ : Fin a) (_ : Fin b) => (1 : ℝ))) * (Matrix.of (fun (_ : Fin b) (_ : Fin c) => (1 : ℝ))) = (b : ℝ) • (Matrix.of (fun (_ : Fin a) (_ : Fin c) => (1 : ℝ))) := by
  calc
    _ = Matrix.of (fun (_ : Fin a) (_ : Fin c) => (b : ℝ)) := by
      simpa [Matrix.vecMulVec, dotProduct] using
        (Matrix.vecMulVec_mul_vecMulVec (1 : Fin a → ℝ) (1 : Fin b → ℝ)
          (1 : Fin b → ℝ) (1 : Fin c → ℝ))
    _ = _ := by ext i j; simp

/-- proof_shape: bind-only; consumers: Blocks.S_quadratic. -/
private theorem J_mulVec (a b : ℕ) (x : Fin b → ℝ) :
    (Matrix.of (fun (_ : Fin a) (_ : Fin b) => (1 : ℝ))) *ᵥ x = fun _ => ∑ j, x j := by
  have h := Matrix.vecMulVec_mulVec (1 : Fin a → ℝ) (1 : Fin b → ℝ) x
  rw [op_smul_eq_smul] at h
  ext i
  simpa [Matrix.vecMulVec, dotProduct] using congrFun h i

/-- proof_shape: bind-only; consumers: Blocks.M_mul_H, baseline_energy. -/
private theorem M_symm (a b : ℕ) : (M a b).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  cases i <;> cases j <;> simp [M, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

/-- proof_shape: bind-only; consumers: Blocks.M_mul_H, baseline_energy, deletion_increases. -/
private theorem H_symm (a b : ℕ) : (H a b).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  cases i <;> cases j <;> simp [H, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

/-- proof_shape: bind-only; consumers: Blocks.M_mul_H, Blocks.S_posSemidef. -/
private theorem S_symm (a b : ℕ) : (S a b).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  cases i <;> cases j <;> simp [S, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

/-- proof_shape: bind-only; consumers: baseline_energy, deletion_increases. -/
private theorem H_sq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : H a b * H a b = 1 := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  simp only [H, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, J_mul, smul_smul]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply] <;>
    split_ifs <;> field_simp [ha', hb'] <;> ring

/-- proof_shape: bind-only; consumers: Blocks.M_mul_H, baseline_energy, perturbation_commutator, deletion_increases. -/
private theorem H_mul_M (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : H a b * M a b = S a b := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  simp only [H, M, S, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub,
    Matrix.one_mul, Matrix.mul_one, mul_neg, neg_mul, J_mul, smul_smul,
    smul_sub, smul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul]
  congr 1 <;> ext i j <;>
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.neg_apply, Matrix.zero_apply, Matrix.of_apply] <;>
    field_simp [ha', hb'] <;> ring

/-- proof_shape: bind-only; consumers: perturbation_commutator. -/
private theorem M_mul_H (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : M a b * H a b = S a b := by
  have ht := congrArg Matrix.transpose (H_mul_M a b ha hb)
  simpa only [Matrix.transpose_mul, (M_symm a b).eq, (H_symm a b).eq,
    (S_symm a b).eq] using ht

/-- proof_shape: bind-only; consumers: Blocks.S_posSemidef. -/
private theorem S_quadratic (a b : ℕ) (x : (Fin a ⊕ Fin b) → ℝ) :
    star x ⬝ᵥ ((S a b) *ᵥ x) =
      3 * (∑ i, x (.inl i) ^ 2) + 3 * (∑ j, x (.inr j) ^ 2) +
      (3 - 6 / (a : ℝ)) * (∑ i, x (.inl i)) ^ 2 +
      (3 - 6 / (b : ℝ)) * (∑ j, x (.inr j)) ^ 2 +
      2 * (∑ i, x (.inl i)) * (∑ j, x (.inr j)) := by
  have hl (i : Fin a) : (S a b *ᵥ x) (.inl i) =
      3 * x (.inl i) + (3 - 6 / (a : ℝ)) * (∑ j, x (.inl j)) + ∑ j, x (.inr j) := by
    simp only [S, Matrix.fromBlocks_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, J_mulVec, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have hr (i : Fin b) : (S a b *ᵥ x) (.inr i) =
      (∑ j, x (.inl j)) + (3 * x (.inr i) + (3 - 6 / (b : ℝ)) * (∑ j, x (.inr j))) := by
    simp only [S, Matrix.fromBlocks_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, J_mulVec, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  simp only [dotProduct, star_trivial, Fintype.sum_sum_type, hl, hr, mul_add,
    Finset.sum_add_distrib]
  simp_rw [show ∀ t : ℝ, t * (3 * t) = 3 * t ^ 2 by intro t; ring]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring


/-- proof_shape: bind-only; consumers: Blocks.S_posSemidef. -/
private theorem scalar_quadratic_nonneg (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (p q u v : ℝ) (hp : p ^ 2 ≤ a * u) (hq : q ^ 2 ≤ b * v) :
    0 ≤ 3 * u + 3 * v + (3 - 6 / a) * p ^ 2 + (3 - 6 / b) * q ^ 2 + 2 * p * q := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpa : 0 ≤ u - p ^ 2 / a := by
    rw [sub_nonneg, div_le_iff₀ ha0]; simpa only [mul_comm] using hp
  have hqb : 0 ≤ v - q ^ 2 / b := by
    rw [sub_nonneg, div_le_iff₀ hb0]; simpa only [mul_comm] using hq
  have hca : 0 ≤ 2 - 3 / a := by
    rw [sub_nonneg, div_le_iff₀ ha0]; linarith
  have hcb : 0 ≤ 2 - 3 / b := by
    rw [sub_nonneg, div_le_iff₀ hb0]; linarith
  have heq : 3 * u + 3 * v + (3 - 6 / a) * p ^ 2 + (3 - 6 / b) * q ^ 2 + 2 * p * q =
      3 * (u - p ^ 2 / a) + 3 * (v - q ^ 2 / b) +
      (2 - 3 / a) * p ^ 2 + (2 - 3 / b) * q ^ 2 + (p + q) ^ 2 := by ring
  rw [heq]
  positivity

/-- proof_shape: bind-only; consumers: baseline_energy. -/
private theorem S_posSemidef (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : (S a b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (S_symm a b))
  intro x
  rw [S_quadratic]
  apply scalar_quadratic_nonneg (a : ℝ) (b : ℝ) (by exact_mod_cast ha) (by exact_mod_cast hb)
  · simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => x (.inl i))
  · simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => x (.inr j))

/-- proof_shape: bind-only; consumers: baseline_energy, deletion_increases. -/
private theorem trace_S (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : (S a b).trace = 6 * ((a : ℝ) + b - 2) := by
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  simp [S, Matrix.trace, Fintype.sum_sum_type, Matrix.of_apply]
  field_simp [ha', hb']
  ring

end Blocks

open Matrix SimpleGraph

/-- proof_shape: bind-only; consumers: baseline_energy, deletion_increases. -/
private theorem energy_eigenvalues {V : Type*} [Fintype V] [DecidableEq V]
    {X : Matrix V V ℝ} (hX : X.IsHermitian) :
    energy X = ∑ i, |hX.eigenvalues i| := by
  simp [energy, hX.roots_charpoly_eq_eigenvalues, Multiset.map_map, Function.comp_def]

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem distSeidel_hermitian {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (distSeidel G).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext x y
  simp [distSeidel, SimpleGraph.dist_comm, eq_comm]

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem baseline_matrix (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    distSeidel (completeBipartiteGraph (Fin a) (Fin b)) = Blocks.M a b := by
  haveI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  haveI : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  ext x y
  cases x <;> cases y <;>
    simp [distSeidel, Blocks.M, Matrix.of_apply, complete_dist_inl, complete_dist_inr,
      complete_dist_inl_inr, SimpleGraph.dist_comm, Matrix.one_apply] <;>
    (try split_ifs) <;> norm_num

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem perturbation (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (u : Fin a) (v : Fin b) :
    distSeidel ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)}) = Blocks.M a b - (4 : ℝ) •
      (Matrix.single (Sum.inl u : Fin a ⊕ Fin b) (Sum.inr v) (1 : ℝ) + Matrix.single (Sum.inr v : Fin a ⊕ Fin b) (Sum.inl u) (1 : ℝ)) := by
  haveI : Nontrivial (Fin a) := Fin.nontrivial_iff_two_le.mpr ha
  haveI : Nontrivial (Fin b) := Fin.nontrivial_iff_two_le.mpr hb
  ext x y
  cases x <;> cases y <;>
    simp [distSeidel, Blocks.M, Matrix.of_apply, deleted_dist_ll, deleted_dist_rr,
      deleted_dist_lr, SimpleGraph.dist_comm, Matrix.one_apply, Matrix.single_apply, eq_comm] <;>
    (try split_ifs) <;> norm_num <;> simp_all [eq_comm]

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem baseline_energy (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    energy (Blocks.M a b) = 6 * ((a : ℝ) + b - 2) := by
  have ha0 : a ≠ 0 := Nat.ne_zero_of_lt ha
  have hb0 : b ≠ 0 := Nat.ne_zero_of_lt hb
  have hm := Matrix.isHermitian_iff_isSymm.mpr (Blocks.M_symm a b)
  rw [energy_eigenvalues hm, Spectral.sign_energy hm (Blocks.H_symm a b)
    (Blocks.H_sq a b ha0 hb0)]
  · rw [Blocks.H_mul_M a b ha0 hb0, Blocks.trace_S a b ha0 hb0]
  · rw [Blocks.H_mul_M a b ha0 hb0]
    exact Blocks.S_posSemidef a b ha hb

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem perturbation_trace (a b : ℕ) (u : Fin a) (v : Fin b) :
    (Blocks.H a b * (Blocks.M a b - (4 : ℝ) •
      (Matrix.single (Sum.inl u : Fin a ⊕ Fin b) (Sum.inr v) (1 : ℝ) + Matrix.single (Sum.inr v : Fin a ⊕ Fin b) (Sum.inl u) (1 : ℝ)))).trace =
      (Blocks.H a b * Blocks.M a b).trace := by
  simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_single, Blocks.H]

/-- proof_shape: bind-only; consumers: deletion_increases. -/
private theorem perturbation_commutator (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (u i : Fin a) (v : Fin b) (hi : i ≠ u) :
    let N := Blocks.M a b - (4 : ℝ) •
      (Matrix.single (Sum.inl u : Fin a ⊕ Fin b) (Sum.inr v) (1 : ℝ) + Matrix.single (Sum.inr v : Fin a ⊕ Fin b) (Sum.inl u) (1 : ℝ))
    (Blocks.H a b * N - N * Blocks.H a b) (.inl i) (.inr v) = 8 / (a : ℝ) := by
  dsimp only
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul,
    Blocks.H_mul_M a b (Nat.ne_zero_of_lt ha) (Nat.ne_zero_of_lt hb),
    Blocks.M_mul_H a b (Nat.ne_zero_of_lt ha) (Nat.ne_zero_of_lt hb)]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Blocks.H,
    Matrix.of_apply, Matrix.one_apply, hi, Ne.symm hi]
  ring

/-- proof_shape: bind-only; consumers: result. -/
private theorem deletion_increases (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (u : Fin a) (v : Fin b) :
    energy (distSeidel (completeBipartiteGraph (Fin a) (Fin b))) <
      energy (distSeidel ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)})) := by
  have ha0 : a ≠ 0 := Nat.ne_zero_of_lt ha
  have hb0 : b ≠ 0 := Nat.ne_zero_of_lt hb
  let N := distSeidel ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)})
  have hN := distSeidel_hermitian ((completeBipartiteGraph _ _).deleteEdges {s(Sum.inl u, Sum.inr v)})
  have hsame : (Blocks.H a b * N).trace = energy (Blocks.M a b) := by
    rw [show N = _ from perturbation a b ha hb u v, perturbation_trace,
      Blocks.H_mul_M a b ha0 hb0, Blocks.trace_S a b ha0 hb0,
      baseline_energy a b ha hb]
  have hnc : Blocks.H a b * N ≠ N * Blocks.H a b := by
    intro hc
    obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using (show 1 < a from ha)) u
    have he := perturbation_commutator a b ha hb u i v hi
    dsimp only at he
    rw [← perturbation a b ha hb u v] at he
    change (Blocks.H a b * N - N * Blocks.H a b) (.inl i) (.inr v) = _ at he
    rw [hc, sub_self] at he
    have : (8 : ℝ) / a ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast ha0)
    exact this he.symm
  rw [baseline_matrix a b ha hb, ← hsame, energy_eigenvalues hN]
  exact Trace.trace_lt_energy hN (Blocks.H_symm a b) (Blocks.H_sq a b ha0 hb0) hnc

theorem result : claim := by
  intro a b ha hb e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (completeBipartiteGraph (Fin a) (Fin b)).Adj x y := he
    cases x with
    | inl u =>
      cases y with
      | inl w => simp [completeBipartiteGraph_adj] at hxy
      | inr v => exact deletion_increases a b ha hb u v
    | inr v =>
      cases y with
      | inl u =>
        simpa only [show s(Sum.inr v, Sum.inl u) = s(Sum.inl u, Sum.inr v) from Sym2.eq_swap] using deletion_increases a b ha hb u v
      | inr w => simp [completeBipartiteGraph_adj] at hxy


end

end D5.S3.Combinatorics.Graph.KyFanGap.HarithaChithraDistanceSeidelEnergy
