/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound]
   utility: none
   digest: Every finite simple graph with m edges and r non-isolated vertices has common-neighbourhood energy at most 2 sum_v max(d(v) - 1, 0) = 4m - 2r. -/

/- Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/32715 -/
import D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Neighbourhood-clique bound for the common-neighbourhood energy of a finite simple graph. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound

attribute [local instance] Classical.propDecidable

/-
proof_shape:
  nbhd, proj, matP, matQ: definitions
  nbhd_sq, nbhd_sum, nbhd_dot, diag_mul_outer, outer_mul_diag: bind-only
    (consumers: smul_proj, compl_posSemidef, split_eq, trace_value)
  smul_proj, compl_posSemidef, matP_posSemidef, matQ_posSemidef, split_eq, trace_value:
    content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.psd_difference_bound,
    common_neighbour_eq_square_sub_degree (statement_id sha256:4a61e26c582e3a9997b9d862d130ebfd8cd223970eceb985e8b3f0f6933182cd)
  D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.source_matrix_isHermitian
    (statement_id sha256:f1719f538d0bfd6d4c9cd272d7a3754edc7169f96ade79d35351cea0c770b729)
escape_witness: the neighbourhood-clique decomposition CN = sum_v (a_v a_v^T - diag a_v) =
  P - Q with P = sum_v (d_v - 1) Pi_v and Q = sum_v (diag a_v - Pi_v), where Pi_v is the averaging
  projection onto the neighbourhood of v and diag a_v - Pi_v is a symmetric idempotent; both parts
  are positive semidefinite and tr P = tr Q = sum_v max(d_v - 1, 0).
admission_basis: escape-witness
-/

open Matrix Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
  (psd_difference_bound common_neighbour_eq_square_sub_degree)

section Split

variable {V : Type} [Fintype V] (g : SimpleGraph V)

/-- The indicator vector of the neighbourhood of `v`. -/
private def nbhd (v : V) : V → ℝ := fun x => g.adjMatrix ℝ x v

omit [Fintype V] in
private theorem nbhd_sq (v x : V) : nbhd g v x * nbhd g v x = nbhd g v x := by
  unfold nbhd
  by_cases h : g.Adj x v <;> simp [h]

private theorem nbhd_sum (v : V) : ∑ x, nbhd g v x = g.degree v := by
  calc ∑ x, nbhd g v x = ((univ.filter (g.Adj v ·)).card : ℝ) := by
        simp [nbhd, SimpleGraph.adjMatrix_apply, Finset.sum_boole, g.adj_comm]
    _ = g.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

private theorem nbhd_dot (v : V) : nbhd g v ⬝ᵥ nbhd g v = g.degree v := by
  simp only [dotProduct, nbhd_sq, nbhd_sum]

/-- The averaging projection onto the neighbourhood of `v` (zero when `v` is isolated). -/
private def proj (v : V) : Matrix V V ℝ :=
  (g.degree v : ℝ)⁻¹ • vecMulVec (nbhd g v) (nbhd g v)

/-- The positive part: `Σ_v (d_v - 1) Π_v`. -/
private def matP : Matrix V V ℝ := ∑ v, ((g.degree v : ℝ) - 1) • proj g v

/-- The negative part: `Σ_v (diag a_v - Π_v)`. -/
private def matQ : Matrix V V ℝ := ∑ v, (diagonal (nbhd g v) - proj g v)

private theorem smul_proj (v : V) :
    (g.degree v : ℝ) • proj g v = vecMulVec (nbhd g v) (nbhd g v) := by
  unfold proj
  by_cases hd : (g.degree v : ℝ) = 0
  · have hz : nbhd g v = 0 := by
      funext x
      have h := nbhd_dot g v
      rw [hd] at h
      have hx : nbhd g v x * nbhd g v x = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_self_nonneg (nbhd g v y))).mp
          (by simpa only [dotProduct] using h) x (mem_univ x)
        exact this
      simpa [nbhd_sq] using hx
    rw [hz, hd]
    simp
  · rw [smul_smul, mul_inv_cancel₀ hd, one_smul]

private theorem diag_mul_outer (v : V) :
    diagonal (nbhd g v) * vecMulVec (nbhd g v) (nbhd g v) = vecMulVec (nbhd g v) (nbhd g v) := by
  ext x y
  rw [Matrix.diagonal_mul, vecMulVec_apply, ← mul_assoc, nbhd_sq]

private theorem outer_mul_diag (v : V) :
    vecMulVec (nbhd g v) (nbhd g v) * diagonal (nbhd g v) = vecMulVec (nbhd g v) (nbhd g v) := by
  ext x y
  rw [Matrix.mul_diagonal, vecMulVec_apply, mul_assoc, nbhd_sq]

private theorem compl_posSemidef (v : V) : (diagonal (nbhd g v) - proj g v).PosSemidef := by
  set M := diagonal (nbhd g v) - proj g v
  have hMh : Mᴴ = M := by
    simp only [M, proj, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.diagonal_conjTranspose, conjTranspose_vecMulVec, star_trivial]
  have hMM : M * M = M := by
    simp only [M, proj, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      diag_mul_outer, outer_mul_diag, vecMulVec_mul_vecMulVec, nbhd_dot,
      Matrix.diagonal_mul_diagonal, nbhd_sq]
    by_cases hd : (g.degree v : ℝ) = 0
    · simp [hd]
    · have e : vecMulVec (nbhd g v) ((g.degree v : ℝ) • nbhd g v) =
          (g.degree v : ℝ) • vecMulVec (nbhd g v) (nbhd g v) := by
        ext x y
        simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
        ring
      rw [e, smul_smul, inv_mul_cancel₀ hd, one_smul, sub_self, smul_zero, sub_zero]
  have h := Matrix.posSemidef_conjTranspose_mul_self M
  rwa [hMh, hMM] at h

private theorem matP_posSemidef : (matP g).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro v _
  have hc : 0 ≤ ((g.degree v : ℝ) - 1) * (g.degree v : ℝ)⁻¹ := by
    rcases Nat.eq_zero_or_pos (g.degree v) with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ g.degree v := by exact_mod_cast h
      exact mul_nonneg (by linarith) (inv_nonneg.mpr (by linarith))
  have hv := Matrix.posSemidef_vecMulVec_self_star (nbhd g v)
  have hs : star (nbhd g v) = nbhd g v := by funext x; simp
  rw [hs] at hv
  rw [proj, smul_smul]
  exact hv.smul hc

private theorem matQ_posSemidef : (matQ g).PosSemidef :=
  Matrix.posSemidef_sum _ fun v _ => compl_posSemidef g v

private theorem split_eq : commonNeighbourMatrix g = matP g - matQ g := by
  rw [common_neighbour_eq_square_sub_degree]
  have h1 : g.adjMatrix ℝ * g.adjMatrix ℝ = ∑ v, vecMulVec (nbhd g v) (nbhd g v) := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, nbhd]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [g.adjMatrix_apply v y, g.adjMatrix_apply y v, g.adj_comm]
  have h2 : g.degMatrix ℝ = ∑ v, diagonal (nbhd g v) := by
    ext x y
    rw [Matrix.sum_apply]
    by_cases hxy : x = y
    · subst hxy
      simp only [SimpleGraph.degMatrix, diagonal_apply_eq]
      rw [← nbhd_sum g x]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [nbhd, g.adjMatrix_apply, g.adj_comm]
    · simp [SimpleGraph.degMatrix, diagonal_apply_ne _ hxy]
  rw [h1, h2, matP, matQ, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← smul_proj, sub_smul, one_smul]
  abel

private theorem trace_value :
    (matP g).trace + (matQ g).trace = 2 * ∑ v, max ((g.degree v : ℝ) - 1) 0 := by
  have hdiag (v : V) : (diagonal (nbhd g v)).trace = g.degree v := by
    rw [Matrix.trace_diagonal, nbhd_sum]
  have hproj (v : V) : (proj g v).trace = (g.degree v : ℝ)⁻¹ * g.degree v := by
    rw [proj, Matrix.trace_smul, trace_vecMulVec, nbhd_dot, smul_eq_mul]
  simp only [matP, matQ, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub, hdiag, hproj,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases Nat.eq_zero_or_pos (g.degree v) with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ g.degree v := by exact_mod_cast h
    have h0 : (g.degree v : ℝ) ≠ 0 := by linarith
    rw [max_eq_left (by linarith), inv_mul_cancel₀ h0]
    ring

end Split

/-- For every finite simple graph with `m` edges, `r` non-isolated vertices and degrees `d(v)`,
the common-neighbourhood energy is at most `2 Σ_v max(d(v) - 1, 0) = 4m - 2r`. -/
theorem result {V : Type} [Fintype V] (g : SimpleGraph V) :
    graphEnergy g .commonNeighbour ≤ 2 * ∑ v, max ((g.degree v : ℝ) - 1) 0 ∧
      2 * ∑ v, max ((g.degree v : ℝ) - 1) 0 =
        4 * (g.edgeFinset.card : ℝ) - 2 * ((univ.filter fun v => 0 < g.degree v).card : ℝ) := by
  constructor
  · have hP := matP_posSemidef g
    have hQ := matQ_posSemidef g
    have h := psd_difference_bound (matP g) (matQ g) hP hQ
    have he : graphEnergy g .commonNeighbour =
        ∑ i, |(hP.isHermitian.sub hQ.isHermitian).eigenvalues i| := by
      simp [graphEnergy, graphSpectrum, sourceMatrix, split_eq g, Multiset.map_map]
    rw [he, ← trace_value g]
    exact h
  · have hsum : ∑ v, max ((g.degree v : ℝ) - 1) 0 =
        ∑ v, (g.degree v : ℝ) - ∑ v, (if 0 < g.degree v then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rcases Nat.eq_zero_or_pos (g.degree v) with h | h
      · simp [h]
      · have h1 : (1 : ℝ) ≤ g.degree v := by exact_mod_cast h
        rw [ite_eq_left h, max_eq_left (by linarith)]
    have hdeg : ∑ v, (g.degree v : ℝ) = 2 * g.edgeFinset.card := by
      exact_mod_cast g.sum_degrees_eq_twice_card_edges
    rw [hsum, hdeg, Finset.sum_boole]
    ring

#print axioms result

end D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound
