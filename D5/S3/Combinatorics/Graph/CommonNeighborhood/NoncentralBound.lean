/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The noncentral commuting graph satisfies the complete-graph CN energy bound. -/

/- Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/29340#issuecomment-6807007168 -/
import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound

attribute [local instance] Classical.propDecidable Classical.decEq

open Matrix Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

/-- The vertices are individual noncentral elements, not conjugacy classes. -/
abbrev Vertex (G : Type) [Group G] := {x : G // x ∉ Subgroup.center G}

/-- Distinct noncentral elements are adjacent precisely when they commute. -/
def commutingGraph (G : Type) [Group G] : SimpleGraph (Vertex G) where
  Adj x y := x ≠ y ∧ x.val * y.val = y.val * x.val
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

private theorem common_neighbour_eq_square_sub_degree {V : Type} [Fintype V]
    (g : SimpleGraph V) :
    commonNeighbourMatrix g = g.adjMatrix ℝ * g.adjMatrix ℝ - g.degMatrix ℝ := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [commonNeighbourMatrix, SimpleGraph.degMatrix,
      g.adjMatrix_mul_self_apply_self]
  · have hd : g.degMatrix ℝ i j = 0 := by simp [SimpleGraph.degMatrix, hij]
    simp only [commonNeighbourMatrix, if_neg hij, Matrix.sub_apply, hd, sub_zero,
      Matrix.mul_apply, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : g.Adj i k <;> by_cases hjk : g.Adj j k
    · have hki := (g.ne_of_adj hik).symm
      have hkj := (g.ne_of_adj hjk).symm
      simp [hik, hjk, g.adj_comm, hki, hkj]
    · simp [hik, hjk, g.adj_comm]
    · simp [hik, hjk, g.adj_comm]
    · simp [hik, hjk, g.adj_comm]

private theorem psd_difference_bound {V : Type} [Fintype V] [DecidableEq V]
    (P Q : Matrix V V ℝ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (∑ i, |(hP.isHermitian.sub hQ.isHermitian).eigenvalues i|) ≤
      P.trace + Q.trace := by
  let hC := hP.isHermitian.sub hQ.isHermitian
  let U : Matrix V V ℝ := hC.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff V ℝ).mp hC.eigenvectorUnitary.2
  have hdiag : Uᵀ * (P - Q) * U = Matrix.diagonal hC.eigenvalues := by
    simpa [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using
      hC.conjStarAlgAut_star_eigenvectorUnitary
  have hp : (Uᵀ * P * U).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.conjTranspose_mul_mul_same U
  have hq : (Uᵀ * Q * U).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.conjTranspose_mul_mul_same U
  have ht (M : Matrix V V ℝ) : (Uᵀ * M * U).trace = M.trace := by
    rw [Matrix.trace_mul_cycle, hUU, one_mul]
  have hpoint (i : V) : |hC.eigenvalues i| ≤
      (Uᵀ * P * U) i i + (Uᵀ * Q * U) i i := by
    have he := congrArg (fun M : Matrix V V ℝ => M i i) hdiag
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply,
      Matrix.diagonal_apply_eq] at he
    rw [← he]
    exact abs_le.mpr ⟨by linarith [hp.diag_nonneg (i := i)],
      by linarith [hq.diag_nonneg (i := i)]⟩
  calc
    (∑ i, |hC.eigenvalues i|) ≤
        ∑ i, ((Uᵀ * P * U) i i + (Uᵀ * Q * U) i i) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (Uᵀ * P * U).trace + (Uᵀ * Q * U).trace := by
      rw [Finset.sum_add_distrib]; rfl
    _ = P.trace + Q.trace := by
      rw [ht, ht]

/-- The published general estimate, used only by the all-group conclusion. -/
private theorem cn_energy_le_twice_degree_sum {V : Type} [Fintype V]
    (g : SimpleGraph V) :
    graphEnergy g .commonNeighbour ≤ 2 * ∑ i, (g.degree i : ℝ) := by
  classical
  let A := g.adjMatrix ℝ
  have hP : (A * A).PosSemidef := by
    simpa [A, (g.isHermitian_adjMatrix ℝ).eq] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have hD : (g.degMatrix ℝ).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => Nat.cast_nonneg (g.degree i)
  have h := psd_difference_bound (A * A) (g.degMatrix ℝ) hP hD
  have heq := common_neighbour_eq_square_sub_degree g
  have he : graphEnergy g .commonNeighbour =
      ∑ i, |(hP.isHermitian.sub hD.isHermitian).eigenvalues i| := by
    simp [graphEnergy, graphSpectrum, sourceMatrix, heq, A,
      Multiset.map_map, Function.comp_def]
  rw [he]
  calc
    _ ≤ (A * A).trace + (g.degMatrix ℝ).trace := h
    _ = 2 * ∑ i, (g.degree i : ℝ) := by
      simp [Matrix.trace, A, g.adjMatrix_mul_self_apply_self, SimpleGraph.degMatrix]
      <;> ring

private theorem degree_and_center_le_centralizer (G : Type) [Group G] [Fintype G]
    (x : Vertex G) :
    (commutingGraph G).degree x + Fintype.card (Subgroup.center G) + 1 ≤
      Fintype.card (Subgroup.centralizer ({x.val} : Set G)) := by
  classical
  let Z : Finset G := univ.filter (fun y => y ∈ Subgroup.center G)
  let K : Finset G := univ.filter (fun y => y ∈ Subgroup.centralizer ({x.val} : Set G))
  let N : Finset G := univ.filter
    (fun y => y ∉ Subgroup.center G ∧ y ≠ x.val ∧ x.val * y = y * x.val)
  let e : (commutingGraph G).neighborSet x ≃
      {y : G // y ∉ Subgroup.center G ∧ y ≠ x.val ∧ x.val * y = y * x.val} :=
    { toFun := fun y => ⟨y.val.val, y.val.property,
        fun h => y.property.1 (Subtype.ext h.symm), y.property.2⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩,
        ⟨fun h => y.property.2.1 (congrArg Subtype.val h.symm), y.property.2.2⟩⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  have hN : (commutingGraph G).degree x = N.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact (Fintype.card_congr e).trans (Fintype.card_subtype _)
  have hZ : Z.card = Fintype.card (Subgroup.center G) :=
    (Fintype.card_subtype _).symm
  have hK : K.card = Fintype.card (Subgroup.centralizer ({x.val} : Set G)) :=
    (Fintype.card_subtype _).symm
  have hx : x.val ∉ N := by simp [N]
  have hdis : Disjoint Z (insert x.val N) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hyZ : y ∈ Subgroup.center G := (mem_filter.mp hy).2
    rcases mem_insert.mp hz with h | h
    · subst y; exact x.property hyZ
    · exact (mem_filter.mp h).2.1 hyZ
  have hsub : Z ∪ insert x.val N ⊆ K := by
    intro y hy
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hy with h | h
    · exact Subgroup.center_le_centralizer _ (mem_filter.mp h).2
    · rcases mem_insert.mp h with h | h
      · subst y; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mem_filter.mp h).2.2.2.symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem hx,
    hZ, hK, ← hN] at hc
  omega

private theorem twice_degree_bound (G : Type) [Group G] [Fintype G]
    (x : Vertex G) :
    2 * ((commutingGraph G).degree x : ℝ) ≤
      (Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 2 := by
  classical
  let K := Subgroup.centralizer ({x.val} : Set G)
  have hproper : K ≠ ⊤ := by
    intro h
    exact x.property ((Subgroup.centralizer_eq_top_iff_subset.mp h) (Set.mem_singleton _))
  have hindex : 2 ≤ K.index := K.one_lt_index_of_ne_top hproper
  have hcard : 2 * Fintype.card K ≤ Fintype.card G := by
    calc
      2 * Fintype.card K = Fintype.card K * 2 := Nat.mul_comm _ _
      _ ≤ Fintype.card K * K.index := Nat.mul_le_mul_left _ hindex
      _ = Fintype.card G := by simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
  have hd := degree_and_center_le_centralizer G x
  have hz : Fintype.card (Subgroup.center G) ≤ Fintype.card G :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hn : Fintype.card (Vertex G) + Fintype.card (Subgroup.center G) =
      Fintype.card G := by
    rw [Fintype.card_subtype_compl, Nat.sub_add_cancel hz]
  have hc : 2 * (commutingGraph G).degree x +
      2 * Fintype.card (Subgroup.center G) + 2 ≤ Fintype.card G := by
    dsimp [K] at hcard
    omega
  have hci : (2 : ℤ) * (commutingGraph G).degree x +
      2 * Fintype.card (Subgroup.center G) + 2 ≤ Fintype.card G := by exact_mod_cast hc
  have hni : (Fintype.card (Vertex G) : ℤ) + Fintype.card (Subgroup.center G) =
      Fintype.card G := by exact_mod_cast hn
  have hi : (2 : ℤ) * (commutingGraph G).degree x ≤
      (Fintype.card (Vertex G) : ℤ) - Fintype.card (Subgroup.center G) - 2 := by omega
  exact_mod_cast hi

/-- Nath–Fasfous–Das–Shang, Conjecture 2, with its full group quantifiers. -/
theorem result (G : Type) [Group G] [Fintype G]
    (nonabelian : ∃ a b : G, a * b ≠ b * a) :
    graphEnergy (commutingGraph G) .commonNeighbour ≤
      2 * ((Fintype.card (Vertex G) : ℝ) - 1) *
        ((Fintype.card (Vertex G) : ℝ) - 2) := by
  classical
  obtain ⟨a, b, hab⟩ := nonabelian
  have ha : a ∉ Subgroup.center G := by
    intro h; exact hab (Subgroup.mem_center_iff.mp h b).symm
  letI : Nonempty (Vertex G) := ⟨⟨a, ha⟩⟩
  have hn : (0 : ℝ) ≤ Fintype.card (Vertex G) :=
    le_of_lt (by exact_mod_cast Fintype.card_pos (α := Vertex G))
  have hz : (0 : ℝ) ≤ Fintype.card (Subgroup.center G) := Nat.cast_nonneg _
  have hs : 2 * ∑ x : Vertex G, ((commutingGraph G).degree x : ℝ) ≤
      (Fintype.card (Vertex G) : ℝ) *
        ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 2) := by
    calc
      _ = ∑ x : Vertex G, 2 * ((commutingGraph G).degree x : ℝ) := Finset.mul_sum _ _ _
      _ ≤ ∑ _x : Vertex G,
          ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 2) :=
        Finset.sum_le_sum fun x _ => twice_degree_bound G x
      _ = _ := by simp
  have he := cn_energy_le_twice_degree_sum (commutingGraph G)
  nlinarith [sq_nonneg ((Fintype.card (Vertex G) : ℝ) - 2), mul_nonneg hn hz]

end D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
