/- GID: D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The second largest ordinary Laplacian eigenvalue plus real adjacency rank is at most twice the edge count. -/

/-
admission_basis: open-problem-resolution (#26564; Proved).
escape_witness: none.
Every helper below has proof_shape: bind-only. The consumer-to-prerequisite edges are:
lap_second_le_edges -> lap_eigen_nonneg, lap_eigen_antitone, lap_eigen_sum;
lap_second_order_two -> lap_eigen_nonneg;
partition_energy_le -> pair_energy_le;
internal_bridge_second -> second_le_of_hyperplane, partition_energy_le,
  bridge_side_card_two;
result -> lap_second_le_edges, lap_second_order_two, full_rank_internal_edge,
  internal_bridge_second.
result: proof_shape: bind-only; external settlement #26564.
The scalar estimates, finite-dimensional spectral argument, cut facts and
rank interfaces are reused and normalized; no independent escape content is claimed.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26564.
-/

import D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
import D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting

/-!
# Cazenave's Laplacian–rank inequality

The ordinary decreasing Laplacian spectrum, real adjacency rank and unordered
edge count satisfy Conjecture 5 of arXiv:2611.03879v1.
-/

open Matrix Finset
open scoped BigOperators InnerProductSpace
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.CazenaveLaplacianRankBound
open LinWangCaiBroomSpectralRatio

/-- Conjecture 5 (#239534), for every connected simple graph of order at least two. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 2))) [DecidableRel G.Adj],
    G.Connected →
      lapEig G (1 : Fin (n + 2)) + ((G.adjMatrix ℝ).rank : ℝ) ≤
        2 * (G.edgeFinset.card : ℝ)

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

private lemma lap_eigen_nonneg {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (i : Fin N) : 0 ≤ lapEig G i := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply,
    lapEig] using (G.posSemidef_lapMatrix ℝ).eigenvalues_nonneg
      (e (Fin.cast (Fintype.card_fin N).symm i))

private lemma lap_eigen_antitone {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : Antitone (lapEig G) := by
  intro i j hij
  exact (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone hij

private lemma lap_eigen_sum {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] :
    ∑ i, lapEig G i = 2 * (G.edgeFinset.card : ℝ) := by
  have hs : (G.lapMatrix ℝ).trace =
      ∑ i : Fin (Fintype.card (Fin N)), (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits
      (G.isHermitian_lapMatrix ℝ).splits_charpoly,
      (G.isHermitian_lapMatrix ℝ).roots_charpoly_eq_eigenvalues₀]
    simp [List.sum_ofFn]
    exact Equiv.sum_comp (finCongr (Fintype.card_fin _).symm) _
  have he : (∑ i, lapEig G i) = (G.lapMatrix ℝ).trace := by
    rw [hs]
    exact Equiv.sum_comp (finCongr (Fintype.card_fin N).symm) _
  rw [he]
  have hd := G.sum_degrees_eq_twice_card_edges
  have hc : (∑ i, (G.degree i : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hd
  simpa [Matrix.trace, Matrix.diag, SimpleGraph.lapMatrix,
    SimpleGraph.degMatrix] using hc

private lemma lap_second_le_edges {n : ℕ} (G : SimpleGraph (Fin (n + 2)))
    [DecidableRel G.Adj] :
    lapEig G (1 : Fin (n + 2)) ≤ (G.edgeFinset.card : ℝ) := by
  have hsum := lap_eigen_sum G
  have hle : lapEig G (0 : Fin (n + 2)) + lapEig G (1 : Fin (n + 2)) ≤
      ∑ i, lapEig G i := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (s := ({0, 1} : Finset (Fin (n + 2)))) (t := univ) (by simp)
      (fun i _ _ => lap_eigen_nonneg G i)
    simpa using hh
  have ho := lap_eigen_antitone G (Fin.zero_le (1 : Fin (n + 2)))
  linarith

private lemma lap_second_order_two (G : SimpleGraph (Fin 2))
    [DecidableRel G.Adj] : lapEig G 1 = 0 := by
  have hz := G.zero_mem_spectrum_lapMatrix ℝ
  rw [(G.isHermitian_lapMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hz
  obtain ⟨i, hi⟩ := hz
  have hlo : lapEig G 1 ≤ (G.isHermitian_lapMatrix ℝ).eigenvalues i := by
    apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
    exact Fin.le_last _
  exact le_antisymm (hi ▸ hlo) (lap_eigen_nonneg G 1)

private lemma pair_energy_le {V : Type*} [DecidableEq V] (s : Finset V) (x : V → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (x i - x j)^2) ≤
      2 * (s.card : ℝ) * (∑ i ∈ s, (x i)^2) := by
  have he : (∑ i ∈ s, ∑ j ∈ s, (x i - x j)^2) =
      2 * (s.card : ℝ) * (∑ i ∈ s, (x i)^2) - 2 * (∑ i ∈ s, x i)^2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, ← sum_mul, ← mul_sum]
    ring
  rw [he]
  nlinarith [sq_nonneg (∑ i ∈ s, x i)]

private lemma second_le_of_hyperplane {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hA : A.IsHermitian)
    (u v : Fin (n + 2)) (c : ℝ)
    (hq : ∀ x : Fin (n + 2) → ℝ, x u = x v →
      x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin (n + 2)).symm 1) ≤ c := by
  let B := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    finrank_euclideanSpace
  let i₀ : Fin (Fintype.card (Fin (n + 2))) :=
    Fin.cast (Fintype.card_fin (n + 2)).symm 0
  let i₁ : Fin (Fintype.card (Fin (n + 2))) :=
    Fin.cast (Fintype.card_fin (n + 2)).symm 1
  let d₀ : ℝ := B i₀ u - B i₀ v
  let d₁ : ℝ := B i₁ u - B i₁ v
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨a, b, hab, hd⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      a * d₀ + b * d₁ = 0 := by
    by_cases h : d₁ = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, by simp [h]⟩
    · exact ⟨d₁, -d₀, Or.inl h, by ring⟩
  let y : EuclideanSpace ℝ (Fin (n + 2)) := a • B i₀ + b • B i₁
  let x : Fin (n + 2) → ℝ := WithLp.ofLp y
  have hyrepr (i) : B.repr y i =
      a * (if i₀ = i then 1 else 0) + b * (if i₁ = i then 1 else 0) := by
    simp [y, eq_comm]
  have hx : x ≠ 0 := by
    intro hx
    have hy : y = 0 := (WithLp.ofLp_eq_zero 2).mp hx
    have h0 := hyrepr i₀
    have h1 := hyrepr i₁
    rw [hy] at h0 h1
    simp [hi, hi.symm] at h0 h1
    exact hab.elim (fun ha => ha h0.symm) (fun hb => hb h1.symm)
  have hsupport : ∀ i, i₁ < i → B.repr (WithLp.toLp 2 x) i = 0 := by
    intro i hi'
    have h1 : i₁ ≠ i := ne_of_lt hi'
    have h0 : i₀ ≠ i := by
      apply ne_of_lt
      exact lt_trans (by simp [i₀, i₁, Fin.lt_def]) hi'
    simpa only [x, WithLp.toLp_ofLp, hyrepr, ite_eq_right h0, ite_eq_right h1,
      mul_zero, add_zero]
  have hlo := LinWangCaiBroomSpectralRatio.rayleigh_ge_of_support hA i₁ x hsupport
  have heq : x u = x v := by
    change (a * B i₀ u + b * B i₁ u) = (a * B i₀ v + b * B i₁ v)
    dsimp [d₀, d₁] at hd
    linarith
  have hu := hq x heq
  have hp : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  exact (mul_le_mul_iff_left₀ hp).mp (hlo.trans hu)

private lemma partition_energy_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P] (c : ℝ)
    (hs : ((univ.filter P).card : ℝ) ≤ c)
    (ht : ((univ.filter (fun i => ¬ P i)).card : ℝ) ≤ c)
    (x : V → ℝ)
    (hcross : ∀ i j, G.Adj i j → ¬ (P i ↔ P j) → x i = x j) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ c * (x ⬝ᵥ x) := by
  let s := univ.filter P
  let t := univ.filter (fun i => ¬ P i)
  have hr (i : V) :
      (∑ j, if G.Adj i j then (x i - x j)^2 else 0) ≤
      if P i then ∑ j ∈ s, (x i - x j)^2 else ∑ j ∈ t, (x i - x j)^2 := by
    by_cases hi : P i
    · rw [ite_eq_left hi]
      dsimp [s]
      rw [sum_filter]
      apply sum_le_sum
      intro j _
      by_cases hj : P j
      · simp only [ite_eq_left hj]
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _
      · simp only [ite_eq_right hj]
        by_cases he : G.Adj i j
        · rw [ite_eq_left he, hcross i j he (by tauto)]
          simp
        · simp [he]
    · rw [ite_eq_right hi]
      dsimp [t]
      rw [sum_filter]
      apply sum_le_sum
      intro j _
      by_cases hj : P j
      · simp only [not_true_eq_false, hj, ite_false]
        by_cases he : G.Adj i j
        · rw [ite_eq_left he, hcross i j he (by tauto)]
          simp
        · simp [he]
      · simp only [hj, not_false_eq_true, ite_true]
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _
  have hb := sum_le_sum (fun i (_ : i ∈ (univ : Finset V)) => hr i)
  have hi : (∑ i, if P i then ∑ j ∈ s, (x i - x j)^2
      else ∑ j ∈ t, (x i - x j)^2) =
      (∑ i ∈ s, ∑ j ∈ s, (x i - x j)^2) +
      (∑ i ∈ t, ∑ j ∈ t, (x i - x j)^2) := by
    rw [sum_ite]
  rw [hi] at hb
  have hse := pair_energy_le s x
  have hte := pair_energy_le t x
  have hsn : 0 ≤ ∑ i ∈ s, (x i)^2 := sum_nonneg (fun i _ => sq_nonneg _)
  have htn : 0 ≤ ∑ i ∈ t, (x i)^2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hn : (∑ i ∈ s, (x i)^2) + (∑ i ∈ t, (x i)^2) = x ⬝ᵥ x := by
    rw [sum_filter_add_sum_filter_not]
    simp [dotProduct, pow_two]
  have hc1 := mul_le_mul_of_nonneg_right hs hsn
  have hc2 := mul_le_mul_of_nonneg_right ht htn
  have he : x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) =
      (∑ i, ∑ j, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
    simpa only [Matrix.toLinearMap₂'_apply'] using G.lapMatrix_toLinearMap₂' ℝ x
  rw [he]
  dsimp [s, t] at hse hte hsn htn hn ⊢
  nlinarith

private lemma full_rank_internal_edge {n : ℕ} (G : SimpleGraph (Fin (n + 3)))
    [DecidableRel G.Adj] (hm : G.edgeFinset.card + 1 = n + 3)
    (hrank : (G.adjMatrix ℝ).rank = n + 3) :
    ∃ u v, G.Adj u v ∧ 2 ≤ G.degree u ∧ 2 ≤ G.degree v := by
  classical
  by_contra! hn
  obtain ⟨u, hu⟩ : ∃ u, 2 ≤ G.degree u := by
    by_contra! h
    have hh : ∑ i, G.degree i ≤ ∑ _ : Fin (n + 3), 1 :=
      sum_le_sum (fun i _ => by have := h i; omega)
    have hd := G.sum_degrees_eq_twice_card_edges
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
    omega
  obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp
    (show 1 < (G.neighborFinset u).card by change 1 < G.degree u; omega)
  have huv : G.Adj u v := by simpa using hv
  have huw : G.Adj u w := by simpa using hw
  have hdv : G.degree v = 1 := by
    have hlo := (G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩
    have hhi := hn u v huv hu
    omega
  have hdw : G.degree w = 1 := by
    have hlo := (G.degree_pos_iff_exists_adj w).mpr ⟨u, huw.symm⟩
    have hhi := hn u w huw hu
    omega
  have hvonly (j) : G.Adj v j ↔ j = u := by
    obtain ⟨a, ha, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdv
    have hau : u = a := huniq u huv.symm
    exact ⟨fun hj => (huniq j hj).trans hau.symm, fun hj => hj ▸ huv.symm⟩
  have hwonly (j) : G.Adj w j ↔ j = u := by
    obtain ⟨a, ha, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdw
    have hau : u = a := huniq u huw.symm
    exact ⟨fun hj => (huniq j hj).trans hau.symm, fun hj => hj ▸ huw.symm⟩
  have hsur : Function.Surjective (G.adjMatrix ℝ).mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hrank)
  obtain ⟨x, hx⟩ := hsur (Pi.single v 1)
  have heq : ((G.adjMatrix ℝ) *ᵥ x) v = ((G.adjMatrix ℝ) *ᵥ x) w := by
    simp [mulVec, dotProduct, SimpleGraph.adjMatrix_apply, hvonly, hwonly]
  rw [hx] at heq
  simpa [hvw.symm] using heq

open SimpleGraph
open D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge
open D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting

private lemma bridge_side_card_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : G.Adj u v) (hu : 2 ≤ G.degree u) :
    2 ≤ (@Finset.filter V (fun x => x ∈ deletedSide G u v u) (Classical.decPred _) univ).card := by
  classical
  obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne
    (s := G.neighborFinset u) (by change 1 < G.degree u; omega) v
  have huw : G.Adj u w := by simpa using hw
  have hd : (G.deleteEdges {s(u, v)}).Adj u w := by
    apply deleteEdges_adj.mpr
    refine ⟨huw, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hwv h.2
    · exact huv.ne h.1
  apply Nat.succ_le_iff.mpr
  apply Finset.one_lt_card.mpr
  refine ⟨u, ?_, w, ?_, huw.ne⟩
  · exact mem_filter.mpr ⟨mem_univ _, SimpleGraph.Reachable.rfl⟩
  · exact mem_filter.mpr ⟨mem_univ _, hd.reachable⟩

private lemma internal_bridge_second {n : ℕ} (G : SimpleGraph (Fin (n + 2)))
    [DecidableRel G.Adj] (hG : G.Connected)
    {u v : Fin (n + 2)} (huv : G.Adj u v) (hb : G.IsBridge s(u, v))
    (hu : 2 ≤ G.degree u) (hv : 2 ≤ G.degree v) :
    lapEig G 1 ≤ (n : ℝ) := by
  classical
  let P : Fin (n + 2) → Prop := fun x => x ∈ deletedSide G u v u
  let s := univ.filter P
  let t := univ.filter (fun x => ¬ P x)
  have hd := deletedSide_disjoint hb
  have hcover := deletedSide_cover hG u v
  have hright (x) : ¬ P x ↔ x ∈ deletedSide G u v v := by
    constructor
    · intro hx
      exact (hcover x).resolve_left hx
    · intro hx hs
      exact Set.disjoint_left.mp hd hs hx
  have hS : 2 ≤ s.card := bridge_side_card_two G huv hu
  have hT : 2 ≤ t.card := by
    have hh := bridge_side_card_two G huv.symm hv
    simpa only [t, P, hright, deletedSide_swap] using hh
  have hsum : s.card + t.card = n + 2 := by
    simpa only [s, t, card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 2)))) P
  have hSc : (s.card : ℝ) ≤ n := by exact_mod_cast (show s.card ≤ n by omega)
  have hTc : (t.card : ℝ) ≤ n := by exact_mod_cast (show t.card ≤ n by omega)
  apply second_le_of_hyperplane (G.lapMatrix ℝ) (G.isHermitian_lapMatrix ℝ) u v n
  intro x heq
  apply partition_energy_le G P n hSc hTc x
  intro i j hij hne
  by_cases hi : P i
  · have hj : ¬ P j := by tauto
    obtain ⟨rfl, rfl⟩ := bridge_side_cross hb hij hi hj
    exact heq
  · have hj : P j := by tauto
    obtain ⟨rfl, rfl⟩ := bridge_side_cross hb hij.symm hj hi
    exact heq.symm

/-- Cazenave's full Laplacian-rank bound, with the ordinary decreasing spectrum. -/
theorem result : claim := by
  intro n G inst hG
  letI := inst
  have hr : (G.adjMatrix ℝ).rank ≤ n + 2 := by
    simpa using Matrix.rank_le_card_width (G.adjMatrix ℝ)
  have hμ := lap_second_le_edges G
  have hconn : n + 2 ≤ G.edgeFinset.card+1 := by
    simpa [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using
      hG.card_vert_le_card_edgeSet_add_one
  by_cases hdense : n + 2 ≤ G.edgeFinset.card
  · have hr' : ((G.adjMatrix ℝ).rank : ℝ) ≤ G.edgeFinset.card :=
      Nat.cast_le.mpr (hr.trans hdense)
    linarith
  have hm : G.edgeFinset.card+1 = n + 2 := by omega
  by_cases hlow : (G.adjMatrix ℝ).rank < n + 2
  · have hr' : ((G.adjMatrix ℝ).rank : ℝ) ≤ G.edgeFinset.card := by
      exact_mod_cast (show (G.adjMatrix ℝ).rank ≤ G.edgeFinset.card by omega)
    linarith
  have hfull : (G.adjMatrix ℝ).rank = n + 2 := by omega
  cases n with
  | zero =>
    have hz := lap_second_order_two G
    have hm' : (G.edgeFinset.card : ℝ) = 1 := by exact_mod_cast (show G.edgeFinset.card=1 by omega)
    have hr' : ((G.adjMatrix ℝ).rank : ℝ) ≤ 2 := by exact_mod_cast hr
    linarith
  | succ k =>
    obtain ⟨u,v,huv,hu,hv⟩ := full_rank_internal_edge G hm hfull
    have htree : G.IsTree := SimpleGraph.isTree_iff_connected_and_card.mpr
      ⟨hG, by simpa [Nat.card_eq_fintype_card, ← G.edgeFinset_card] using hm⟩
    have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.isAcyclic huv
    have hμ' := internal_bridge_second G hG huv hb hu hv
    have hm' : (G.edgeFinset.card : ℝ)+1 = (k + 1:ℕ)+2 := by exact_mod_cast hm
    have hr' : ((G.adjMatrix ℝ).rank : ℝ) ≤ (k + 1:ℕ)+2 := by exact_mod_cast hr
    push_cast at *
    linarith

end D5.S3.Combinatorics.SpectralGraph.CazenaveLaplacianRankBound
