/- GID: D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The second largest ordinary Laplacian eigenvalue plus real adjacency rank is at most twice the edge count. -/

import D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio
import D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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
  have ht := (G.isHermitian_lapMatrix ℝ).trace_eq_sum_eigenvalues
  have hs : (G.lapMatrix ℝ).trace =
      ∑ i : Fin (Fintype.card (Fin N)), (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits
      (G.isHermitian_lapMatrix ℝ).splits_charpoly,
      (G.isHermitian_lapMatrix ℝ).roots_charpoly_eq_eigenvalues₀]
    simp
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
  have ho := lap_eigen_antitone G (show (0 : Fin (n+2)) ≤ 1 by decide)
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
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, sum_mul, mul_sum,
      sum_const, nsmul_eq_mul]
    ring
  rw [he]
  nlinarith [sq_nonneg (∑ i ∈ s, x i)]

private lemma second_le_of_hyperplane {n : ℕ}
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.IsHermitian)
    (u v : Fin (n+2)) (c : ℝ)
    (hq : ∀ x : Fin (n+2) → ℝ, x u = x v →
      x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin (n+2)).symm 1) ≤ c := by
  let B := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    finrank_euclideanSpace
  let i₀ : Fin (Fintype.card (Fin (n+2))) :=
    Fin.cast (Fintype.card_fin (n+2)).symm 0
  let i₁ : Fin (Fintype.card (Fin (n+2))) :=
    Fin.cast (Fintype.card_fin (n+2)).symm 1
  let d₀ : ℝ := B i₀ u - B i₀ v
  let d₁ : ℝ := B i₁ u - B i₁ v
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨a, b, hab, hd⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      a * d₀ + b * d₁ = 0 := by
    by_cases h : d₁ = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, by simp [h]⟩
    · exact ⟨d₁, -d₀, Or.inl h, by ring⟩
  let y : EuclideanSpace ℝ (Fin (n+2)) := a • B i₀ + b • B i₁
  let x : Fin (n+2) → ℝ := WithLp.ofLp y
  have hyrepr (i) : B.repr y i =
      a * (if i₀ = i then 1 else 0) + b * (if i₁ = i then 1 else 0) := by
    simp [y, apply_ite]
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
      exact lt_trans (by simp [i₀, i₁, Fin.lt_iff_val_lt_val]) hi'
    simpa only [x, WithLp.toLp_ofLp, hyrepr, if_neg h0, if_neg h1,
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
    · rw [if_pos hi]
      dsimp [s]
      rw [sum_filter]
      apply sum_le_sum
      intro j _
      by_cases hj : P j
      · simp only [if_pos hj]
        split_ifs <;> positivity
      · simp only [if_neg hj]
        by_cases he : G.Adj i j
        · rw [if_pos he, hcross i j he (by tauto)]
          simp
        · simp [he]
    · rw [if_neg hi]
      dsimp [t]
      rw [sum_filter]
      apply sum_le_sum
      intro j _
      by_cases hj : P j
      · simp only [not_true_eq_false, hj, if_false]
        by_cases he : G.Adj i j
        · rw [if_pos he, hcross i j he (by tauto)]
          simp
        · simp [he]
      · simp only [hj, not_false_eq_true, if_true]
        split_ifs <;> positivity
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
    exact G.lapMatrix_toLinearMap₂' ℝ x
  rw [he]
  dsimp [s, t] at hse hte hsn htn hn ⊢
  nlinarith

private lemma full_rank_internal_edge {n : ℕ} (G : SimpleGraph (Fin (n+3)))
    [DecidableRel G.Adj] (hm : G.edgeFinset.card + 1 = n+3)
    (hrank : (G.adjMatrix ℝ).rank = n+3) :
    ∃ u v, G.Adj u v ∧ 2 ≤ G.degree u ∧ 2 ≤ G.degree v := by
  classical
  by_contra! hn
  obtain ⟨u, hu⟩ : ∃ u, 2 ≤ G.degree u := by
    by_contra! h
    have hh : ∑ i, G.degree i ≤ ∑ _ : Fin (n+3), 1 :=
      sum_le_sum (fun i _ => by have := h i; omega)
    have hd := G.sum_degrees_eq_twice_card_edges
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
    omega
  obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp
    (show 1 < G.neighborFinset u |>.card by simpa using hu)
  have huv : G.Adj u v := by simpa using hv
  have huw : G.Adj u w := by simpa using hw
  have hdv : G.degree v = 1 := by
    have hlo := G.degree_pos_iff_exists_adj.mpr ⟨u, huv.symm⟩
    have hhi := hn u v huv hu
    omega
  have hdw : G.degree w = 1 := by
    have hlo := G.degree_pos_iff_exists_adj.mpr ⟨u, huw.symm⟩
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

end D5.S3.Combinatorics.SpectralGraph.CazenaveLaplacianRankBound
