/- GID: D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Independent uniform blow-ups multiply the ordinary maximum cut by the square of block size. -/

import D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation

/-! Exact ordinary cut scaling via finite coordinate rounding. -/

open Finset
open scoped BigOperators
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut

/-- Vertices are encoded pairs, with independent fibres of size s. -/
def blowup {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℕ) : SimpleGraph (Fin (n*s)) :=
  H.comap (fun u => (finProdFinEquiv.symm u).1)

private noncomputable def score {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) : ℤ := by
  classical
  exact ∑ i, ∑ j, if H.Adj i j then x i * (s - x j) else 0

private lemma score_interpolate {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) (i : Fin n) :
    s * score H s x = (s-x i) * score H s (Function.update x i 0) +
      x i * score H s (Function.update x i s) := by
  classical
  simp only [score, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : H.Adj u v
  · have huv : u ≠ v := H.ne_of_adj h
    by_cases hu : u = i <;> by_cases hv : v = i
    · exact False.elim (huv (hu.trans hv.symm))
    all_goals simp [h, Function.update, hu, hv]; ring
  · simp [h]

private lemma score_endpoint {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (hs : 0 < s) (x : Fin n → ℤ) (i : Fin n) (hx : 0 ≤ x i ∧ x i ≤ s) :
    ∃ t : ℤ, (t = 0 ∨ t = s) ∧ score H s x ≤ score H s (Function.update x i t) := by
  have h := score_interpolate H s x i
  by_cases h0 : score H s x ≤ score H s (Function.update x i 0)
  · exact ⟨0, Or.inl rfl, h0⟩
  · refine ⟨s, Or.inr rfl, ?_⟩
    by_contra h1
    have ha := mul_le_mul_of_nonneg_left
      (show score H s (Function.update x i 0) ≤ score H s x - 1 by omega)
      (show 0 ≤ s-x i by omega)
    have hb := mul_le_mul_of_nonneg_left
      (show score H s (Function.update x i s) ≤ score H s x - 1 by omega) hx.1
    nlinarith

/-- Finite coordinate rounding constructs a dominating endpoint occupancy. -/
private theorem round_score {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ) (hs : 0 < s)
    (x : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ s) :
    ∃ y : Fin n → ℤ, (∀ i, y i = 0 ∨ y i = s) ∧ score H s x ≤ score H s y := by
  classical
  have go : ∀ t : Finset (Fin n), ∀ x : Fin n → ℤ,
      (∀ i, 0 ≤ x i ∧ x i ≤ s) →
      ∃ y : Fin n → ℤ, (∀ i, 0 ≤ y i ∧ y i ≤ s) ∧
        score H s x ≤ score H s y ∧ (∀ i ∈ t, y i = 0 ∨ y i = s) ∧
        (∀ i ∉ t, y i = x i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx
      exact ⟨x, hx, le_rfl, by simp, by simp⟩
    | @insert a t ha ih =>
      intro x hx
      obtain ⟨v, hv, hle⟩ := score_endpoint H s hs x a (hx a)
      have hb : ∀ i, 0 ≤ Function.update x a v i ∧ Function.update x a v i ≤ s := by
        intro i
        by_cases hi : i = a
        · subst i; simp only [Function.update_self]; rcases hv with rfl | rfl <;> omega
        · simpa [Function.update_of_ne hi] using hx i
      obtain ⟨y, hy, hxy, hend, hfix⟩ := ih (Function.update x a v) hb
      refine ⟨y, hy, hle.trans hxy, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with hi | hi
        · rw [hi, hfix a ha, Function.update_self]; exact hv
        · exact hend i hi
      · intro i hi
        have hit : i ∉ t := fun h => hi (Finset.mem_insert_of_mem h)
        have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a t)
        rw [hfix i hit, Function.update_of_ne hia]
  obtain ⟨y, _, hle, hy, _⟩ := go Finset.univ x hx
  exact ⟨y, fun i => hy i (Finset.mem_univ i), hle⟩

private noncomputable def occupancy {n s : ℕ} (S : Finset (Fin (n*s))) (i : Fin n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin s)).filter (fun a => finProdFinEquiv (i,a) ∈ S)).card

private lemma occupancy_le {n s : ℕ} (S : Finset (Fin (n*s))) (i : Fin n) :
    occupancy S i ≤ s := by
  classical
  simpa [occupancy] using Finset.card_filter_le (Finset.univ : Finset (Fin s))
    (fun a => finProdFinEquiv (i,a) ∈ S)

private lemma cut_eq_score {n s : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (S : Finset (Fin (n*s))) :
    (((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses S)).card : ℤ) =
      score H s (fun i => occupancy S i) := by
  classical
  let e : Fin n × Fin s ≃ Fin (n*s) := finProdFinEquiv
  have hsum : ∀ i j : Fin n,
      (∑ a : Fin s, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0) =
      if H.Adj i j then (occupancy S i : ℤ) * (s - occupancy S j) else 0 := by
    intro i j
    have hone : ∀ k : Fin n, (∑ a : Fin s, if e (k,a) ∈ S then (1 : ℤ) else 0) =
        occupancy S k := by
      intro k
      simp [occupancy, e, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hzero : (∑ b : Fin s, if e (j,b) ∉ S then (1 : ℤ) else 0) =
        (s : ℤ) - occupancy S j := by
      have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s)))
        (fun b => e (j,b) ∈ S)
      have hc' : (occupancy S j : ℤ) +
          (((Finset.univ : Finset (Fin s)).filter (fun b => e (j,b) ∉ S)).card : ℤ) = s := by
        exact_mod_cast hc
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter] at hc'
      exact eq_sub_of_add_eq' hc'
    by_cases hij : H.Adj i j
    · simp only [hij, true_and, if_true]
      calc
        _ = (∑ a : Fin s, if e (i,a) ∈ S then (1 : ℤ) else 0) *
            (∑ b : Fin s, if e (j,b) ∉ S then (1 : ℤ) else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          by_cases ha : e (i,a) ∈ S <;> by_cases hb : e (j,b) ∈ S <;> simp [ha,hb]
        _ = _ := by rw [hone, hzero]
    · simp [hij]
  calc
    _ = ∑ u : Fin (n*s), ∑ v : Fin (n*s),
        if (blowup H s).Adj u v ∧ u ∈ S ∧ v ∉ S then (1 : ℤ) else 0 := by
      rw [CutBoundRefutation.cut_card_eq_sum]
      push_cast
      rfl
    _ = ∑ p : Fin n × Fin s, ∑ q : Fin n × Fin s,
        if H.Adj p.1 q.1 ∧ e p ∈ S ∧ e q ∉ S then (1 : ℤ) else 0 := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro p _
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro q _
      simp [blowup, e, SimpleGraph.comap_adj]
    _ = ∑ i : Fin n, ∑ a : Fin s, ∑ j : Fin n, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin s, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp only [score, hsum]

end D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
