/- GID: D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform independent blow-ups scale ordinary maximum cuts quadratically. -/

import D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation

/-! Exact ordinary cut scaling via finite coordinate rounding. -/

open Finset
open scoped BigOperators
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut

/-- Vertices are encoded pairs, with independent fibres of size s. -/
def blowup {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℕ) : SimpleGraph (Fin (n * s)) :=
  H.comap (fun u => (finProdFinEquiv.symm u).1)

instance blowupDecidableAdj {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (s : ℕ) : DecidableRel (blowup H s).Adj :=
  fun u v => inferInstanceAs
    (Decidable (H.Adj (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm v).1))

/-- The lift places an entire block on the side chosen by its base vertex. -/
noncomputable def liftCut {n : ℕ} (s : ℕ) (T : Finset (Fin n)) : Finset (Fin (n * s)) := by
  classical
  exact Finset.univ.filter (fun u => (finProdFinEquiv.symm u).1 ∈ T)

private noncomputable def score {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) : ℤ := by
  classical
  exact ∑ i, ∑ j, if H.Adj i j then x i * (s - x j) else 0

private lemma score_interpolate {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) (i : Fin n) :
    s * score H s x = (s - x i) * score H s (Function.update x i 0) +
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
    all_goals simp [h, Function.update, hu, hv] <;> ring
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
      (show 0 ≤ s - x i by omega)
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

private noncomputable def occupancy {n s : ℕ} (S : Finset (Fin (n * s))) (i : Fin n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin s)).filter (fun a => finProdFinEquiv (i,a) ∈ S)).card

private lemma occupancy_le {n s : ℕ} (S : Finset (Fin (n * s))) (i : Fin n) :
    occupancy S i ≤ s := by
  classical
  simpa [occupancy] using Finset.card_filter_le (Finset.univ : Finset (Fin s))
    (fun a => finProdFinEquiv (i,a) ∈ S)

open Classical in
private lemma cut_eq_score {n s : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (S : Finset (Fin (n * s))) :
    (((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses S)).card : ℤ) =
      score H s (fun i => occupancy S i) := by
  classical
  let e : Fin n × Fin s ≃ Fin (n * s) := finProdFinEquiv
  have hsum : ∀ i j : Fin n,
      (∑ a : Fin s, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0) =
      if H.Adj i j then (occupancy S i : ℤ) * (s - occupancy S j) else 0 := by
    intro i j
    have hone : ∀ k : Fin n, (∑ a : Fin s, if e (k,a) ∈ S then (1 : ℤ) else 0) =
        occupancy S k := by
      intro k
      simp only [occupancy, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    have hzero : (∑ b : Fin s, if e (j,b) ∉ S then (1 : ℤ) else 0) =
        (s : ℤ) - occupancy S j := by
      have ht : (∑ b : Fin s, if e (j,b) ∈ S then (1 : ℤ) else 0) +
          (∑ b : Fin s, if e (j,b) ∉ S then (1 : ℤ) else 0) = s := by
        rw [← Finset.sum_add_distrib]
        calc
          _ = ∑ _b : Fin s, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hb : e (j,b) ∈ S <;> simp [hb]
          _ = _ := by simp
      rw [hone] at ht
      omega
    by_cases hij : H.Adj i j
    · simp only [hij, true_and, ite_true]
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
    _ = ∑ u : Fin (n * s), ∑ v : Fin (n * s),
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
      change (if H.Adj (e.symm (e p)).1 (e.symm (e q)).1 ∧
        e p ∈ S ∧ e q ∉ S then (1 : ℤ) else 0) = _
      simp only [Equiv.symm_apply_apply]
    _ = ∑ i : Fin n, ∑ a : Fin s, ∑ j : Fin n, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin s, ∑ b : Fin s,
        if H.Adj i j ∧ e (i,a) ∈ S ∧ e (j,b) ∉ S then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp only [score, hsum]

private lemma occupancy_lift {n s : ℕ} (T : Finset (Fin n)) (i : Fin n) :
    occupancy (liftCut s T) i = if i ∈ T then s else 0 := by
  classical
  have hp : ∀ a : Fin s, finProdFinEquiv (i,a) ∈ liftCut s T ↔ i ∈ T := by
    intro a
    change finProdFinEquiv (i,a) ∈ Finset.univ.filter _ ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  simp only [occupancy, hp]
  by_cases hi : i ∈ T <;> simp [hi]

open Classical in
private lemma lift_count {n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : Finset (Fin n)) :
    ((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses (liftCut s T))).card =
      s^2 * (H.edgeFinset.filter (CutBoundRefutation.crosses T)).card := by
  classical
  have he : (((blowup H s).edgeFinset.filter
        (CutBoundRefutation.crosses (liftCut s T))).card : ℤ) =
      (s : ℤ)^2 * (H.edgeFinset.filter (CutBoundRefutation.crosses T)).card := by
    rw [cut_eq_score, CutBoundRefutation.cut_card_eq_sum]
    simp only [score, occupancy_lift]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : H.Adj i j <;> by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
      simp [hij, hi, hj, pow_two]
  exact_mod_cast he

/-- Any cut is dominated by a cut consisting of whole blocks. -/
open Classical in
theorem exists_block_cut {n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hs : 1 ≤ s) (S : Finset (Fin (n * s))) :
    ∃ T : Finset (Fin n),
      ((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses S)).card ≤
      ((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses (liftCut s T))).card := by
  classical
  obtain ⟨y, hy, hle⟩ := round_score H (s : ℤ) (by omega)
    (fun i => (occupancy S i : ℤ)) (fun i => ⟨by positivity, by exact_mod_cast occupancy_le S i⟩)
  let T : Finset (Fin n) := Finset.univ.filter (fun i => y i = s)
  have heq : ∀ i, (occupancy (liftCut s T) i : ℤ) = y i := by
    intro i
    rw [occupancy_lift]
    by_cases hi : y i = s
    · simp [T, hi]
    · have hz : y i = 0 := (hy i).resolve_right hi
      have hit : i ∉ T := by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      simp [hit, hz]
  refine ⟨T, ?_⟩
  have hc : (((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses S)).card : ℤ) ≤
      ((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses (liftCut s T))).card := by
    rw [cut_eq_score, cut_eq_score]
    simpa only [heq] using hle
  exact_mod_cast hc

/-- Ordinary unordered edge counts scale by s squared, including empty graphs. -/
theorem maxCut_blowup {n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hs : 1 ≤ s) :
    CutBoundRefutation.maxCut (blowup H s) = s^2 * CutBoundRefutation.maxCut H := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S _
    obtain ⟨T, hT⟩ := exists_block_cut H hs S
    rw [lift_count] at hT
    exact hT.trans (Nat.mul_le_mul_left _ (Finset.le_sup
      (f := fun U => (H.edgeFinset.filter (CutBoundRefutation.crosses U)).card)
      (Finset.mem_univ T)))
  · obtain ⟨T, _, hT⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Finset (Fin n))) ⟨∅, Finset.mem_univ _⟩
      (fun T => (H.edgeFinset.filter (CutBoundRefutation.crosses T)).card)
    change CutBoundRefutation.maxCut H = _ at hT
    rw [hT, ← lift_count H T]
    exact Finset.le_sup
      (f := fun U => ((blowup H s).edgeFinset.filter (CutBoundRefutation.crosses U)).card)
      (Finset.mem_univ (liftCut s T))

#print axioms exists_block_cut
#print axioms maxCut_blowup

end D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
