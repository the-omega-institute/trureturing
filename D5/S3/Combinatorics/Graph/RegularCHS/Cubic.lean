/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Cubic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Cubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum, mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Minimum degree return bounds and cubic graph domination of cycle moments. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Interface
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Classical Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Interface

namespace D5.S3.Combinatorics.Graph.RegularCHS.Cubic

private lemma pow_symm {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (v w : Fin n) :
    ((G.adjMatrix ℕ) ^ k) v w = ((G.adjMatrix ℕ) ^ k) w v := by
  exact (G.isSymm_adjMatrix.pow k).apply w v

private lemma even_closed_eq {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) :
    closedWalks G (2 * j) = ∑ v, ∑ w, ((G.adjMatrix ℕ) ^ j) v w ^ 2 := by
  simp only [closedWalks, two_mul, pow_add, Matrix.mul_apply]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  rw [pow_symm G j w v, pow_two]

private lemma row_sum_ge {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : ∀ v, r ≤ G.degree v) (j : ℕ) (v : Fin n) :
    r ^ j ≤ ∑ w, ((G.adjMatrix ℕ) ^ j) v w := by
  induction j generalizing v with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ' (G.adjMatrix ℕ)]
    simp only [SimpleGraph.adjMatrix_mul_apply]
    rw [sum_comm]
    calc
      r ^ (j + 1) = r * r ^ j := pow_succ' r j
      _ ≤ G.degree v * r ^ j := Nat.mul_le_mul_right _ (hr v)
      _ = ∑ _u ∈ G.neighborFinset v, r ^ j := by simp
      _ ≤ _ := sum_le_sum fun u _ => ih u

/-- Even closed walks dominate walks of half the length in a minimum-degree graph. -/
theorem closedWalks_ge_of_minDegree {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : ∀ v, r ≤ G.degree v) (j : ℕ) :
    n * r ^ j ≤ closedWalks G (2 * j) := by
  rw [even_closed_eq]
  calc
    n * r ^ j = ∑ _v : Fin n, r ^ j := by simp
    _ ≤ ∑ v, ∑ w, ((G.adjMatrix ℕ) ^ j) v w :=
      sum_le_sum fun v _ => row_sum_ge G hr j v
    _ ≤ _ := sum_le_sum fun v _ => sum_le_sum fun w _ => by
      simpa [pow_two] using Nat.le_mul_self (((G.adjMatrix ℕ) ^ j) v w)

private lemma row_sum_eq {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree r) (j : ℕ) (v : Fin n) :
    (∑ w, ((G.adjMatrix ℕ) ^ j) v w) = r ^ j := by
  induction j generalizing v with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ' (G.adjMatrix ℕ)]
    simp only [SimpleGraph.adjMatrix_mul_apply]
    rw [sum_comm]
    simp [ih, hr v, pow_succ, mul_comm]

private lemma square_diag {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ((G.adjMatrix ℕ) ^ 2) v v = G.degree v := by
  simpa [pow_two] using G.adjMatrix_mul_self_apply_self (α := ℕ) v

private lemma second_eq {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree r) : closedWalks G 2 = n * r := by
  simp only [closedWalks, square_diag, hr.degree_eq, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

private lemma cubic_fourth_ge {n : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree 3) : n * 15 ≤ closedWalks G 4 := by
  rw [show 4 = 2 * 2 from rfl, even_closed_eq]
  calc
    n * 15 = ∑ _v : Fin n, 15 := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro v _
      have hrow := row_sum_eq G hr 2 v
      have hd := square_diag G v
      rw [hr v] at hd
      have hle : (∑ w ∈ univ.erase v, ((G.adjMatrix ℕ) ^ 2) v w) ≤
          ∑ w ∈ univ.erase v, ((G.adjMatrix ℕ) ^ 2) v w ^ 2 := by
        apply sum_le_sum
        intro w _
        exact (Nat.le_mul_self (((G.adjMatrix ℕ) ^ 2) v w)).trans_eq (pow_two _).symm
      rw [← sum_erase_add _ _ (mem_univ v)] at hrow ⊢
      rw [hd] at hrow ⊢
      norm_num at hrow ⊢
      omega

private lemma square_entry_le_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : Fin n) : ((G.adjMatrix ℕ) ^ 2) v w ≤ G.degree v := by
  rw [pow_two, SimpleGraph.adjMatrix_mul_apply]
  calc
    _ ≤ ∑ _u ∈ G.neighborFinset v, 1 := by
      apply sum_le_sum
      intro u _
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> omega
    _ = _ := by simp

private lemma twoRegular_fourth_le {n : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree 2) : closedWalks G 4 ≤ n * 8 := by
  rw [show 4 = 2 * 2 from rfl, even_closed_eq]
  calc
    _ ≤ ∑ v, ∑ w, 2 * ((G.adjMatrix ℕ) ^ 2) v w := by
      apply sum_le_sum
      intro v _
      apply sum_le_sum
      intro w _
      have h := square_entry_le_degree G v w
      rw [hr v] at h
      nlinarith
    _ = _ := by simp_rw [← mul_sum, row_sum_eq G hr 2]; simp; omega

private lemma split_closed_eq {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℕ) :
    closedWalks G (a + b) =
      ∑ p : Fin n × Fin n, ((G.adjMatrix ℕ) ^ a) p.1 p.2 *
        ((G.adjMatrix ℕ) ^ b) p.1 p.2 := by
  simp only [closedWalks, pow_add, Matrix.mul_apply, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  rw [pow_symm G b w v]

private lemma even_log_convex {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) :
    closedWalks G (2 * (m + 1)) ^ 2 ≤
      closedWalks G (2 * m) * closedWalks G (2 * (m + 2)) := by
  rw [show 2 * (m + 1) = m + (m + 2) by omega, split_closed_eq]
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n × Fin n))
    (fun p => ((G.adjMatrix ℕ) ^ m) p.1 p.2)
    (fun p => ((G.adjMatrix ℕ) ^ (m + 2)) p.1 p.2)
  simpa only [Fintype.sum_prod_type, ← even_closed_eq] using h

private lemma cubic_growth {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree 3) (m : ℕ) (hm : 1 ≤ m) :
    5 * closedWalks G (2 * m) ≤ closedWalks G (2 * (m + 1)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h := cubic_fourth_ge G hr
    simpa [second_eq G hr, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  | succ m hm ih =>
    have hp : 0 < closedWalks G (2 * m) := lt_of_lt_of_le
      (Nat.mul_pos hn (pow_pos (by omega : 0 < 3) m))
      (closedWalks_ge_of_minDegree G (fun v => (hr v).ge) m)
    have hc := even_log_convex G m
    have he : closedWalks G (2 * m) * (5 * closedWalks G (2 * (m + 1))) ≤
        closedWalks G (2 * m) * closedWalks G (2 * (m + 2)) := by
      calc
        _ = (5 * closedWalks G (2 * m)) * closedWalks G (2 * (m + 1)) := by ring
        _ ≤ closedWalks G (2 * (m + 1)) ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul_right (closedWalks G (2 * (m + 1))) ih
        _ ≤ _ := hc
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa [mul_comm, Nat.add_assoc] using he)

private lemma cubic_even_ge {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree 3) (m : ℕ) (hm : 3 ≤ m) :
    n * 4 ^ m ≤ closedWalks G (2 * m) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h4 := cubic_fourth_ge G hr
    have h6 := cubic_growth hn G hr 2 (by omega)
    norm_num at h6 ⊢
    omega
  | succ m hm ih =>
    calc
      n * 4 ^ (m + 1) = 4 * (n * 4 ^ m) := by rw [pow_succ]; ring
      _ ≤ 4 * closedWalks G (2 * m) := Nat.mul_le_mul_left _ ih
      _ ≤ 5 * closedWalks G (2 * m) := by omega
      _ ≤ _ := cubic_growth hn G hr m (by omega)

private lemma regular_closed_le {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree r) (k : ℕ) : closedWalks G k ≤ n * r ^ k := by
  calc
    closedWalks G k ≤ ∑ v, ∑ w, ((G.adjMatrix ℕ) ^ k) v w := by
      apply sum_le_sum
      intro v _
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    _ = _ := by simp [row_sum_eq G hr]

private lemma cycle_regular {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).IsRegularOfDegree 2 := by
  classical
  match n with
  | 0 | 1 | 2 => omega
  | n + 3 => exact fun _ => SimpleGraph.cycleGraph_degree_three_le

private lemma cubic_even_card {n : ℕ} (G : SimpleGraph (Fin n))
    (hr : G.IsRegularOfDegree 3) : Even n := by
  have h := G.even_card_odd_degree_vertices
  simpa only [hr.degree_eq, show Odd 3 from by decide, filter_true, card_univ, Fintype.card_fin] using h

private lemma bicoloring_odd_closed_zero {n k : ℕ} (G : SimpleGraph (Fin n))
    (c : G.Coloring Bool) (hk : Odd k) : closedWalks G k = 0 := by
  classical
  apply sum_eq_zero
  intro v _
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  have he : IsEmpty {p : G.Walk v v | p.length = k} := by
    constructor
    intro p
    have hh := c.even_length_iff_congr p.val
    have hp : Even p.val.length := hh.mpr Iff.rfl
    rw [p.property] at hp
    exact (Nat.not_even_iff_odd.mpr hk) hp
  exact Fintype.card_eq_zero

/-- A cubic graph dominates the cycle in every positive closed walk count. -/
theorem closedWalks_cubic_ge_cycle {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 3 ≤ n) (hr : G.IsRegularOfDegree 3) (k : ℕ) (hk : 1 ≤ k) :
    closedWalks (SimpleGraph.cycleGraph n) k ≤ closedWalks G k := by
  classical
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, rfl⟩ := he
    rw [← two_mul]
    have hreg : (fun H : SimpleGraph (Fin n) => H.IsRegularOfDegree 2)
        (SimpleGraph.cycleGraph n) := by
      intro v
      simpa only [← SimpleGraph.ncard_neighborSet] using cycle_regular hn v
    by_cases hm0 : m = 0
    · subst m
      omega
    by_cases hm1 : m = 1
    · subst m
      simp only [mul_one, second_eq _ hreg, second_eq _ hr]
      omega
    by_cases hm2 : m = 2
    · subst m
      have hc := twoRegular_fourth_le _ hreg
      have hg := cubic_fourth_ge G hr
      norm_num
      omega
    have hm : 3 ≤ m := by omega
    calc
      _ ≤ n * 2 ^ (2 * m) := regular_closed_le _ hreg _
      _ = n * 4 ^ m := by rw [pow_mul]; norm_num
      _ ≤ _ := cubic_even_ge (by omega) G hr m hm
  · rw [bicoloring_odd_closed_zero _
      (SimpleGraph.cycleGraph.bicoloring_of_even n (cubic_even_card G hr)) ho]
    exact Nat.zero_le _

end D5.S3.Combinatorics.Graph.RegularCHS.Cubic
