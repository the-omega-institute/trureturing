/- GID: D5/S3/Combinatorics/VoronoiGames/FacilityAdvantageTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VoronoiGames/FacilityAdvantageTwo
   mirror-E: none(waiver:local-response-geometric-argument)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Two responders retain at most four gadget voters against any two leaders. -/

import D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageTwo

open FacilityAdvantageDefs

theorem two_response (A : Finset ℝ) (hA : A.card = 2) :
    ∃ Q : Finset ℝ, Q.card = 2 ∧ (∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5) ∧
      won (([0, 0, 1, 2, 3, 3, 4, 5, 5] : List ℝ) : Multiset ℝ) A Q ≤ 4 := by
  classical
  have pair_eq (x y : ℝ) (hxy : x ≠ y) (hx : x ∈ A) (hy : y ∈ A) :
      A = {x, y} := by
    apply (Finset.eq_of_subset_of_card_le (s := {x, y}) (t := A) _ _).symm
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hx, hy⟩
    · simp [hA, Finset.card_pair hxy]
  have explicit (P Q : Finset ℝ)
      (heq : A = P) (hQ : Q.card = 2) (hb : ∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5)
      (hc : won (([0, 0, 1, 2, 3, 3, 4, 5, 5] : List ℝ) : Multiset ℝ) P Q ≤ 4) :
      ∃ Q : Finset ℝ, Q.card = 2 ∧ (∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5) ∧
        won (([0, 0, 1, 2, 3, 3, 4, 5, 5] : List ℝ) : Multiset ℝ) A Q ≤ 4 := by
    exact ⟨Q, hQ, hb, heq ▸ hc⟩
  by_cases h03 : (0 : ℝ) ∈ A ∧ 3 ∈ A
  · apply explicit {0, 3} {(3 / 2 : ℝ), 9 / 2} (pair_eq 0 3 (by norm_num) h03.1 h03.2)
    · norm_num
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    · norm_num [won, Multiset.filter_cons, abs_of_nonneg, abs_of_nonpos]
  by_cases h05 : (0 : ℝ) ∈ A ∧ 5 ∈ A
  · apply explicit {0, 5} {(3 / 2 : ℝ), 7 / 2} (pair_eq 0 5 (by norm_num) h05.1 h05.2)
    · norm_num
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    · norm_num [won, Multiset.filter_cons, abs_of_nonneg, abs_of_nonpos]
  by_cases h35 : (3 : ℝ) ∈ A ∧ 5 ∈ A
  · apply explicit {3, 5} {(3 / 2 : ℝ), 4} (pair_eq 3 5 (by norm_num) h35.1 h35.2)
    · norm_num
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    · norm_num [won, Multiset.filter_cons, abs_of_nonneg, abs_of_nonpos]
  have general (p q : ℝ) (hpq : p < q) (hpair : A = {p, q}) :
      ∃ Q : Finset ℝ, Q.card = 2 ∧ (∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5) ∧
        won (([0, 0, 1, 2, 3, 3, 4, 5, 5] : List ℝ) : Multiset ℝ) A Q ≤ 4 := by
    have kill (v t : ℝ) (Q : Finset ℝ) (ht : t ∈ Q)
        (hp : |v - t| < |v - p|) (hq : |v - t| < |v - q|) :
        ¬ (∀ z ∈ Q, ∃ x ∈ A, |v - x| ≤ |v - z|) := by
      intro hw
      obtain ⟨x, hx, hd⟩ := hw t ht
      rw [hpair] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> linarith
    have vacant (v : ℝ) (Q : Finset ℝ) (hv : v ∈ Q) (hn : v ∉ A) :
        ¬ (∀ z ∈ Q, ∃ x ∈ A, |v - x| ≤ |v - z|) := by
      intro hw
      obtain ⟨x, hx, hd⟩ := hw v hv
      have hz : |v - x| = 0 := le_antisymm (by simpa using hd) (abs_nonneg _)
      have he : v = x := sub_eq_zero.mp (abs_eq_zero.mp hz)
      exact hn (he ▸ hx)
    by_cases hp : 1 < p
    · have h0 (Q : Finset ℝ) (ht : (1 : ℝ) ∈ Q) :
          ¬ (∀ z ∈ Q, ∃ x ∈ A, |(0 : ℝ) - x| ≤ |0 - z|) := by
        apply kill 0 1 Q ht
        · rw [abs_of_nonpos (by linarith : 0 - p ≤ 0)]
          norm_num
          linarith
        · rw [abs_of_nonpos (by linarith : 0 - q ≤ 0)]
          norm_num
          linarith
      have h1 (Q : Finset ℝ) (ht : (1 : ℝ) ∈ Q) :
          ¬ (∀ z ∈ Q, ∃ x ∈ A, |(1 : ℝ) - x| ≤ |1 - z|) := by
        apply kill 1 1 Q ht
        · rw [abs_of_nonpos (by linarith : 1 - p ≤ 0)]
          norm_num
          linarith
        · rw [abs_of_nonpos (by linarith : 1 - q ≤ 0)]
          norm_num
          linarith
      by_cases h3 : (3 : ℝ) ∉ A
      · refine ⟨{1, 3}, by norm_num, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> norm_num
        · have e0 := h0 {1, 3} (by simp)
          have e1 := h1 {1, 3} (by simp)
          have e3 := vacant 3 {1, 3} (by simp) h3
          change (Multiset.filter
            (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
            (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
          simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
            e0, e1, e3, if_false]
          split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
      · have h5 : (5 : ℝ) ∉ A := by tauto
        refine ⟨{1, 5}, by norm_num, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> norm_num
        · have e0 := h0 {1, 5} (by simp)
          have e1 := h1 {1, 5} (by simp)
          have e5 := vacant 5 {1, 5} (by simp) h5
          change (Multiset.filter
            (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
            (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
          simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
            e0, e1, e5, if_false]
          split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
    by_cases hq : q < 4
    · have h4 (Q : Finset ℝ) (ht : (4 : ℝ) ∈ Q) :
          ¬ (∀ z ∈ Q, ∃ x ∈ A, |(4 : ℝ) - x| ≤ |4 - z|) := by
        apply kill 4 4 Q ht
        · rw [abs_of_nonneg (by linarith : 0 ≤ 4 - p)]
          norm_num
          linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ 4 - q)]
          norm_num
          linarith
      have h5 (Q : Finset ℝ) (ht : (4 : ℝ) ∈ Q) :
          ¬ (∀ z ∈ Q, ∃ x ∈ A, |(5 : ℝ) - x| ≤ |5 - z|) := by
        apply kill 5 4 Q ht
        · rw [abs_of_nonneg (by linarith : 0 ≤ 5 - p)]
          norm_num
          linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ 5 - q)]
          norm_num
          linarith
      by_cases h0 : (0 : ℝ) ∉ A
      · refine ⟨{4, 0}, by norm_num, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> norm_num
        · have e4 := h4 {4, 0} (by simp)
          have e5 := h5 {4, 0} (by simp)
          have e0 := vacant 0 {4, 0} (by simp) h0
          change (Multiset.filter
            (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
            (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
          simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
            e4, e5, e0, if_false]
          split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
      · have h3 : (3 : ℝ) ∉ A := by tauto
        refine ⟨{4, 3}, by norm_num, ?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> norm_num
        · have e4 := h4 {4, 3} (by simp)
          have e5 := h5 {4, 3} (by simp)
          have e3 := vacant 3 {4, 3} (by simp) h3
          change (Multiset.filter
            (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
            (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
          simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
            e4, e5, e3, if_false]
          split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
    have h2 (Q : Finset ℝ) (ht : (5 / 2 : ℝ) ∈ Q) :
        ¬ (∀ z ∈ Q, ∃ x ∈ A, |(2 : ℝ) - x| ≤ |2 - z|) := by
      apply kill 2 (5 / 2) Q ht
      · rw [abs_of_nonneg (by linarith : 0 ≤ 2 - p)]
        norm_num
        linarith
      · rw [abs_of_nonpos (by linarith : 2 - q ≤ 0)]
        norm_num
        linarith
    have h3 (Q : Finset ℝ) (ht : (5 / 2 : ℝ) ∈ Q) :
        ¬ (∀ z ∈ Q, ∃ x ∈ A, |(3 : ℝ) - x| ≤ |3 - z|) := by
      apply kill 3 (5 / 2) Q ht
      · rw [abs_of_nonneg (by linarith : 0 ≤ 3 - p)]
        norm_num
        linarith
      · rw [abs_of_nonpos (by linarith : 3 - q ≤ 0)]
        norm_num
        linarith
    by_cases h0 : (0 : ℝ) ∉ A
    · refine ⟨{(5 / 2 : ℝ), 0}, by norm_num, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> norm_num
      · have e2 := h2 {(5 / 2 : ℝ), 0} (by simp)
        have e3 := h3 {(5 / 2 : ℝ), 0} (by simp)
        have e0 := vacant 0 {(5 / 2 : ℝ), 0} (by simp) h0
        change (Multiset.filter
          (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
          (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
        simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
          e2, e3, e0, if_false]
        split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
    · have h5 : (5 : ℝ) ∉ A := by tauto
      refine ⟨{(5 / 2 : ℝ), 5}, by norm_num, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> norm_num
      · have e2 := h2 {(5 / 2 : ℝ), 5} (by simp)
        have e3 := h3 {(5 / 2 : ℝ), 5} (by simp)
        have e5 := vacant 5 {(5 / 2 : ℝ), 5} (by simp) h5
        change (Multiset.filter
          (fun v => ∀ z ∈ _, ∃ x ∈ A, |v - x| ≤ |v - z|)
          (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)).card ≤ 4
        simp only [Multiset.filter_cons, Multiset.filter_zero, Multiset.card_add,
          e2, e3, e5, if_false]
        split_ifs <;> simp only [Multiset.card_zero, Multiset.card_singleton] <;> omega
  obtain ⟨p, q, hpq, hpair⟩ := Finset.card_eq_two.mp hA
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact general p q hlt hpair
  · exact general q p hgt (by simpa [Finset.pair_comm] using hpair)

end D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageTwo
