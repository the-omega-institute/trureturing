/- GID: D5/S3/Combinatorics/VoronoiGames/FacilityAdvantageLocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VoronoiGames/FacilityAdvantageLocal
   mirror-E: none(waiver:local-response-geometry)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Two responders capture all but twice the number of leaders in the nine-voter gadget. -/

import D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageDefs
import D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageTwo
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageLocal

open FacilityAdvantageDefs

/-- The nine-voter gadget, with multiplicities retained. -/
def B : Multiset ℝ := (([0, 0, 1, 2, 3, 3, 4, 5, 5] : List ℝ) : Multiset ℝ)

/-- A response within the gadget captures all but twice the number of leaders. -/
theorem local_response (A : Finset ℝ) :
    ∃ Q : Finset ℝ, Q.card = 2 ∧ (∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5) ∧
      won B A Q ≤ 2 * A.card := by
  classical
  let T : Finset ℝ := {0, 1, 2, 3, 4, 5}
  let H : Finset ℝ := {0, 3, 5}
  have bounds : ∀ x ∈ T, 0 ≤ x ∧ x ≤ 5 := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have capture (Q : Finset ℝ) (x : ℝ) (hx : x ∉ A) (hQ : x ∈ Q) :
      ¬ (∀ q ∈ Q, ∃ p ∈ A, |x - p| ≤ |x - q|) := by
    intro hw
    obtain ⟨p, hp, hdist⟩ := hw x hQ
    have heq : x - p = 0 := abs_eq_zero.mp (le_antisymm (by simpa using hdist)
      (abs_nonneg _))
    exact hx (by have : x = p := sub_eq_zero.mp heq; simpa [this] using hp)
  by_cases ha0 : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp ha0
    refine ⟨{0, 5}, by norm_num, ?_, ?_⟩
    · intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    · have hz : won B A {0, 5} = 0 := by
        unfold won
        rw [Multiset.filter_eq_nil.mpr]
        · rfl
        · intro x _ hw
          obtain ⟨p, hp, _⟩ := hw 0 (by simp)
          simp [hA] at hp
      simp [hz]
  by_cases ha1 : A.card = 1
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp ha1
    have single (Q : Finset ℝ) (hq : Q.card = 2)
        (hqb : ∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5)
        (hc : ∀ x ∈ T, x ≠ p → ∃ q ∈ Q, |x - q| < |x - p|) :
        ∃ Q : Finset ℝ, Q.card = 2 ∧ (∀ q ∈ Q, 0 ≤ q ∧ q ≤ 5) ∧
          won B {p} Q ≤ 2 * ({p} : Finset ℝ).card := by
      refine ⟨Q, hq, hqb, ?_⟩
      have hle : won B {p} Q ≤ (B.filter (fun x => x = p)).card := by
        apply Multiset.card_le_card
        apply Multiset.le_filter.mpr
        refine ⟨Multiset.filter_le _ _, ?_⟩
        intro x hx
        obtain ⟨hxB, hw⟩ := Multiset.mem_filter.mp hx
        have hxT : x ∈ T := by simpa [B, T] using hxB
        by_contra hxp
        obtain ⟨q, hq, hlt⟩ := hc x hxT hxp
        obtain ⟨z, hz, hdist⟩ := hw q hq
        have hz : z = p := Finset.mem_singleton.mp hz
        subst z
        exact (not_lt_of_ge hdist) hlt
      have hcount : (B.filter (fun x => x = p)).card ≤ 2 := by
        by_cases h0 : p = 0
        · subst p; norm_num [B, Multiset.filter_cons]
        by_cases h1 : p = 1
        · subst p; norm_num [B, Multiset.filter_cons]
        by_cases h2 : p = 2
        · subst p; norm_num [B, Multiset.filter_cons]
        by_cases h3 : p = 3
        · subst p; norm_num [B, Multiset.filter_cons]
        by_cases h4 : p = 4
        · subst p; norm_num [B, Multiset.filter_cons]
        by_cases h5 : p = 5
        · subst p; norm_num [B, Multiset.filter_cons]
        simp [B, eq_comm, h0, h1, h2, h3, h4, h5]
      simpa using hle.trans hcount
    have qp : ({0, 5} : Finset ℝ).card = 2 := by norm_num
    have qpb : ∀ q ∈ ({0, 5} : Finset ℝ), 0 ≤ q ∧ q ≤ 5 := by
      intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> norm_num
    by_cases hp0 : p < 0
    · apply single {0, 5} qp qpb
      intro x hx _
      obtain ⟨hx0, _⟩ := bounds x hx
      refine ⟨0, by simp, ?_⟩
      rw [sub_zero, abs_of_nonneg hx0, abs_of_pos (by linarith : 0 < x - p)]
      linarith
    by_cases hp5 : 5 < p
    · apply single {0, 5} qp qpb
      intro x hx _
      obtain ⟨_, hx5⟩ := bounds x hx
      refine ⟨5, by simp, ?_⟩
      rw [abs_of_nonpos (by linarith : x - 5 ≤ 0),
        abs_of_neg (by linarith : x - p < 0)]
      linarith
    have hp0' : 0 ≤ p := le_of_not_gt hp0
    have hp5' : p ≤ 5 := le_of_not_gt hp5
    have epsilon : ∀ S : Finset ℝ, ∃ e : ℝ, 0 < e ∧
        ∀ x ∈ S, x ≠ p → e < |x - p| := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact ⟨1, by norm_num, by simp⟩
      | @insert x S hx ih =>
        obtain ⟨e, he, hdist⟩ := ih
        by_cases hxp : x = p
        · refine ⟨e, he, ?_⟩
          intro y hy hyp
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (hyp hxp).elim
          · exact hdist y hy hyp
        · have hpos : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr hxp)
          refine ⟨min e (|x - p| / 2), lt_min he (by positivity), ?_⟩
          intro y hy hyp
          rcases Finset.mem_insert.mp hy with hy | hy
          · subst y
            exact (min_le_right _ _).trans_lt (by linarith)
          · exact (min_le_left _ _).trans_lt (hdist y hy hyp)
    obtain ⟨e, he, heT⟩ := epsilon T
    let u := max 0 (p - e)
    let v := min 5 (p + e)
    have huv : u < v := by
      dsimp [u, v]
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      constructor <;> constructor <;> linarith
    apply single {u, v}
    · simp [ne_of_lt huv]
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · dsimp [u]; constructor
        · exact le_max_left _ _
        · exact max_le (by norm_num) (by linarith)
      · have hq : q = v := Finset.mem_singleton.mp hq
        subst q; dsimp [v]; constructor
        · exact le_min (by norm_num) (by linarith)
        · exact min_le_left _ _
    · intro x hx hxp
      obtain ⟨hx0, hx5⟩ := bounds x hx
      have hdist := heT x hx hxp
      rcases lt_or_gt_of_ne hxp with hlt | hgt
      · rw [abs_of_neg (by linarith : x - p < 0)] at hdist
        have hpu : 0 ≤ p - e := by linarith
        refine ⟨u, by simp, ?_⟩
        dsimp [u]
        rw [max_eq_right hpu, abs_of_neg (by linarith : x - (p - e) < 0),
          abs_of_neg (by linarith : x - p < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < x - p)] at hdist
        have hpv : p + e ≤ 5 := by linarith
        refine ⟨v, by simp, ?_⟩
        dsimp [v]
        rw [min_eq_right hpv, abs_of_pos (by linarith : 0 < x - (p + e)),
          abs_of_pos (by linarith : 0 < x - p)]
        linarith
  by_cases ha2 : A.card = 2
  · simpa [B, ha2] using FacilityAdvantageTwo.two_response A ha2
  by_cases ha3 : A.card = 3
  · by_cases hHA : H ⊆ A
    · have hA : A = H := (Finset.eq_of_subset_of_card_le hHA (by simp [H, ha3])).symm
      refine ⟨{3 / 2, 4}, by norm_num, ?_, ?_⟩
      · intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num
      · rw [ha3, hA]
        change won (0 ::ₘ 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 3 ::ₘ 4 ::ₘ 5 ::ₘ 5 ::ₘ 0)
          {0, 3, 5} {3 / 2, 4} ≤ 6
        norm_num [won, Multiset.filter_cons]
    · obtain ⟨h, hhH, hhA⟩ := Finset.not_subset.mp hHA
      have hT : h ∈ T := by
        simp only [H, Finset.mem_insert, Finset.mem_singleton] at hhH
        rcases hhH with rfl | rfl | rfl <;> simp [T]
      have hc : A.card < (T.erase h).card := by
        rw [Finset.card_erase_of_mem hT]
        norm_num [T, ha3]
      obtain ⟨s, hsT, hsA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
      obtain ⟨hsh, hsT'⟩ := Finset.mem_erase.mp hsT
      refine ⟨{h, s}, by simp [ne_comm.mp hsh], ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with hq | hq
        · subst q; exact bounds h hT
        · rw [Finset.mem_singleton] at hq; subst q; exact bounds s hsT'
      · apply le_trans (Multiset.card_le_card (Multiset.monotone_filter_right B
          (fun x hw => show x ≠ h ∧ x ≠ s from ⟨fun heq => by
            subst x; exact capture {h, s} h hhA (by simp) hw,
            fun heq => by subst x; exact capture {h, s} s hsA (by simp) hw⟩)))
        rw [ha3]
        simp only [H, Finset.mem_insert, Finset.mem_singleton] at hhH
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hsT'
        rcases hhH with rfl | rfl | rfl <;>
          rcases hsT' with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact (hsh rfl).elim | norm_num [B, Multiset.filter_cons]
  by_cases ha4 : A.card = 4
  · have hc : A.card < T.card := by norm_num [T, ha4]
    obtain ⟨s, hsT, hsA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    let t : ℝ := if s = 0 then 5 else 0
    have hst : s ≠ t := by dsimp [t]; split_ifs <;> simp_all
    have htT : t ∈ T := by dsimp [t]; split_ifs <;> simp [T]
    refine ⟨{s, t}, by simp [hst], ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q; exact bounds s hsT
      · rw [Finset.mem_singleton] at hq; subst q; exact bounds t htT
    · apply le_trans (Multiset.card_le_card (Multiset.monotone_filter_right B
        (fun x hw => show x ≠ s from fun heq => by
          subst x; exact capture {s, t} s hsA (by simp) hw)))
      rw [ha4]
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hsT
      rcases hsT with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [B, Multiset.filter_cons]
  refine ⟨{0, 5}, by norm_num, ?_, ?_⟩
  · intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num
  · have hcard : B.card = 9 := by norm_num [B, Multiset.filter_cons]
    have hle : won B A {0, 5} ≤ B.card := Multiset.card_le_card (Multiset.filter_le _ _)
    rw [hcard] at hle
    omega

end D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageLocal
