/- GID: D5/S3/Combinatorics/VoronoiGames/FacilityAdvantageAmplification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VoronoiGames/FacilityAdvantageAmplification
   mirror-E: none(waiver:separated-voter-family)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Nearest-anchor assignment amplifies the two-responder gadget to all positive sizes. -/

import D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageLocal
import Mathlib.Tactic

open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageAmplification

open FacilityAdvantageDefs FacilityAdvantageLocal

/-- The multiset union of the nine-voter gadget translated to anchors spaced by thirty. -/
noncomputable def voters (r : ℕ) : Multiset ℝ :=
  ∑ j : Fin r, B.map (fun v => 30 * (j.val : ℝ) + v)
set_option maxHeartbeats 800000 in
-- The geometric partition and multiset estimates are elaborated in one declaration.
/-- Every leader budget below one quarter of the population loses against two responders
per separated gadget. -/
theorem family_bound (r k : ℕ) (hr : 1 ≤ r) (hk : 4 * k < 9 * r) :
    2 * gameValue k (2 * r) (voters r) < (voters r).card := by
  classical
  have hB : B.card = 9 := by simp [B]
  have hmem : ∀ v ∈ B, 0 ≤ v ∧ v ≤ 5 := by
    intro v hv
    simp only [B, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h | h | h | h <;> subst v <;> norm_num
  have hcard : (voters r).card = 9 * r := by
    have hadd (s : Finset (Fin r)) :
        (∑ j ∈ s, B.map (fun v => 30 * (j.val : ℝ)+v)).card = s.card * 9 := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [Finset.sum_insert, ha, Multiset.card_add, ih, hB]; omega
    simpa [voters, Nat.mul_comm] using hadd Finset.univ
  have hresponse (P : Finset ℝ) : ∃ Q : Finset ℝ,
      Q.card = 2 * r ∧ won (voters r) P Q ≤ 2 * P.card := by
    have hn : (Finset.univ : Finset (Fin r)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hmin (p : ℝ) := Finset.exists_min_image Finset.univ
      (fun j : Fin r => |p-30 * (j.val : ℝ)|) hn
    choose assign hassign hnear using hmin
    let S (j : Fin r) := P.filter (fun p => assign p = j)
    let A (j : Fin r) := (S j).image (fun p => p-30 * (j.val : ℝ))
    have hAc (j : Fin r) : (A j).card = (S j).card := by
      apply Finset.card_image_of_injective
      intro p q hpq
      dsimp at hpq
      linarith
    choose R hRc hRb hRw using fun j : Fin r => local_response (A j)
    let T (j : Fin r) := (R j).image (fun q => 30 * (j.val : ℝ)+q)
    have hTc (j : Fin r) : (T j).card = 2 := by
      dsimp [T]
      rw [Finset.card_image_of_injective]
      · exact hRc j
      · intro p q hpq
        linarith
    have hTb (j : Fin r) (q : ℝ) (hq : q ∈ T j) :
        30 * (j.val : ℝ) ≤ q ∧ q ≤ 30 * (j.val : ℝ)+5 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hl, hu⟩ := hRb j x hx
      constructor <;> linarith
    have hdisj : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint T := by
      intro i hi j hj hij
      apply Finset.disjoint_left.mpr
      intro q hqi hqj
      obtain ⟨hil, hiu⟩ := hTb i q hqi
      obtain ⟨hjl, hju⟩ := hTb j q hqj
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hsep : (i.val : ℝ)+1 ≤ j.val ∨ (j.val : ℝ)+1 ≤ i.val := by
        rcases lt_or_gt_of_ne hne with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      rcases hsep with h | h <;> linarith
    let Q := Finset.univ.biUnion T
    have hQc : Q.card = 2 * r := by
      dsimp [Q]
      rw [Finset.card_biUnion hdisj]
      simp [hTc, Nat.mul_comm]
    have hfar (j : Fin r) (v : ℝ) (hv : v ∈ B) (p : ℝ)
        (hp : p ∈ P) (hps : p ∉ S j) : 10 ≤ |30 * (j.val : ℝ)+v-p| := by
      have hnj : assign p ≠ j := by
        intro h
        exact hps (Finset.mem_filter.mpr ⟨hp, h⟩)
      have hd : 30 ≤ |30 * ((assign p).val : ℝ)-30 * (j.val : ℝ)| := by
        have hnval : (assign p).val ≠ j.val := fun h => hnj (Fin.ext h)
        have hsep : ((assign p).val : ℝ)+1 ≤ j.val ∨
            (j.val : ℝ)+1 ≤ (assign p).val := by
          rcases lt_or_gt_of_ne hnval with h | h
          · left; exact_mod_cast h
          · right; exact_mod_cast h
        rcases hsep with h | h
        · rw [abs_of_nonpos] <;> linarith
        · rw [abs_of_nonneg] <;> linarith
      have ht := abs_sub_le (30 * ((assign p).val : ℝ)) p (30 * (j.val : ℝ))
      have hm := hnear p j (Finset.mem_univ j)
      rw [abs_sub_comm (30 * ((assign p).val : ℝ)) p] at ht
      have hdist : 15 ≤ |p-30 * (j.val : ℝ)| := by linarith
      obtain ⟨hvl, hvu⟩ := hmem v hv
      have htri := abs_sub_le p (30 * (j.val : ℝ)+v) (30 * (j.val : ℝ))
      have heq : |30 * (j.val : ℝ)+v-30 * (j.val : ℝ)| = v := by
        rw [show 30 * (j.val : ℝ)+v-30 * (j.val : ℝ)=v by ring, abs_of_nonneg hvl]
      rw [heq, abs_sub_comm p (30 * (j.val : ℝ)+v)] at htri
      linarith
    have hblock (j : Fin r) :
        won (B.map (fun v => 30 * (j.val : ℝ)+v)) P Q ≤ 2 * (S j).card := by
      have hle : won (B.map (fun v => 30 * (j.val : ℝ)+v)) P Q ≤ won B (A j) (R j) := by
        unfold won
        rw [Multiset.filter_map, Multiset.card_map]
        apply Multiset.card_le_card
        apply Multiset.le_filter.mpr
        constructor
        · exact Multiset.filter_le _ _
        · intro v hv
          obtain ⟨hvb, hvw⟩ := Multiset.mem_filter.mp hv
          intro q hq
          have htq : 30 * (j.val : ℝ)+q ∈ Q :=
            Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
              Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
          obtain ⟨p, hp, hdist⟩ := hvw _ htq
          have hps : p ∈ S j := by
            by_contra hnot
            have hf := hfar j v hvb p hp hnot
            have hqr : |v-q| ≤ 5 := by
              obtain ⟨hv0, hv5⟩ := hmem v hvb
              obtain ⟨hq0, hq5⟩ := hRb j q hq
              exact abs_le.mpr ⟨by linarith, by linarith⟩
            have heq : |30 * (j.val : ℝ)+v-(30 * (j.val : ℝ)+q)| = |v-q| := by
              congr 1; ring
            rw [heq] at hdist
            linarith
          refine ⟨p-30 * (j.val : ℝ), Finset.mem_image.mpr ⟨p, hps, rfl⟩, ?_⟩
          convert hdist using 1 <;> congr 1 <;> ring
      rw [← hAc j]
      exact hle.trans (hRw j)
    have hcount : won (voters r) P Q ≤ ∑ j : Fin r, 2 * (S j).card := by
      have hsum (s : Finset (Fin r)) :
          won (∑ j ∈ s, B.map (fun v => 30 * (j.val : ℝ)+v)) P Q =
          ∑ j ∈ s, won (B.map (fun v => 30 * (j.val : ℝ)+v)) P Q := by
        induction s using Finset.induction_on with
        | empty => simp [won]
        | @insert a s ha ih =>
          simp only [Finset.sum_insert ha, won, Multiset.filter_add, Multiset.card_add] at *
          rw [ih]
      rw [voters, hsum]
      exact Finset.sum_le_sum fun j hj => hblock j
    have hpartition : ∑ j : Fin r, (S j).card = P.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_univ (assign p))
    refine ⟨Q, hQc, ?_⟩
    simpa [← Finset.mul_sum, hpartition] using hcount
  have hgame : gameValue k (2 * r) (voters r) ≤ 2 * k := by
    unfold gameValue
    obtain ⟨P₀, hP₀⟩ := Finset.exists_card_eq (α := ℝ) k
    apply csSup_le
    · exact ⟨_, P₀, hP₀, rfl⟩
    rintro x ⟨P, hPk, rfl⟩
    obtain ⟨Q, hQc, hQw⟩ := hresponse P
    have hinf : sInf {y | ∃ Q : Finset ℝ, Q.card = 2 * r ∧
        y = won (voters r) P Q} ≤ won (voters r) P Q := Nat.sInf_le ⟨Q, hQc, rfl⟩
    exact hinf.trans (by simpa [hPk] using hQw)
  rw [hcard]
  omega
end D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageAmplification
