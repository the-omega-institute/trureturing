/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedCycNestStar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedCycNestStar
   mirror-E: none(waiver:cyclic-nested-matching-star)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: The cyclic Ramsey number of a nested matching against a star. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedCounting
import D5.S3.Combinatorics.DihedralRamsey.NestedMetricColouring
import D5.S3.Combinatorics.DihedralRamsey.NestedSelection
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyStar
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedCycNestStar

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs Finset

theorem result : claimCycNestStar := by
  classical
  intro a b ha hae hb
  let k := a / 2
  have hk : 0 < k := by dsimp [k]; omega
  have hak : a = 2 * k := by dsimp [k]; omega
  let N := if 4 ∣ a ∧ b % 2 = 1 then a + b - 3 else a + b - 2
  have hN : 0 < N := by
    dsimp [N]
    split_ifs with h
    · obtain ⟨d, hd⟩ := h.1
      omega
    · omega
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (nestMatching a) G ∨ CyclicEmbeddable (startStar b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_contra h
    obtain ⟨hred, hblue⟩ := not_or.mp h
    have hclass : ∀ c : Fin N,
        (univ.filter fun e : Fin N × Fin N =>
          e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % N = c.val).card ≤ k - 1 := by
      intro c
      by_contra hgt
      apply hred
      rw [hak]
      exact NestedSelection.sum_class_copy hN hk G c (by omega)
    have hbdeg : ∀ v, Gᶜ.degree v ≤ b - 2 := by
      intro v
      by_contra hh
      have hx : b - 1 ≤ Gᶜ.degree v := by omega
      have hcopy := (star_iff_degree hb false Gᶜ).mpr ⟨v, by convert hx⟩
      exact hblue hcopy
    have hdegrees : ∀ v, G.degree v + Gᶜ.degree v = N - 1 := by
      intro v
      have hl := G.degree_lt_card_verts v
      rw [G.degree_compl, Fintype.card_fin]
      simp only [Fintype.card_fin] at hl
      omega
    obtain ⟨hgeneral, hstrong⟩ := NestedCounting.endpoint_degree_bound hN G hclass
    by_cases hp : 4 ∣ a ∧ b % 2 = 1
    · have hne : N % 2 = 0 := by
        obtain ⟨d, hd⟩ := hp.1
        dsimp [N]
        rw [if_pos hp]
        omega
      have hke : (k - 1) % 2 = 1 := by
        obtain ⟨d, hd⟩ := hp.1
        omega
      obtain ⟨v, hv⟩ := hstrong hne hke
      have hd := hdegrees v
      have hbv := hbdeg v
      have hnval : N = a + b - 3 := if_pos hp
      have hd' : G.degree v + Gᶜ.degree v = a + b - 4 := by
        omega
      omega
    · obtain ⟨v, hv⟩ := hgeneral
      have hd := hdegrees v
      have hbv := hbdeg v
      have hnval : N = a + b - 2 := if_neg hp
      have hd' : G.degree v + Gᶜ.degree v = a + b - 3 := by
        omega
      omega
  have predecessor : ∃ G : SimpleGraph (Fin (N - 1)),
      ¬CyclicEmbeddable (nestMatching a) G ∧ ¬CyclicEmbeddable (startStar b) Gᶜ := by
    obtain ⟨G, hred, hdeg⟩ := NestedMetricColouring.star_predecessor hk hb
    have hn : (if k % 2 = 0 ∧ b % 2 = 1 then 2 * k + b - 4
        else 2 * k + b - 3) = N - 1 := by
      have hdvd : 4 ∣ a ↔ k % 2 = 0 := by
        constructor
        · rintro ⟨d, hd⟩
          omega
        · intro hke
          exact ⟨k / 2, by omega⟩
      dsimp [N]
      by_cases hp : 4 ∣ a ∧ b % 2 = 1
      · have hp' : k % 2 = 0 ∧ b % 2 = 1 := ⟨hdvd.mp hp.1, hp.2⟩
        simp only [if_pos hp, if_pos hp']
        omega
      · have hp' : ¬(k % 2 = 0 ∧ b % 2 = 1) := by
          exact fun h => hp ⟨hdvd.mpr h.1, h.2⟩
        simp only [if_neg hp, if_neg hp']
        omega
    rw [← hn]
    refine ⟨G, ?_, ?_⟩
    · intro hcopy
      have hc : CyclicEmbeddable (nestMatching (2 * k)) G := by
        exact (congrArg (fun x => CyclicEmbeddable (nestMatching x) G) hak).mp hcopy
      exact hred hc
    · intro hcopy
      obtain ⟨v, hv⟩ := (star_iff_degree hb false Gᶜ).mp hcopy
      have hd := hdeg v
      have hd' : Gᶜ.degree v ≤ b - 2 := by convert hd
      exact (Nat.not_le_of_gt (by omega : b - 2 < b - 1)) (hv.trans hd')
  have lower : ∀ n ∈ S, N ≤ n := by
    intro n hn
    by_contra hlt
    have hle : n ≤ N - 1 := by omega
    obtain ⟨G, hred, hblue⟩ := predecessor
    let ι := Fin.castLE hle
    have hm : StrictMono ι := fun _ _ h => h
    obtain h | h := hn (G.comap ι)
    · obtain ⟨s, ψ, hψ, hcopy⟩ := h
      apply hred
      exact ⟨s, ι ∘ ψ, hm.comp hψ, hcopy⟩
    · obtain ⟨s, ψ, hψ, hcopy⟩ := h
      apply hblue
      refine ⟨s, ι ∘ ψ, hm.comp hψ, ?_⟩
      intro i j hij
      have hh := hcopy i j hij
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at hh ⊢
      exact ⟨fun heq => hh.1 (hm.injective heq), hh.2⟩
  change sInf S = N
  exact le_antisymm (csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ upper)
    (le_csInf ⟨N, upper⟩ lower)

#print axioms result

end D5.S3.Combinatorics.DihedralRamsey.NestedCycNestStar
