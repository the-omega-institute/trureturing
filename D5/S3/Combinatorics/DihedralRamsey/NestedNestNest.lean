/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedNestNest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedNestNest
   mirror-E: none(waiver:cyclic-nested-matching-ramsey)
   anchors: []
   utility: none
   digest: Full-matching balance settles the cyclic nested matching Ramsey conjecture. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedBalanceUpper
import D5.S3.Combinatorics.DihedralRamsey.NestedMetricExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedNestNest

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs Finset
open scoped BigOperators

set_option maxHeartbeats 800000 in
theorem result : claimNestNest := by
  classical
  intro a b ha hb hda hdb
  let k := a / 2
  let l := b / 2
  have hak : a = 2 * k := by
    obtain ⟨d, hd⟩ := hda
    dsimp [k]
    omega
  have hbl : b = 2 * l := by
    obtain ⟨d, hd⟩ := hdb
    dsimp [l]
    omega
  have hk : 2 ≤ k := by omega
  have hl : 2 ≤ l := by omega
  have hke : k % 2 = 0 := by
    obtain ⟨d, hd⟩ := hda
    omega
  have hle : l % 2 = 0 := by
    obtain ⟨d, hd⟩ := hdb
    omega
  let N := 2 * (k + l - 2) + 1
  have hN : 0 < N := by dsimp [N]; omega
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (nestMatching a) G ∨ CyclicEmbeddable (nestMatching b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    have h : CyclicEmbeddable (nestMatching (2 * k)) G ∨
        CyclicEmbeddable (nestMatching (2 * l)) Gᶜ := by
        by_contra h
        push_neg at h
        obtain ⟨hred, hblue⟩ := h
        let m := k + l - 2
        have hm : 0 < m := by dsimp [m]; omega
        have hme : m % 2 = 0 := by dsimp [m]; omega
        let C : ℕ → ℕ → ℕ := fun x y =>
          if hx : x < 2 * m + 1 then
            if hy : y < 2 * m + 1 then if G.Adj ⟨x, hx⟩ ⟨y, hy⟩ then 1 else 0 else 0 else 0
        have hs : ∀ x y, C x y = C y x := by
          intro x y
          dsimp [C]
          by_cases hx : x < 2 * m + 1 <;> by_cases hy : y < 2 * m + 1 <;>
            simp only [hx, hy, dif_pos, dif_neg, SimpleGraph.adj_comm]
        have hd : ∀ x, C x x = 0 := by
          intro x
          dsimp [C]
          split_ifs <;> simp_all
        have hb : ∀ (h : Fin (2 * m + 1)) (c : Fin (2 * m)), c.val % 2 = 1 →
            (∑ i : Fin (2 * m), C (h.succAbove i).val (h.succAbove (c - i)).val) =
              2 * (k - 1) := by
          intro h c hc
          simpa only [C, dif_pos (h.succAbove _).isLt] using
            NestedBalanceUpper.full_matching_balance hk hl G hred hblue h c hc
        obtain ⟨hfour, hconstant⟩ := NestedBalanceDegree.full_balance_degree hm hme C hs hd hb
        let D := ∑ d ∈ Finset.range (2 * m), C 0 (d + 1)
        have deg : ∀ v : Fin (2 * m + 1), G.degree v = D := by
          intro v
          rw [← G.card_neighborFinset_eq_degree]
          have hh := hconstant v.val v.isLt
          rw [Finset.sum_range] at hh
          change (∑ u : Fin (2 * m + 1), C v.val u.val) = D at hh
          have hrow : ∀ u : Fin (2 * m + 1), C v.val u.val =
              if G.Adj v u then 1 else 0 := by
            intro u
            simp only [C, dif_pos v.isLt, dif_pos u.isLt, Fin.eta]
          simp_rw [hrow] at hh
          rw [sum_boole] at hh
          rw [SimpleGraph.neighborFinset_eq_filter]
          convert hh using 1
          congr 1
        have bound : ∀ {t : ℕ} (ht : 0 < t) (H : SimpleGraph (Fin (2 * m + 1))),
            ¬CyclicEmbeddable (nestMatching (2 * t)) H → ∃ v, H.degree v ≤ 2 * (t - 1) := by
          intro t ht H havoid
          apply (NestedCounting.endpoint_degree_bound (by omega) H ?_).1
          intro c
          by_contra hc
          exact havoid (NestedSelection.sum_class_copy (by omega) ht H c (by omega))
        obtain ⟨v, hv⟩ := bound (by omega) G hred
        obtain ⟨w, hw⟩ := bound (by omega) Gᶜ hblue
        have hw' : Gᶜ.degree w ≤ 2 * (l - 1) := by
          convert hw using 1
          unfold SimpleGraph.degree
          congr 1
          ext x
          simp
        have hcomp := G.degree_compl w
        simp only [Fintype.card_fin] at hcomp
        rw [deg v] at hv
        rw [deg w] at hcomp
        have hlt := G.degree_lt_card_verts w
        simp only [Fintype.card_fin, deg w] at hlt
        have hmn : m = k + l - 2 := rfl
        change Gᶜ.degree w = 2 * m + 1 - 1 - D at hcomp
        change D < 2 * m + 1 at hlt
        have hsumarith : Gᶜ.degree w + D = 2 * m := by omega
        have hsplit : 2 * m = 2 * (k - 1) + 2 * (l - 1) := by dsimp [m]; omega
        have arithmetic : ∀ A B X Y : ℕ,
            A + B = X + Y → A ≤ X → B ≤ Y → A = X := by
          intro A B X Y hsum hA hB
          omega
        have hD : D = 2 * (k - 1) := arithmetic D (Gᶜ.degree w)
          (2 * (k - 1)) (2 * (l - 1))
          (by simpa only [Nat.add_comm] using hsumarith.trans hsplit) hv hw'
        change 4 ∣ D at hfour
        rw [hD] at hfour
        obtain ⟨q, hq⟩ := hfour
        omega
    rcases h with hr | hb
    · left
      exact (congrArg (fun x => CyclicEmbeddable (nestMatching x) G) hak).mpr hr
    · right
      exact (congrArg (fun x => CyclicEmbeddable (nestMatching x) Gᶜ) hbl).mpr hb
  have predecessor : ∃ G : SimpleGraph (Fin (N - 1)),
      ¬CyclicEmbeddable (nestMatching a) G ∧ ¬CyclicEmbeddable (nestMatching b) Gᶜ := by
    have hn : 2 * k + 2 * l - 4 = N - 1 := by dsimp [N]; omega
    rw [← hn]
    obtain ⟨G, hred, hblue⟩ := NestedMetricExtension.matching_predecessor hk hl hke
    refine ⟨G, ?_, ?_⟩
    · intro h
      apply hred
      exact (congrArg (fun x => CyclicEmbeddable (nestMatching x) G) hak).mp h
    · intro h
      apply hblue
      exact (congrArg (fun x => CyclicEmbeddable (nestMatching x) Gᶜ) hbl).mp h
  have lower : ∀ n ∈ S, N ≤ n := by
    intro n hn
    by_contra hlt
    have hle : n ≤ N - 1 := by omega
    obtain ⟨G, hred, hblue⟩ := predecessor
    let ι := Fin.castLE hle
    have hm : StrictMono ι := fun _ _ h => h
    obtain h | h := hn (G.comap ι)
    · obtain ⟨s, ψ, hψ, hcopy⟩ := h
      exact hred ⟨s, ι ∘ ψ, hm.comp hψ, hcopy⟩
    · obtain ⟨s, ψ, hψ, hcopy⟩ := h
      apply hblue
      refine ⟨s, ι ∘ ψ, hm.comp hψ, ?_⟩
      intro i j hij
      have hh := hcopy i j hij
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at hh ⊢
      exact ⟨fun heq => hh.1 (hm.injective heq), hh.2⟩
  have heq : sInf S = N :=
    le_antisymm (csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ upper)
      (le_csInf ⟨N, upper⟩ lower)
  change sInf S = a + b - 3
  rw [heq]
  dsimp [N]
  omega

#print axioms result

end D5.S3.Combinatorics.DihedralRamsey.NestedNestNest
