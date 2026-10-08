/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedBalanceUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedBalanceUpper
   mirror-E: none(waiver:cyclic-nested-matching-balance)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Constant full-matching balance rules out avoidance at the nested Ramsey threshold. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedBalanceCount
import D5.S3.Combinatorics.DihedralRamsey.NestedSelection
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedBalanceUpper

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs Finset
open scoped BigOperators

/-- Avoidance forces every full reflection to have the same prescribed colour count. -/
theorem full_matching_balance {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l)
    (G : SimpleGraph (Fin (2 * (k + l - 2) + 1))) [DecidableRel G.Adj]
    (hred : ¬CyclicEmbeddable (nestMatching (2 * k)) G)
    (hblue : ¬CyclicEmbeddable (nestMatching (2 * l)) Gᶜ)
    (h : Fin (2 * (k + l - 2) + 1)) (c : Fin (2 * (k + l - 2)))
    (hc : c.val % 2 = 1) :
    (∑ i : Fin (2 * (k + l - 2)),
      if G.Adj (h.succAbove i) (h.succAbove (c - i)) then 1 else 0) = 2 * (k - 1) := by
  classical
  let a := 2 * (k + l - 2)
  have ha : 0 < a := by dsimp [a]; omega
  have hae : a % 2 = 0 := by dsimp [a]; omega
  let H := G.comap h.succAbove
  have mono : StrictMono h.succAbove := Fin.strictMono_succAbove h
  have redbound : (univ.filter fun e : Fin a × Fin a =>
      e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card ≤ k - 1 := by
    by_contra hh
    have hge : k ≤ (univ.filter fun e : Fin a × Fin a =>
        e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card := by omega
    have hcopy := NestedSelection.sum_class_copy ha (by omega : 0 < k) H c
      (by convert hge using 1; congr 1; ext e; simp only [mem_filter, mem_univ])
    obtain ⟨s, ψ, hψ, he⟩ := hcopy
    exact hred ⟨s, h.succAbove ∘ ψ, mono.comp hψ, he⟩
  have bluebound : (univ.filter fun e : Fin a × Fin a =>
      e.1 < e.2 ∧ Hᶜ.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card ≤ l - 1 := by
    by_contra hh
    have hge : l ≤ (univ.filter fun e : Fin a × Fin a =>
        e.1 < e.2 ∧ Hᶜ.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card := by omega
    have hcopy := NestedSelection.sum_class_copy ha (by omega : 0 < l) Hᶜ c
      (by convert hge using 1; congr 1; ext e; simp only [mem_filter, mem_univ])
    obtain ⟨s, ψ, hψ, he⟩ := hcopy
    apply hblue
    refine ⟨s, h.succAbove ∘ ψ, mono.comp hψ, ?_⟩
    intro i j hij
    have hh := he i j hij
    simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, H] at hh ⊢
    exact ⟨fun hij => hh.1 (mono.injective hij), hh.2⟩
  have redsum := NestedBalanceCount.reflection_class_indicator_sum ha hae H c hc
  let P := univ.filter fun e : Fin a × Fin a =>
    e.1 < e.2 ∧ (e.1.val + e.2.val) % a = c.val
  have total : (univ.filter fun e : Fin a × Fin a =>
      e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card +
      (univ.filter fun e : Fin a × Fin a =>
      e.1 < e.2 ∧ Hᶜ.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val).card =
        k + l - 2 := by
    have hcP : P.card = k + l - 2 :=
      NestedBalanceCount.full_reflection_class_card (by omega) c hc
    have hfilter : (P.filter fun e => H.Adj e.1 e.2) =
        univ.filter fun e : Fin a × Fin a =>
          e.1 < e.2 ∧ H.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val := by
      ext e
      simp only [P, mem_filter, mem_univ, true_and]
      tauto
    have hfilter' : (P.filter fun e => ¬H.Adj e.1 e.2) =
        univ.filter fun e : Fin a × Fin a =>
          e.1 < e.2 ∧ Hᶜ.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % a = c.val := by
      ext e
      simp only [P, mem_filter, mem_univ, true_and, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨⟨hij, hsum⟩, hnot⟩
        exact ⟨hij, ⟨ne_of_lt hij, hnot⟩, hsum⟩
      · rintro ⟨hij, ⟨_, hnot⟩, hsum⟩
        exact ⟨⟨hij, hsum⟩, hnot⟩
    rw [← hfilter, ← hfilter', card_filter_add_card_filter_not, hcP]
  change (∑ i : Fin a, if H.Adj i (c - i) then 1 else 0) = _
  omega


end D5.S3.Combinatorics.DihedralRamsey.NestedBalanceUpper
