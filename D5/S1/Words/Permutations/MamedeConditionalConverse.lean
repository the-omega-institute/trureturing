/- GID: D5/S1/Words/Permutations/MamedeConditionalConverse
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeConditionalConverse
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One source singleton of first-branch shape enables reduced insertion of every target singleton. -/

import D5.S1.Words.Permutations.MamedeSourceAction

namespace D5.S1.Words.Permutations.MamedeConditionalConverse

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeSourceAction

theorem source_deletion_surjective (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (a₀ p₀ q₀ : List Nat)
    (hs : exactSourceHypotheses n m M i j σ)
    (hshape : sourceShape m M i j a₀ p₀ q₀)
    (ha₀ : singletonWord n σ a₀) :
    ∀ b, singletonWord n
        (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b →
      ∃ a p q, singletonWord n σ a ∧
        sourceShape m M i j a p q ∧
        imageWord i j p q = b ∧ b.length < a.length := by
  let adjacentLetters (a b : Nat) : Prop := a + 1 = b ∨ b + 1 = a

  have insertion_reduced_from_shape (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1))) (a₀ p₀ q₀ p q : List Nat)
      (hs : exactSourceHypotheses n m M i j σ)
      (hshape : sourceShape m M i j a₀ p₀ q₀)
      (ha₀ : singletonWord n σ a₀)
      (hp : ∀ k ∈ p, m < k ∧ k < j)
      (hq : ∀ k ∈ q, i < k ∧ k < M)
      (hb : reducedWord n (imageWord i j p q))
      (hπ : wordProduct n (imageWord i j p q) =
        σ * (wordProduct n (deletedExcursion m M i))⁻¹) :
      reducedWord n (p ++ fullExcursion m M i j ++ q) := by
    have insertion_length (m M i j : Nat) (p q : List Nat)
        (hmi : m < i) (hij : i ≤ j) :
        (p ++ fullExcursion m M i j ++ q).length =
          (imageWord i j p q).length + (deletedExcursion m M i).length := by
      simp only [fullExcursion, deletedExcursion, imageWord, descending, ascending,
        List.length_append, List.length_map, List.length_range]
      omega
    have descending_valid (n lo hi : Nat)
        (hlo : 1 ≤ lo) (hhi : lo ≤ hi ∧ hi ≤ n) :
        validWord n (descending hi lo) := by
      intro k hk
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      have hrange := List.mem_range.mp hr
      constructor <;> omega

    have ascending_valid (n lo hi : Nat)
        (hlo : 1 ≤ lo) (hhi : lo ≤ hi ∧ hi ≤ n) :
        validWord n (ascending lo hi) := by
      intro k hk
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      have hrange := List.mem_range.mp hr
      constructor <;> omega

    have fullExcursion_valid (n m M i j : Nat)
        (hm : 1 ≤ m) (hmi : m < i) (hij : i ≤ j) (hjM : j < M) (hMn : M ≤ n) :
        validWord n (fullExcursion m M i j) := by
      intro k hk
      simp only [fullExcursion, List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · exact descending_valid n m j hm ⟨by omega, by omega⟩ k hk
      · exact ascending_valid n (m + 1) M (by omega) ⟨by omega, hMn⟩ k hk
      · exact descending_valid n i (M - 1) (by omega) ⟨by omega, by omega⟩ k hk
    have source_deleted_length (m M i j : Nat) (a p q : List Nat)
        (hmi : m < i) (hij : i ≤ j)
        (hshape : sourceShape m M i j a p q) :
        a.length = (imageWord i j p q).length + (deletedExcursion m M i).length := by
      rw [hshape.1]
      simp only [fullExcursion, deletedExcursion, imageWord, descending, ascending,
        List.length_append, List.length_map, List.length_range]
      omega
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    have hs : exactSourceHypotheses n m M i j σ :=
      ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    let b₀ := imageWord i j p₀ q₀
    have hbase := source_full_product n m M i j p₀ q₀
      hm hmi hij hjM hMn hshape.2.2
    rw [← hshape.1, ha₀.2.2] at hbase
    have hb₀prod : wordProduct n b₀ =
        σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by
      calc
        wordProduct n b₀ =
            (wordProduct n b₀ * wordProduct n (deletedExcursion m M i)) *
              (wordProduct n (deletedExcursion m M i))⁻¹ := by group
        _ = σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by
          rw [hbase]
    have hb₀valid : validWord n b₀ := by
      intro k hk
      simp only [b₀, imageWord, List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · have h := hshape.2.1 k hk
        omega
      · exact descending_valid n i j (by omega) ⟨hij, by omega⟩ k hk
      · have h := hshape.2.2 k hk
        omega
    have hfullvalid := fullExcursion_valid n m M i j hm hmi hij hjM hMn
    have hcandvalid : validWord n (p ++ fullExcursion m M i j ++ q) := by
      intro k hk
      simp only [List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · have h := hp k hk
        omega
      · exact hfullvalid k hk
      · have h := hq k hk
        omega
    have hcandprod : wordProduct n (p ++ fullExcursion m M i j ++ q) = σ := by
      rw [source_full_product n m M i j p q hm hmi hij hjM hMn hq, hπ]
      group
    have hle₁ : (imageWord i j p q).length ≤ b₀.length :=
      hb.2 b₀ hb₀valid (hb₀prod.trans hπ.symm)
    have hle₂ : a₀.length ≤ (p ++ fullExcursion m M i j ++ q).length :=
      ha₀.1.2 _ hcandvalid (hcandprod.trans ha₀.2.2.symm)
    have hsource_len := source_deleted_length m M i j a₀ p₀ q₀ hmi hij hshape
    change a₀.length = b₀.length + (deletedExcursion m M i).length at hsource_len
    have hcand_len := insertion_length m M i j p q hmi hij
    have heq : (p ++ fullExcursion m M i j ++ q).length = a₀.length := by
      omega
    refine ⟨hcandvalid, ?_⟩
    intro v hv hprod
    rw [heq]
    exact ha₀.1.2 v hv (hprod.trans (hcandprod.trans ha₀.2.2.symm))

  have descending_head (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).head? = some hi := by
    simp [descending, List.head?_range]

  have descending_last (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).getLast? = some lo := by
    simp [descending, List.getLast?_range]
    omega

  have ascending_head (lo hi : Nat) (h : lo ≤ hi) :
      (ascending lo hi).head? = some lo := by
    simp [ascending, List.head?_range]

  have ascending_last (lo hi : Nat) (h : lo ≤ hi) :
      (ascending lo hi).getLast? = some hi := by
    simp [ascending, List.getLast?_range]
    omega

  have descending_chain (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).IsChain adjacentLetters := by
    rw [descending, List.isChain_map, List.isChain_range]
    intro r hr
    right
    dsimp [adjacentLetters]
    omega

  have ascending_chain (lo hi : Nat) (_h : lo ≤ hi) :
      (ascending lo hi).IsChain adjacentLetters := by
    rw [ascending, List.isChain_map, List.isChain_range]
    intro r hr
    left
    dsimp [adjacentLetters]
    omega

  have fullExcursion_chain (m M i j : Nat)
      (hmi : m < i) (hij : i ≤ j) (hjM : j < M) :
      (fullExcursion m M i j).IsChain adjacentLetters := by
    simp only [fullExcursion, List.isChain_append]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨descending_chain m j (by omega),
        ascending_chain (m + 1) M (by omega), ?_⟩
      rw [descending_last m j (by omega), ascending_head (m + 1) M (by omega)]
      simp [adjacentLetters]
    · exact descending_chain i (M - 1) (by omega)
    · rw [List.getLast?_append_of_ne_nil]
      · rw [ascending_last (m + 1) M (by omega),
          descending_head i (M - 1) (by omega)]
        simp [adjacentLetters, show M - 1 + 1 = M by omega]
      · intro he
        have hh := ascending_head (m + 1) M (by omega)
        rw [he] at hh
        simp at hh

  have insertion_consecutive (m M i j : Nat) (p q : List Nat)
      (hmi : m < i) (hij : i ≤ j) (hjM : j < M)
      (hc : consecutive (imageWord i j p q)) :
      consecutive (p ++ fullExcursion m M i j ++ q) := by
    have consecutive_iff_chain (w : List Nat) :
        consecutive w ↔ w.IsChain adjacentLetters := by
      induction w using List.twoStepInduction with
      | nil => simp [consecutive]
      | singleton a => simp [consecutive]
      | cons_cons a b rest _ ih =>
        simpa [consecutive, adjacentLetters, List.isChain_cons_cons] using
          and_congr Iff.rfl (ih b)
    rw [consecutive_iff_chain] at hc ⊢
    simp only [imageWord] at hc
    have hhead : (fullExcursion m M i j).head? = (descending j i).head? := by
      have hn : descending j m ≠ [] := by
        intro he
        have hh := descending_head m j (by omega)
        rw [he] at hh
        simp at hh
      rw [fullExcursion, List.append_assoc,
        List.head?_append_of_ne_nil _ hn]
      rw [descending_head m j (by omega), descending_head i j hij]
    have hlast : (fullExcursion m M i j).getLast? = (descending j i).getLast? := by
      have hn : descending (M - 1) i ≠ [] := by
        intro he
        have hh := descending_head i (M - 1) (by omega)
        rw [he] at hh
        simp at hh
      simp [fullExcursion, List.getLast?_append_of_ne_nil _ hn,
        descending_last i (M - 1) (by omega), descending_last i j hij]
    have hDne : descending j i ≠ [] := by
      intro he
      have hh := descending_head i j hij
      rw [he] at hh
      simp at hh
    have hFne : fullExcursion m M i j ≠ [] := by
      intro he
      rw [he, descending_head i j hij] at hhead
      simp at hhead
    have hlast_outer : (p ++ fullExcursion m M i j).getLast? =
        (p ++ descending j i).getLast? := by
      rw [List.getLast?_append_of_ne_nil p hFne,
        List.getLast?_append_of_ne_nil p hDne]
      exact hlast
    -- The two outer adjacency checks use only the endpoints of the replaced block.
    simp only [List.isChain_append] at hc ⊢
    rcases hc with ⟨⟨hp, hD, hleft⟩, hq, hright⟩
    refine ⟨⟨hp, fullExcursion_chain m M i j hmi hij hjM, ?_⟩, hq, ?_⟩
    · simpa only [hhead] using hleft
    · simpa only [hlast_outer] using hright

  have source_insertionReduced (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1))) (a₀ p₀ q₀ : List Nat)
      (hs : exactSourceHypotheses n m M i j σ)
      (hshape : sourceShape m M i j a₀ p₀ q₀)
      (ha₀ : singletonWord n σ a₀) :
      ∀ p q, (∀ k ∈ p, m < k ∧ k < j) →
        (∀ k ∈ q, i < k ∧ k < M) →
        singletonWord n (σ * (wordProduct n (deletedExcursion m M i))⁻¹)
          (imageWord i j p q) →
        singletonWord n σ (p ++ fullExcursion m M i j ++ q) := by
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    have hs : exactSourceHypotheses n m M i j σ :=
      ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    intro p q hp hq hb
    have hprod : wordProduct n (p ++ fullExcursion m M i j ++ q) = σ := by
      rw [source_full_product n m M i j p q hm hmi hij hjM hMn hq, hb.2.2]
      group
    refine ⟨insertion_reduced_from_shape n m M i j σ a₀ p₀ q₀ p q
        hs hshape ha₀ hp hq hb.1 hb.2.2, ?_, hprod⟩
    exact insertion_consecutive m M i j p q hmi hij hjM hb.2.1

  have hf := source_target_factorization n m M i j σ a₀ p₀ q₀ hs hshape ha₀
  have hi := source_insertionReduced n m M i j σ a₀ p₀ q₀ hs hshape ha₀
  intro b hb
  obtain ⟨p, q, rfl, hp, hq⟩ := hf b hb
  have hmi : m < i := hs.2.1
  have hij : i ≤ j := hs.2.2.1
  have hlen :
      (p ++ fullExcursion m M i j ++ q).length =
        (imageWord i j p q).length + (deletedExcursion m M i).length := by
    simp only [fullExcursion, deletedExcursion, imageWord, descending, ascending,
      List.length_append, List.length_map, List.length_range]
    omega
  have hpos : 0 < (deletedExcursion m M i).length := by
    simp only [deletedExcursion, List.length_append]
    have h : 0 < (ascending (m + 1) M).length := by simp [ascending]
    omega
  exact ⟨p ++ fullExcursion m M i j ++ q, p, q,
    hi p q hp hq hb, ⟨rfl, hp, hq⟩, rfl, by omega⟩

end D5.S1.Words.Permutations.MamedeConditionalConverse
