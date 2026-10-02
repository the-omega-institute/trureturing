/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBConstruction
   mirror-E: none(waiver:decomposable-parent-ranked-construction)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Internal first-component insertions retain local cuts and later boundaries only. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.GeomSum

open D5.S3.Combinatorics.Fishburn
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBReconstruction

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicParents
open FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns FishburnBasicComponents
open FishburnBasicSumInsertion NonnestingBasicSum

theorem indecomposable_construction (n : ℕ) :
    (Set.BijOn (fun entry : List ℕ × ℕ => entry.1.insertIdx entry.2 (n + 1))
      {entry | entry.1 ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
        (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
          (∀ block ∈ first :: rest, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
          entry.2 < first.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])}
      {p | p ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
        sumIndecomposable p} ∧
    (∀ parts : List (List ℕ),
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      assemble parts ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] → 0 < n →
      let child := (assemble parts).insertIdx 0 (n + 1)
      (@Finset.filter ℕ (fun gap => child.insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))).card =
          parts.length + 1) ∧
    (∀ first rest,
      (∀ block ∈ first :: rest, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      first ∈ avoiders first.length [[2, 4, 3, 1], [3, 2, 4, 1]] →
      assemble rest ∈ avoiders (assemble rest).length [[2, 4, 3, 1], [3, 2, 4, 1]] →
      assemble (first :: rest) ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] →
      ∀ site, 0 < site → site < first.length →
        first.insertIdx site (first.length + 1) ∈
          avoiders (first.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] →
      let cuts := @Finset.filter ℕ (fun gap =>
        first.insertIdx gap (first.length + 1) ∈
          avoiders (first.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (first.length + 1))
      let child := (assemble (first :: rest)).insertIdx site (n + 1)
      let childCuts := @Finset.filter ℕ (fun gap => child.insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
      childCuts.card + (cuts.filter fun gap => gap < site).card =
        cuts.card + if rest = [] then 1 else rest.length) ∧
    (∀ p, p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] → 0 < n →
      let cuts := @Finset.filter ℕ (fun gap => p.insertIdx gap (n + 1) ∈
        avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
      ∃ selection : Fin (cuts.card - 2) ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length},
        ∀ index, (cuts.filter fun gap => gap < (selection index).val).card =
          index.val + 1)) ∧
    (∀ _hn : 0 < n,
      let active (size : ℕ) (word : List ℕ) := @Finset.filter ℕ
        (fun gap => word.insertIdx gap (size + 1) ∈
          avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (word.length + 1))
      let components := {parts : List (List ℕ) |
        (∀ block ∈ parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
        assemble parts ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]]}
      let choices := Σ parts : components,
        Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)
      let targets := {word : List ℕ |
        word ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧ sumIndecomposable word}
      ∃ construction : (components ⊕ choices) ≃ targets,
        (∀ parts, (active (n + 1) (construction (Sum.inl parts)).val).card =
          parts.val.length + 1) ∧
        (∀ parts index,
          (active (n + 1) (construction (Sum.inr ⟨parts, index⟩)).val).card =
            (active (parts.val.headD []).length (parts.val.headD [])).card +
              (if parts.val.tail = [] then 1 else parts.val.tail.length) - index.val - 1) ∧
        targets.ncard = (avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]]).ncard + Nat.card choices ∧
        (∀ label,
          {child : targets | (active (n + 1) child.val).card = label + 2}.ncard =
            {parts : components | parts.val.length + 1 = label + 2}.ncard +
            {parts : components |
              (if parts.val.tail = [] then 1 else parts.val.tail.length) ≤ label ∧
                label + 3 ≤ (active (parts.val.headD []).length (parts.val.headD [])).card +
                  (if parts.val.tail = [] then 1 else parts.val.tail.length)}.ncard) ∧
        (∑ᶠ child : targets,
          (Polynomial.X : Polynomial ℚ) ^ ((active (n + 1) child.val).card - 2)) =
            (∑ᶠ parts : components,
              (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1)) +
            ∑ᶠ parts : components,
              (Polynomial.X : Polynomial ℚ) ^
                (if parts.val.tail = [] then 1 else parts.val.tail.length) *
              ∑ exponent ∈ Finset.range
                ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
                (Polynomial.X : Polynomial ℚ) ^ exponent) := by
  classical
  have hfront (n : ℕ) (p : List ℕ) (hp : p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]]) :
      p.insertIdx 0 (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    have hmax : ∀ value ∈ p, value < n + 1 := by
      intro value hv
      have hm := hp.1.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm
      omega
    have hperm : (p.insertIdx 0 (n + 1)).Perm (List.range' 1 (n + 1)) := by
      apply (List.perm_insertIdx (n + 1) p (Nat.zero_le _)).trans
      apply (hp.1.cons (n + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
    refine ⟨hperm, ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (Nat.zero_le _) hmax).mpr
      exact ⟨hp.2.1, by intros; omega⟩
    · intro pattern hpattern hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · rcases (maximum_crossing_pattern_tests n p hp.1 0 (Nat.zero_le _)).2.mp hbad
          with hold | ⟨first, second, third, hf, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
      · rcases (maximum_four_pattern_tests n p hp.1 0 (Nat.zero_le _)).2.2.mp hbad
          with hold | ⟨first, second, third, hf, hs, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
  have hstructure (n : ℕ) :
    Set.BijOn (fun entry : List ℕ × ℕ => entry.1.insertIdx entry.2 (n + 1))
      {entry | entry.1 ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
        (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
          (∀ block ∈ first :: rest, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
          entry.2 < first.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])}
      {p | p ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
        sumIndecomposable p} ∧
    (∀ parts : List (List ℕ),
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      assemble parts ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] → 0 < n →
      let child := (assemble parts).insertIdx 0 (n + 1)
      (@Finset.filter ℕ (fun gap => child.insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))).card =
          parts.length + 1) ∧
    (∀ first rest,
      (∀ block ∈ first :: rest, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      first ∈ avoiders first.length [[2, 4, 3, 1], [3, 2, 4, 1]] →
      assemble rest ∈ avoiders (assemble rest).length [[2, 4, 3, 1], [3, 2, 4, 1]] →
      assemble (first :: rest) ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] →
      ∀ site, 0 < site → site < first.length →
        first.insertIdx site (first.length + 1) ∈
          avoiders (first.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] →
      let cuts := @Finset.filter ℕ (fun gap =>
        first.insertIdx gap (first.length + 1) ∈
          avoiders (first.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (first.length + 1))
      let child := (assemble (first :: rest)).insertIdx site (n + 1)
      let childCuts := @Finset.filter ℕ (fun gap => child.insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
      childCuts.card + (cuts.filter fun gap => gap < site).card =
        cuts.card + if rest = [] then 1 else rest.length) ∧
    (∀ p, p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] → 0 < n →
      let cuts := @Finset.filter ℕ (fun gap => p.insertIdx gap (n + 1) ∈
        avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
      ∃ selection : Fin (cuts.card - 2) ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length},
        ∀ index, (cuts.filter fun gap => gap < (selection index).val).card =
          index.val + 1) := by
    have hfront := hfront n
    refine ⟨?constructors, ?frontCounts, ?internalCounts, ?rankedChoices⟩
    case rankedChoices =>
      intro p hp hn
      have hlast : p.insertIdx p.length (n + 1) ∈
          avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
        have hmax : ∀ value ∈ p, value < n + 1 := by
          intro value hv
          have hm := hp.1.mem_iff.mp hv
          simp only [List.mem_range', Nat.one_mul] at hm
          obtain ⟨offset, ho, heq⟩ := hm
          omega
        have hperm : (p.insertIdx p.length (n + 1)).Perm (List.range' 1 (n + 1)) := by
          apply (List.perm_insertIdx (n + 1) p le_rfl).trans
          apply (hp.1.cons (n + 1)).trans
          rw [List.range'_concat]
          simpa [Nat.add_comm] using
            (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
        refine ⟨hperm, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff p (n + 1) p.length le_rfl hmax).mpr
          refine ⟨hp.2.1, ?_⟩
          intro before later hb hl hbound
          omega
        · intro pattern hpattern hbad
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
          rcases hpattern with rfl | rfl
          · rcases (maximum_crossing_pattern_tests n p hp.1 p.length le_rfl).2.mp hbad
              with hold | ⟨first, second, third, hf, hs, hst, ht, _⟩
            · exact hp.2.2 _ (by simp) hold
            · omega
          · rcases (maximum_four_pattern_tests n p hp.1 p.length le_rfl).2.2.mp hbad
              with hold | ⟨first, second, third, hf, hs, hst, ht, _⟩
            · exact hp.2.2 _ (by simp) hold
            · omega
      dsimp only
      let cuts := (Finset.range (p.length + 1)).filter fun gap =>
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]
      let internal := (cuts.erase 0).erase p.length
      have hlen : p.length = n := by simpa using hp.1.length_eq
      have hzero : 0 ∈ cuts :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hfront p hp⟩
      have hfinal : p.length ∈ cuts :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hlast⟩
      have hfinalErase : p.length ∈ cuts.erase 0 :=
        Finset.mem_erase.mpr ⟨by omega, hfinal⟩
      have hcard : internal.card = cuts.card - 2 := by
        have hfirst := Finset.card_erase_add_one hzero
        have hsecond := Finset.card_erase_add_one hfinalErase
        dsimp only [internal]
        omega
      have htest (gap : ℕ) :
          gap ∈ internal ↔ gap ∈ cuts ∧ 0 < gap ∧ gap < p.length := by
        simp only [internal, Finset.mem_erase]
        constructor
        · rintro ⟨hl, hz, hg⟩
          have hb : gap ≤ p.length := by
            have := (Finset.mem_filter.mp hg).1
            simp only [Finset.mem_range] at this
            omega
          exact ⟨hg, by omega, by omega⟩
        · rintro ⟨hg, hz, hl⟩
          exact ⟨by omega, by omega, hg⟩
      let ordering := internal.orderIsoOfFin hcard
      let correspondence : internal ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length} :=
        Equiv.subtypeEquivRight htest
      let selection := ordering.toEquiv.trans correspondence
      refine ⟨selection, ?_⟩
      intro index
      have hindexBound : index.val < cuts.card - 2 := index.is_lt
      let site := (ordering index).val
      have hsite : site ∈ internal := (ordering index).property
      have hsitePositive := ((htest site).mp hsite).2.1
      have hsiteBound := ((htest site).mp hsite).2.2
      have hsplit : cuts.filter (fun gap => gap < site) =
          insert 0 (internal.filter fun gap => gap < site) := by
        ext gap
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hb⟩
          by_cases hz : gap = 0
          · exact Or.inl hz
          · exact Or.inr ⟨(htest gap).mpr ⟨hg, by omega, by omega⟩, hb⟩
        · rintro (rfl | ⟨hg, hb⟩)
          · exact ⟨hzero, hsitePositive⟩
          · exact ⟨((htest gap).mp hg).1, hb⟩
      have hinternalRank : (internal.filter fun gap => gap < site).card = index.val := by
        have hsmall (rank : ℕ) (hr : rank ∈ Finset.range index.val) :
            rank < cuts.card - 2 := by
          have := Finset.mem_range.mp hr
          omega
        have hbijection : (Finset.range index.val).card =
            (internal.filter fun gap => gap < site).card := by
          apply Finset.card_bij (fun rank hr => (ordering ⟨rank, hsmall rank hr⟩).val)
          · intro rank hr
            apply Finset.mem_filter.mpr
            refine ⟨(ordering ⟨rank, hsmall rank hr⟩).property, ?_⟩
            have hless : (⟨rank, hsmall rank hr⟩ : Fin (cuts.card - 2)) < index :=
              Finset.mem_range.mp hr
            exact ordering.strictMono hless
          · intro first hf second hs heq
            have hequal := ordering.injective (Subtype.ext heq)
            exact congrArg Fin.val hequal
          · intro gap hg
            obtain ⟨hi, hless⟩ := Finset.mem_filter.mp hg
            let rank := ordering.symm ⟨gap, hi⟩
            have hsmallRank : rank < index := by
              apply ordering.lt_iff_lt.mp
              change ordering (ordering.symm ⟨gap, hi⟩) < ordering index
              rw [ordering.apply_symm_apply]
              exact hless
            refine ⟨rank.val, Finset.mem_range.mpr hsmallRank, ?_⟩
            have heq : (⟨rank.val, hsmall rank.val (Finset.mem_range.mpr hsmallRank)⟩ :
                Fin (cuts.card - 2)) = rank := rfl
            rw [heq]
            exact congrArg Subtype.val (ordering.apply_symm_apply ⟨gap, hi⟩)
        simpa only [Finset.card_range] using hbijection.symm
      change (cuts.filter fun gap => gap < site).card = index.val + 1
      rw [hsplit, Finset.card_insert_of_notMem (by simp [internal]), hinternalRank]
    case frontCounts =>
      intro parts hparts hp hn
      exact (FishburnTenThirteenBUpdates.crossing_site_updates n (assemble parts) hn hp 0
        (Nat.zero_le _) (hfront (assemble parts) hp)).2.2.2 rfl parts hparts rfl
    case internalCounts =>
      intro first rest hparts hf hr hp site hpositive hproper hactive
      have hindec := (hparts first (by simp)).2.2
      have hsize : n = first.length + (assemble rest).length := by
        have := hp.1.length_eq
        simpa [assemble, directSum, shift] using this.symm
      by_cases hempty : rest = []
      · subst rest
        have hsizeFirst : n = first.length := by simpa [assemble] using hsize
        rw [hsizeFirst]
        dsimp only
        simp only [assemble, directSum, shift, List.map_nil, List.append_nil, ↓reduceIte]
        let cuts := (Finset.range (first.length + 1)).filter fun gap =>
          first.insertIdx gap (first.length + 1) ∈
            avoiders (first.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]
        have hcount := (FishburnTenThirteenBIndecomposable.crossing_indecomposable_sites
          first.length first hf hindec site hpositive (by omega) hactive).2 hproper
        dsimp only at hcount
        have hbound := Finset.card_filter_le cuts (fun gap => gap < site)
        change _ + (cuts.filter fun gap => gap < site).card = cuts.card + 1
        change _ = cuts.card + 1 - (cuts.filter fun gap => gap < site).card at hcount
        omega
      · have htailPositive : 0 < (assemble rest).length := by
          cases rest with
          | nil => exact (hempty rfl).elim
          | cons next tail =>
            have hnext := (hparts next (by simp)).1
            have hnextLen := List.length_pos_iff.mpr hnext
            simp only [assemble, directSum, List.length_append, shift, List.length_map]
            omega
        have hcount := (FishburnTenThirteenBConstruction.decomposable_internal_construction
          first.length (assemble rest).length first (assemble rest) hf hr
          (by simpa only [assemble, hsize] using hp) hindec htailPositive site hpositive
          hproper hactive rest (fun block hb => hparts block (by simp [hb])) rfl).2.2
        simpa only [assemble, hsize, if_neg hempty] using hcount
    have hvalues (block : List ℕ) (hp : block.Perm (List.range' 1 block.length))
        (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ block.length := by
      have hm := hp.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm
      omega
    have htailPositive (parts : List (List ℕ))
        (hp : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
        ∀ value ∈ assemble parts, 1 ≤ value := by
      induction parts with
      | nil => simp [assemble]
      | cons first rest ih =>
        intro value hv
        rcases List.mem_append.mp hv with hfirst | hrest
        · exact (hvalues first (hp first (by simp)) value hfirst).1
        · obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hrest
          have := ih (fun block hb => hp block (by simp [hb])) small hs
          omega
    have hfirstTest (p : List ℕ) (hp : p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]])
        (first : List ℕ) (rest : List (List ℕ)) (heq : assemble (first :: rest) = p)
        (hparts : ∀ block ∈ first :: rest, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block)
        (site : ℕ) (hs : site ≤ p.length) :
        sumIndecomposable (p.insertIdx site (n + 1)) ↔ site < first.length := by
      have hf := hparts first (by simp)
      have hfirstPositive : 0 < first.length := List.length_pos_iff.mpr hf.1
      have hdecomp : p = first ++ shift first.length (assemble rest) := heq.symm
      have hlength : p.length = first.length + (assemble rest).length := by
        simp [hdecomp, shift]
      have hbefore (index : ℕ) (hb : index < first.length) :
          p.getD index 0 = first.getD index 0 := by
        rw [hdecomp]
        exact List.getD_append _ _ _ _ hb
      have hsmall (index : ℕ) (hb : index < first.length) : p.getD index 0 ≤ first.length := by
        rw [hbefore index hb]
        apply (hvalues first hf.2.1 _ _).2
        rw [List.getD_eq_getElem first 0 hb]
        exact List.getElem_mem hb
      have hlarge (index : ℕ) (hl : first.length ≤ index) (hb : index < p.length) :
          first.length < p.getD index 0 := by
        have hm : p.getD index 0 ∈ shift first.length (assemble rest) := by
          rw [hdecomp, List.getD_append_right _ _ _ _ hl,
            List.getD_eq_getElem _ 0 (by simp only [shift, List.length_map]; omega)]
          exact List.getElem_mem (by simp only [shift, List.length_map]; omega)
        obtain ⟨value, hv, hequal⟩ := List.mem_map.mp hm
        have := htailPositive rest (fun block hb => (hparts block (by simp [hb])).2.1) value hv
        omega
      rw [indecomposable_maximum_insertion n p hp.1 site hs]
      constructor
      · intro hcuts
        by_contra hnot
        obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
          hcuts first.length hfirstPositive (by omega)
        have := hsmall before hb
        have := hlarge later hl hbound
        omega
      · intro hproper boundary hb hs
        obtain ⟨before, later, hbad⟩ := hf.2.2 ⟨boundary, by omega⟩ hb
        have hbef : before.val < boundary := by
          have := before.is_lt
          simp only [List.length_take] at this
          omega
        have hlat : boundary + later.val < first.length := by
          have := later.is_lt
          simp only [List.length_drop] at this
          omega
        refine ⟨before.val, boundary + later.val, hbef, by omega, by omega, ?_⟩
        rw [hbefore before.val (by omega), hbefore (boundary + later.val) hlat,
          List.getD_eq_getElem first 0 (by omega : before.val < first.length),
          List.getD_eq_getElem first 0 hlat]
        simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hbad
    have hsource (entry : List ℕ × ℕ)
        (he : entry.1 ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
            (∀ block ∈ first :: rest, block ≠ [] ∧
              block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
            entry.2 < first.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
              avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])) :
        entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
          avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
            sumIndecomposable (entry.1.insertIdx entry.2 (n + 1)) := by
      rcases he.2 with hz | ⟨first, rest, heq, hparts, hb, ha⟩
      · refine ⟨by omega, by simpa only [hz] using hfront entry.1 he.1, ?_⟩
        apply (indecomposable_maximum_insertion n entry.1 he.1.1 entry.2 (by omega)).mpr
        intros
        omega
      · have hlength : entry.1.length = first.length + (assemble rest).length := by
          rw [← heq]
          simp [assemble, directSum, shift]
        exact ⟨by omega, ha, (hfirstTest entry.1 he.1 first rest heq hparts entry.2
          (by omega)).mpr hb⟩
    have hbij := maximum_insertion_bijection n [[2, 4, 3, 1], [3, 2, 4, 1]]
    refine ⟨?_, ?_, ?_⟩
    · intro entry he
      exact (hsource entry he).2
    · intro first hf second hs heq
      have hfirst := hsource first hf
      have hsecond := hsource second hs
      let firstRaw : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]} :=
        ⟨first, hf.1, hfirst.1, hfirst.2.1⟩
      let secondRaw : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]} :=
        ⟨second, hs.1, hsecond.1, hsecond.2.1⟩
      have hraw := hbij.1 (a₁ := firstRaw) (a₂ := secondRaw) (Subtype.ext heq)
      exact congrArg Subtype.val hraw
    · intro p hp
      obtain ⟨entry, heq⟩ := hbij.2 ⟨p, hp.1⟩
      have hword : entry.val.1.insertIdx entry.val.2 (n + 1) = p :=
        congrArg Subtype.val heq
      refine ⟨entry.val, ⟨entry.property.1, ?_⟩, hword⟩
      by_cases hz : entry.val.2 = 0
      · exact Or.inl hz
      have hpatterns : ∀ pattern ∈ [[2, 4, 3, 1], [3, 2, 4, 1]],
          pattern ≠ [] ∧ sumIndecomposable pattern ∧ (∀ value ∈ pattern, 1 ≤ value) ∧
            ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern →
              rank ∈ pattern := by
        intro pattern hpattern
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl
        all_goals
          refine ⟨by decide, by unfold sumIndecomposable; decide, by simp, ?_⟩
          intro rank hr hbound
          norm_num [NonnestingDefs.letters] at hbound
          simp only [List.mem_cons, List.not_mem_nil]
          omega
      obtain ⟨parts, hparts, _⟩ := (unique_sum_components n entry.val.1 entry.property.1.1
        [[2, 4, 3, 1], [3, 2, 4, 1]] hpatterns).1
      cases parts with
      | nil =>
        have hempty : entry.val.1 = [] := by simpa [assemble] using hparts.1.symm
        have := entry.property.2.1
        simp only [hempty, List.length_nil] at this
        omega
      | cons first rest =>
        have hproper := (hfirstTest entry.val.1 entry.property.1 first rest hparts.1
          hparts.2.1 entry.val.2 entry.property.2.1).mp (by rw [hword]; exact hp.2)
        exact Or.inr ⟨first, rest, hparts.1, hparts.2.1, hproper, entry.property.2.2⟩
  refine ⟨hstructure n, ?_⟩
  intro hn
  have hstructureGlobal := hstructure
  have hstructure := hstructure n
  dsimp only
  let patterns := [[2, 4, 3, 1], [3, 2, 4, 1]]
  let active (size : ℕ) (word : List ℕ) := (Finset.range (word.length + 1)).filter
    fun gap => word.insertIdx gap (size + 1) ∈ avoiders (size + 1) patterns
  let components : Set (List (List ℕ)) := {parts |
    (∀ block ∈ parts, block ≠ [] ∧
      block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
    assemble parts ∈ avoiders n patterns}
  let choices := Σ parts : components,
    Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)
  have hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
      (∀ value ∈ pattern, 1 ≤ value) ∧
      ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern := by
    intro pattern hp
    simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals
      refine ⟨by decide, by unfold sumIndecomposable; decide, by simp, ?_⟩
      intro rank hr hb
      norm_num [NonnestingDefs.letters] at hb
      simp only [List.mem_cons, List.not_mem_nil]
      omega
  have hclosure := (unique_sum_components 0 [] (by simp) patterns hpatterns).2.1
  have hinfo (parts : components) :
      parts.val.headD [] ≠ [] ∧
      parts.val.headD [] ∈ avoiders (parts.val.headD []).length patterns ∧
      assemble parts.val.tail ∈ avoiders (assemble parts.val.tail).length patterns ∧
      parts.val = parts.val.headD [] :: parts.val.tail ∧
      n = (parts.val.headD []).length + (assemble parts.val.tail).length := by
    have hv := parts.property.1
    have hp := parts.property.2
    cases heq : parts.val with
    | nil =>
      rw [heq] at hp
      have hlen := hp.1.length_eq
      simp only [assemble, List.length_nil, List.length_range'] at hlen
      omega
    | cons first rest =>
      rw [heq] at hv hp
      change first ≠ [] ∧ first ∈ avoiders first.length patterns ∧
        assemble rest ∈ avoiders (assemble rest).length patterns ∧
        first :: rest = first :: rest ∧ n = first.length + (assemble rest).length
      have hlen : (assemble (first :: rest)).length = n := by simpa using hp.1.length_eq
      have hblocks := (hclosure (first :: rest) hv).mp (by simpa only [hlen] using hp)
      refine ⟨(hv first (by simp)).1, hblocks first (by simp), ?_, rfl, ?_⟩
      · apply (hclosure rest (fun block hb => hv block (by simp [hb]))).mpr
        exact fun block hb => hblocks block (by simp [hb])
      · simpa only [assemble, directSum, shift, List.length_append, List.length_map]
          using hlen.symm
  let serialize (parts : components) : avoiders n patterns :=
    ⟨assemble parts.val, parts.property.2⟩
  have hserialize : Function.Injective serialize := by
    intro left right heq
    have hequal : assemble left.val = assemble right.val := congrArg Subtype.val heq
    obtain ⟨canonical, _, hu⟩ :=
      (unique_sum_components n (assemble left.val) left.property.2.1 patterns hpatterns).1
    have hlen : (assemble left.val).length = n := by simpa using left.property.2.1.length_eq
    have hl : left.val = canonical := hu _ ⟨rfl, left.property.1, by
      simpa only [hlen] using hclosure left.val left.property.1⟩
    have hr : right.val = canonical := hu _ ⟨hequal.symm, right.property.1, by
      simpa only [← hequal, hlen] using hclosure right.val right.property.1⟩
    exact Subtype.ext (hl.trans hr.symm)
  have hserializeSurjective : Function.Surjective serialize := by
    intro word
    obtain ⟨parts, hp, _⟩ :=
      (unique_sum_components n word.val word.property.1 patterns hpatterns).1
    exact ⟨⟨parts, hp.2.1, by rw [hp.1]; exact word.property⟩, Subtype.ext hp.1⟩
  have hsite (parts : components) (gap : ℕ) (hb : gap ≤ (parts.val.headD []).length) :
      (assemble parts.val).insertIdx gap (n + 1) ∈ avoiders (n + 1) patterns ↔
        (parts.val.headD []).insertIdx gap ((parts.val.headD []).length + 1) ∈
          avoiders ((parts.val.headD []).length + 1) patterns := by
    have hi := hinfo parts
    have heq : assemble parts.val = directSum (parts.val.headD []).length
        (parts.val.headD []) (assemble parts.val.tail) := by
      conv_lhs => rw [hi.2.2.2.1]
      rfl
    have hs := FishburnTenThirteenBSums.crossing_sum_sites
      (parts.val.headD []).length (assemble parts.val.tail).length
      (parts.val.headD []) (assemble parts.val.tail) hi.2.1 hi.2.2.1
      (by simpa only [heq, hi.2.2.2.2] using parts.property.2)
    simpa only [← heq, ← hi.2.2.2.2] using hs.1 gap hb
  let pick (parts : components) :
      Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2) ≃
        {gap : ℕ // gap ∈ active (parts.val.headD []).length (parts.val.headD []) ∧
          0 < gap ∧ gap < (parts.val.headD []).length} :=
    Classical.choose ((hstructureGlobal (parts.val.headD []).length).2.2.2
      (parts.val.headD []) (hinfo parts).2.1
      (List.length_pos_iff_ne_nil.mpr (hinfo parts).1))
  have hpick (parts : components)
      (index : Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)) :
      ((active (parts.val.headD []).length (parts.val.headD [])).filter
        fun gap => gap < (pick parts index).val).card = index.val + 1 :=
    Classical.choose_spec ((hstructureGlobal (parts.val.headD []).length).2.2.2
      (parts.val.headD []) (hinfo parts).2.1
      (List.length_pos_iff_ne_nil.mpr (hinfo parts).1)) index
  let domain : Set (List ℕ × ℕ) := {entry | entry.1 ∈ avoiders n patterns ∧
    (entry.2 = 0 ∨ ∃ first rest, assemble (first :: rest) = entry.1 ∧
      (∀ block ∈ first :: rest, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      entry.2 < first.length ∧
      entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns)}
  let raw : components ⊕ choices → domain
    | Sum.inl parts => ⟨(assemble parts.val, 0), parts.property.2, Or.inl rfl⟩
    | Sum.inr ⟨parts, index⟩ => ⟨(assemble parts.val, (pick parts index).val),
      parts.property.2, Or.inr ⟨parts.val.headD [], parts.val.tail,
        congrArg assemble (hinfo parts).2.2.2.1.symm,
        by simpa only [← (hinfo parts).2.2.2.1] using parts.property.1,
        (pick parts index).property.2.2,
        (hsite parts _ (Nat.le_of_lt (pick parts index).property.2.2)).mpr
          (Finset.mem_filter.mp (pick parts index).property.1).2⟩⟩
  have hrawInjective : Function.Injective raw := by
    intro left right heq
    have hv := congrArg Subtype.val heq
    cases left with
    | inl left =>
      cases right with
      | inl right =>
        exact congrArg Sum.inl (hserialize (Subtype.ext (congrArg Prod.fst hv)))
      | inr right =>
        have hs := congrArg Prod.snd hv
        have hp := (pick right.1 right.2).property.2.1
        change 0 = (pick right.1 right.2).val at hs
        omega
    | inr left =>
      cases right with
      | inl right =>
        have hs := congrArg Prod.snd hv
        have hp := (pick left.1 left.2).property.2.1
        change (pick left.1 left.2).val = 0 at hs
        omega
      | inr right =>
        have hparts : left.1 = right.1 :=
          hserialize (Subtype.ext (congrArg Prod.fst hv))
        rcases left with ⟨lp, li⟩
        rcases right with ⟨rp, ri⟩
        dsimp at hparts
        subst rp
        have hindex : li = ri := (pick lp).injective (Subtype.ext (congrArg Prod.snd hv))
        subst ri
        rfl
  have hrawSurjective : Function.Surjective raw := by
    intro entry
    by_cases hz : entry.val.2 = 0
    · let parts := (Equiv.ofBijective serialize ⟨hserialize, hserializeSurjective⟩).symm
        ⟨entry.val.1, entry.property.1⟩
      have heq : assemble parts.val = entry.val.1 := congrArg Subtype.val
        ((Equiv.ofBijective serialize ⟨hserialize, hserializeSurjective⟩).apply_symm_apply
          ⟨entry.val.1, entry.property.1⟩)
      exact ⟨Sum.inl parts, Subtype.ext (Prod.ext heq hz.symm)⟩
    · obtain ⟨first, rest, heq, hv, hb, ha⟩ := entry.property.2.resolve_left hz
      let parts : components := ⟨first :: rest, hv, by rw [heq]; exact entry.property.1⟩
      have hbound : entry.val.2 ≤ first.length := by omega
      have hlocal := (hsite parts entry.val.2 hbound).mp
        (by simpa only [parts, heq] using ha)
      let gap : {gap : ℕ // gap ∈ active (parts.val.headD []).length
          (parts.val.headD []) ∧ 0 < gap ∧ gap < (parts.val.headD []).length} :=
        ⟨entry.val.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          change entry.val.2 < first.length + 1
          omega), hlocal⟩, by omega, hb⟩
      refine ⟨Sum.inr ⟨parts, (pick parts).symm gap⟩, Subtype.ext ?_⟩
      change (assemble parts.val, (pick parts ((pick parts).symm gap)).val) = entry.val
      exact Prod.ext heq (congrArg Subtype.val ((pick parts).apply_symm_apply gap))
  let construction := (Equiv.ofBijective raw ⟨hrawInjective, hrawSurjective⟩).trans
    hstructure.1.equiv
  have hfrontLabels (parts : components) :
      (active (n + 1) (construction (Sum.inl parts)).val).card = parts.val.length + 1 := by
    exact hstructure.2.1 parts.val parts.property.1 parts.property.2 hn
  have hinternalLabels (parts : components)
      (index : Fin ((active (parts.val.headD []).length (parts.val.headD [])).card - 2)) :
      (active (n + 1) (construction (Sum.inr ⟨parts, index⟩)).val).card =
        (active (parts.val.headD []).length (parts.val.headD [])).card +
          (if parts.val.tail = [] then 1 else parts.val.tail.length) - index.val - 1 := by
    have hi := hinfo parts
    have hv : ∀ block ∈ parts.val.headD [] :: parts.val.tail, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
      simpa only [← hi.2.2.2.1] using parts.property.1
    have hp : assemble (parts.val.headD [] :: parts.val.tail) ∈ avoiders n patterns := by
      simpa only [← hi.2.2.2.1] using parts.property.2
    have hf := hstructure.2.2.1 (parts.val.headD []) parts.val.tail hv hi.2.1 hi.2.2.1 hp
      (pick parts index).val (pick parts index).property.2.1 (pick parts index).property.2.2
      (Finset.mem_filter.mp (pick parts index).property.1).2
    have hrank := hpick parts index
    change (active (n + 1)
        ((assemble (parts.val.headD [] :: parts.val.tail)).insertIdx
          (pick parts index).val (n + 1))).card +
      ((active (parts.val.headD []).length (parts.val.headD [])).filter
        fun gap => gap < (pick parts index).val).card =
      (active (parts.val.headD []).length (parts.val.headD [])).card +
        if parts.val.tail = [] then 1 else parts.val.tail.length at hf
    rw [← hi.2.2.2.1, hrank] at hf
    change (active (n + 1)
      ((assemble parts.val).insertIdx (pick parts index).val (n + 1))).card = _
    omega
  have hfinite : (avoiders n patterns).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  let : Finite (avoiders n patterns) := hfinite.to_subtype
  let : Finite components := Finite.of_injective serialize hserialize
  refine ⟨construction, hfrontLabels, hinternalLabels, ?_, ?_, ?_⟩
  · have hcard := Nat.card_congr construction
    have hbase := Nat.card_congr
      (Equiv.ofBijective serialize ⟨hserialize, hserializeSurjective⟩)
    rw [Nat.card_sum, hbase, Nat.card_coe_set_eq] at hcard
    exact hcard.symm
  · intro label
    have hinternalAll (entry : choices) :
        (active (n + 1) (construction (Sum.inr entry)).val).card =
          (active (entry.1.val.headD []).length (entry.1.val.headD [])).card +
            (if entry.1.val.tail = [] then 1 else entry.1.val.tail.length) - entry.2.val - 1 :=
      hinternalLabels entry.1 entry.2
    let labelled := construction.subtypeEquivOfSubtype
      (p := fun child => (active (n + 1) child.val).card = label + 2)
    have hcard := Nat.card_congr (labelled.symm.trans Equiv.subtypeSum)
    let forget : {entry : choices //
        (active (entry.1.val.headD []).length (entry.1.val.headD [])).card +
          (if entry.1.val.tail = [] then 1 else entry.1.val.tail.length) -
            entry.2.val - 1 = label + 2} → {parts : components //
        (if parts.val.tail = [] then 1 else parts.val.tail.length) ≤ label ∧
          label + 3 ≤ (active (parts.val.headD []).length (parts.val.headD [])).card +
            (if parts.val.tail = [] then 1 else parts.val.tail.length)} :=
      fun entry => ⟨entry.val.1, by
        have hi := entry.val.2.isLt
        have hl := entry.property
        omega⟩
    have hforgetInjective : Function.Injective forget := by
      intro left right heq
      have hparts := congrArg Subtype.val heq
      rcases left with ⟨⟨lp, li⟩, hl⟩
      rcases right with ⟨⟨rp, ri⟩, hr⟩
      change lp = rp at hparts
      subst rp
      dsimp only at hl hr
      have hindex : li = ri := by
        apply Fin.ext
        have hli := li.isLt
        have hri := ri.isLt
        omega
      subst ri
      rfl
    have hforgetSurjective : Function.Surjective forget := by
      intro parts
      let rank : Fin ((active (parts.val.val.headD []).length
          (parts.val.val.headD [])).card - 2) :=
        ⟨(active (parts.val.val.headD []).length (parts.val.val.headD [])).card +
          (if parts.val.val.tail = [] then 1 else parts.val.val.tail.length) - (label + 3), by
          have hp := parts.property
          omega⟩
      refine ⟨⟨⟨parts.val, rank⟩, ?_⟩, Subtype.ext rfl⟩
      change (active (parts.val.val.headD []).length (parts.val.val.headD [])).card +
        (if parts.val.val.tail = [] then 1 else parts.val.val.tail.length) -
          rank.val - 1 = label + 2
      dsimp only [rank]
      have hp := parts.property
      omega
    change Nat.card {child : {word : List ℕ |
        word ∈ avoiders (n + 1) patterns ∧ sumIndecomposable word} //
          (active (n + 1) child.val).card = label + 2} =
      Nat.card {parts : components // parts.val.length + 1 = label + 2} +
      Nat.card {parts : components //
        (if parts.val.tail = [] then 1 else parts.val.tail.length) ≤ label ∧
          label + 3 ≤ (active (parts.val.headD []).length (parts.val.headD [])).card +
            (if parts.val.tail = [] then 1 else parts.val.tail.length)}
    simp only [Nat.card_sum, hfrontLabels, hinternalAll] at hcard
    rw [Nat.card_congr (Equiv.ofBijective forget
      ⟨hforgetInjective, hforgetSurjective⟩)] at hcard
    exact hcard
  · let : Fintype components := Fintype.ofFinite _
    change (∑ᶠ child : {word : List ℕ |
        word ∈ avoiders (n + 1) patterns ∧ sumIndecomposable word},
        (Polynomial.X : Polynomial ℚ) ^ ((active (n + 1) child.val).card - 2)) =
      (∑ᶠ parts : components, (Polynomial.X : Polynomial ℚ) ^ (parts.val.length - 1)) +
      ∑ᶠ parts : components,
        (Polynomial.X : Polynomial ℚ) ^
          (if parts.val.tail = [] then 1 else parts.val.tail.length) *
          ∑ exponent ∈ Finset.range
            ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ exponent
    rw [← finsum_comp_equiv construction]
    simp only [finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro parts _
      rw [hfrontLabels]
      congr 1
    · rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro parts _
      have hsum : (∑ index : Fin
          ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
          (Polynomial.X : Polynomial ℚ) ^
            ((active (n + 1) (construction (Sum.inr ⟨parts, index⟩)).val).card - 2)) =
          ∑ index : Fin
            ((active (parts.val.headD []).length (parts.val.headD [])).card - 2),
            (Polynomial.X : Polynomial ℚ) ^
              ((active (parts.val.headD []).length (parts.val.headD [])).card +
                (if parts.val.tail = [] then 1 else parts.val.tail.length) - index.val - 3) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [hinternalLabels]
        congr 1
      rw [hsum, Fin.sum_univ_eq_sum_range (fun index =>
        (Polynomial.X : Polynomial ℚ) ^
          ((active (parts.val.headD []).length (parts.val.headD [])).card +
            (if parts.val.tail = [] then 1 else parts.val.tail.length) - index - 3))]
      rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun index =>
        (Polynomial.X : Polynomial ℚ) ^
          (if parts.val.tail = [] then 1 else parts.val.tail.length) * Polynomial.X ^ index)]
      apply Finset.sum_congr rfl
      intro index hi; rw [← pow_add]
      have := Finset.mem_range.mp hi
      congr 1; omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBReconstruction
