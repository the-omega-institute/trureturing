/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenAConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenAConstruction
   mirror-E: none(waiver:indecomposable-maximum-parent-bijection)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Indecomposable A constructors are reversible and have exact ranked cut labels. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSites
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenASums
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSumInsertion
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.GeomSum

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenAConstruction

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnTenThirteenSites
open FishburnBasicParents FishburnBasicSumInsertion NonnestingBasicSum
open FishburnTenThirteenSiteUpdates FishburnTenThirteenASums

theorem indecomposable_construction (n : ℕ) :
    (Set.BijOn (fun entry : List ℕ × ℕ => entry.1.insertIdx entry.2 (n + 1))
      {entry | entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        (entry.2 = 0 ∨ sumIndecomposable entry.1 ∧ entry.2 < entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])}
      {p | p ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        sumIndecomposable p} ∧
    (∀ p, p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] → 0 < n →
      ∀ site, site ≤ p.length →
        p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] →
        (site = 0 ∨ sumIndecomposable p ∧ site < p.length) →
        let cuts := @Finset.filter ℕ (fun gap =>
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
        let child := p.insertIdx site (n + 1)
        let childCuts := @Finset.filter ℕ (fun gap =>
          child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
        childCuts.card = if site = 0 then cuts.card else
          cuts.card + 1 - (cuts.filter fun gap => gap < site).card) ∧
    (∀ p, p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] → 0 < n →
      let cuts := @Finset.filter ℕ (fun gap => p.insertIdx gap (n + 1) ∈
        avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
      ∃ selection : Fin (cuts.card - 2) ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length},
        ∀ index, (cuts.filter fun gap => gap < (selection index).val).card =
          index.val + 1)) ∧
    (∀ _hn : 0 < n,
      let active (size : ℕ) (word : List ℕ) := @Finset.filter ℕ
        (fun gap => word.insertIdx gap (size + 1) ∈
          avoiders (size + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (word.length + 1))
      let parents := {word : List ℕ | word ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        sumIndecomposable word}
      let choices := Σ parent : parents, Fin ((active n parent.val).card - 2)
      let targets := {word : List ℕ |
        word ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧ sumIndecomposable word}
      ∃ construction : (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ⊕ choices) ≃ targets,
        (∀ parent, (active (n + 1) (construction (Sum.inl parent)).val).card =
          (active n parent.val).card) ∧
        (∀ parent index,
          (active (n + 1) (construction (Sum.inr ⟨parent, index⟩)).val).card =
            (active n parent.val).card - index.val) ∧
        targets.ncard = (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]).ncard +
          Nat.card choices ∧
        (∀ label,
          {child : targets | (active (n + 1) child.val).card = label + 2}.ncard =
            {parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] |
              (active n parent.val).card = label + 2}.ncard +
            {parent : parents | 0 < label ∧ label + 2 ≤ (active n parent.val).card}.ncard) ∧
        (∀ weight : ℕ → Polynomial ℚ,
          (∑ᶠ child : targets, weight ((active (n + 1) child.val).card - 2)) =
            (∑ᶠ parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]],
              weight ((active n parent.val).card - 2)) +
            ∑ᶠ parent : parents, ∑ᶠ index : Fin ((active n parent.val).card - 2),
              weight ((active n parent.val).card - index.val - 2)) ∧
        (let labelled := ∑ᶠ parent : parents,
           (Polynomial.X : Polynomial ℚ) ^ ((active n parent.val).card - 2)
         let quotient := ∑ᶠ parent : parents,
           ∑ exponent ∈ Finset.range ((active n parent.val).card - 2),
             (Polynomial.X : Polynomial ℚ) ^ exponent
         (1 - Polynomial.X) * quotient = Polynomial.C (parents.ncard : ℚ) - labelled ∧
         (∑ᶠ child : targets,
           (Polynomial.X : Polynomial ℚ) ^ ((active (n + 1) child.val).card - 2)) =
           (∑ᶠ parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]],
             (Polynomial.X : Polynomial ℚ) ^ ((active n parent.val).card - 2)) +
             Polynomial.X * quotient)) := by
  classical
  have hfront (p : List ℕ)
      (hp : p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]) :
      p.insertIdx 0 (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
    apply (interval_active_sites n p hp 0 (Nat.zero_le _)).mpr
    refine ⟨by omega, ?_⟩
    constructor
    intro low hlo high hhi middle hbetween
    have hl : 1 ≤ low := by
      have hr := hp.1.mem_iff.mp (by simpa using hlo)
      simp only [List.mem_range', Nat.one_mul] at hr
      obtain ⟨index, hi, heq⟩ := hr
      omega
    have hh : high ≤ n := by
      have hr := hp.1.mem_iff.mp (by simpa using hhi)
      simp only [List.mem_range', Nat.one_mul] at hr
      obtain ⟨index, hi, heq⟩ := hr
      omega
    change middle ∈ p.drop 0
    simp only [List.drop_zero]
    apply hp.1.mem_iff.mpr
    simp only [List.mem_range', Nat.one_mul]
    have hbounds : low ≤ middle ∧ middle ≤ high := hbetween
    exact ⟨middle - 1, by omega, by omega⟩
  have hclassify (p : List ℕ)
      (hp : p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]])
      (site : ℕ) (hs : site ≤ p.length)
      (hc : p.insertIdx site (n + 1) ∈
        avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]) :
      sumIndecomposable (p.insertIdx site (n + 1)) ↔
        site = 0 ∨ sumIndecomposable p ∧ site < p.length := by
    have hprefix (cut index : ℕ) (hi : index < cut) (hb : index < p.length) :
        p.getD index 0 ∈ p.take cut := by
      apply List.mem_take_iff_getElem.mpr
      exact ⟨index, by omega, (List.getD_eq_getElem p 0 hb).symm⟩
    have hsuffix (cut index : ℕ) (hi : cut ≤ index) (hb : index < p.length) :
        p.getD index 0 ∈ p.drop cut := by
      apply List.mem_drop_iff_getElem.mpr
      refine ⟨index - cut, by omega, ?_⟩
      have heq : cut + (index - cut) = index := by omega
      simpa only [heq] using (List.getD_eq_getElem p 0 hb).symm
    have hcutWitness (cut before later : ℕ)
        (hbefore : before < cut) (hlater : cut ≤ later) (hb : later < p.length)
        (hbad : p.getD later 0 ≤ p.getD before 0) :
        ∃ first : Fin (p.take cut).length, ∃ second : Fin (p.drop cut).length,
          (p.drop cut).get second ≤ (p.take cut).get first := by
      let first : Fin (p.take cut).length := ⟨before, by
        simp only [List.length_take]
        omega⟩
      let second : Fin (p.drop cut).length := ⟨later - cut, by
        simp only [List.length_drop]
        omega⟩
      refine ⟨first, second, ?_⟩
      have heq : cut + (later - cut) = later := by omega
      simpa only [first, second, List.get_eq_getElem, List.getElem_take, List.getElem_drop,
        heq, List.getD_eq_getElem p 0 hb,
        List.getD_eq_getElem p 0 (by omega : before < p.length)] using hbad
    rw [indecomposable_maximum_insertion n p hp.1 site hs]
    constructor
    · intro hcuts
      by_cases hzero : site = 0
      · exact Or.inl hzero
      have hpositive : 0 < site := by omega
      obtain ⟨before, later, hb, hl, hbound, hbad⟩ := hcuts site hpositive le_rfl
      have hproper : site < p.length := by omega
      have hconn := (interval_active_sites n p hp site hs).mp hc |>.2
      have hmaxnot : n ∉ p.drop site := by
        intro hmax
        have hvalue : p.getD before 0 ≤ n := by
          have hr := hp.1.mem_iff.mp
            ((List.take_sublist site p).subset (hprefix site before hb (by omega)))
          simp only [List.mem_range', Nat.one_mul] at hr
          obtain ⟨offset, hoffset, heq⟩ := hr
          omega
        have hm : p.getD before 0 ∈ p.drop site :=
          hconn.out (hsuffix site later hl hbound) hmax ⟨hbad, hvalue⟩
        have hnd := hp.1.nodup_iff.mpr (List.nodup_range' 1)
        have happ : (p.take site ++ p.drop site).Nodup := by simpa using hnd
        exact (List.nodup_append.mp happ).2.2 _ (hprefix site before hb (by omega)) _ hm rfl
      have hlength : p.length = n := by simpa using hp.1.length_eq
      have hn : 0 < n := by omega
      have hmax : n ∈ p.take site := by
        have hm : n ∈ p := by
          apply hp.1.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n - 1, by omega, by omega⟩
        have happ : n ∈ p.take site ++ p.drop site := by simpa using hm
        exact (List.mem_append.mp happ).resolve_right hmaxnot
      obtain ⟨maxIndex, hmaxIndex, hmaxValue⟩ := List.mem_take_iff_getElem.mp hmax
      have hmaxD : p.getD maxIndex 0 = n :=
        (List.getD_eq_getElem p 0 (by omega)).trans hmaxValue
      refine Or.inr ⟨?_, hproper⟩
      intro cut hcutpositive
      by_cases hcut : cut.val ≤ site
      · obtain ⟨first, second, hf, hl, hb, hbad⟩ := hcuts cut.val hcutpositive hcut
        exact hcutWitness cut.val first second hf hl hb hbad
      · have hvalue : p.getD cut.val 0 ≤ n := by
          have hm : p.getD cut.val 0 ∈ p := by
            rw [List.getD_eq_getElem p 0 cut.is_lt]
            exact List.getElem_mem cut.is_lt
          have hr := hp.1.mem_iff.mp hm
          simp only [List.mem_range', Nat.one_mul] at hr
          obtain ⟨offset, hoffset, heq⟩ := hr
          omega
        apply hcutWitness cut.val maxIndex cut.val (by omega) le_rfl cut.is_lt
        rwa [hmaxD]
    · rintro (hzero | ⟨hindec, hproper⟩) cut hpositive hcut
      · omega
      · obtain ⟨before, later, hbad⟩ := hindec ⟨cut, by omega⟩ hpositive
        have hbefore : before.val < cut := by
          have := before.is_lt
          simp only [List.length_take] at this
          omega
        have hlater : cut + later.val < p.length := by
          have := later.is_lt
          simp only [List.length_drop] at this
          omega
        refine ⟨before.val, cut + later.val, hbefore, by omega, hlater, ?_⟩
        simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop,
          List.getD_eq_getElem p 0 hlater,
          List.getD_eq_getElem p 0 (by omega : before.val < p.length)] using hbad
  have hsource (entry : List ℕ × ℕ)
      (he : entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        (entry.2 = 0 ∨ sumIndecomposable entry.1 ∧ entry.2 < entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])) :
      entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        entry.2 ≤ entry.1.length ∧
        entry.1.insertIdx entry.2 (n + 1) ∈
          avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        (entry.2 = 0 ∨ sumIndecomposable entry.1 ∧ entry.2 < entry.1.length) := by
    rcases he.2 with hz | ⟨hi, hb, ha⟩
    · exact ⟨he.1, by omega, by simpa only [hz] using hfront entry.1 he.1, Or.inl hz⟩
    · exact ⟨he.1, by omega, ha, Or.inr ⟨hi, hb⟩⟩
  have hbij := maximum_insertion_bijection n [[2, 4, 1, 3], [2, 4, 3, 1]]
  have hstructure :
    Set.BijOn (fun entry : List ℕ × ℕ => entry.1.insertIdx entry.2 (n + 1))
      {entry | entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        (entry.2 = 0 ∨ sumIndecomposable entry.1 ∧ entry.2 < entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])}
      {p | p ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
        sumIndecomposable p} ∧
    (∀ p, p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] → 0 < n →
      ∀ site, site ≤ p.length →
        p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] →
        (site = 0 ∨ sumIndecomposable p ∧ site < p.length) →
        let cuts := @Finset.filter ℕ (fun gap =>
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
        let child := p.insertIdx site (n + 1)
        let childCuts := @Finset.filter ℕ (fun gap =>
          child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
        childCuts.card = if site = 0 then cuts.card else
          cuts.card + 1 - (cuts.filter fun gap => gap < site).card) ∧
    (∀ p, p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] → 0 < n →
      let cuts := @Finset.filter ℕ (fun gap => p.insertIdx gap (n + 1) ∈
        avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
        (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
      ∃ selection : Fin (cuts.card - 2) ≃
          {gap : ℕ // gap ∈ cuts ∧ 0 < gap ∧ gap < p.length},
        ∀ index, (cuts.filter fun gap => gap < (selection index).val).card =
          index.val + 1) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?rankedChoices⟩
    case rankedChoices =>
      intro p hp hn
      have hlast : p.insertIdx p.length (n + 1) ∈
          avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
        apply (interval_active_sites n p hp p.length le_rfl).mpr
        refine ⟨?_, ?_⟩
        · intros
          omega
        · constructor
          intro low hlo
          simp at hlo
      dsimp only
      let cuts := (Finset.range (p.length + 1)).filter fun gap =>
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]
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
    · intro entry he
      have he := hsource entry he
      exact ⟨he.2.2.1, (hclassify entry.1 he.1 entry.2 he.2.1 he.2.2.1).mpr he.2.2.2⟩
    · intro first hf second hs heq
      have hf := hsource first hf
      have hs := hsource second hs
      let firstRaw : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]} :=
        ⟨first, hf.1, hf.2.1, hf.2.2.1⟩
      let secondRaw : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
          entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]} :=
        ⟨second, hs.1, hs.2.1, hs.2.2.1⟩
      have hraw : firstRaw = secondRaw := hbij.1 (Subtype.ext heq)
      exact congrArg Subtype.val hraw
    · intro child hc
      obtain ⟨entry, heq⟩ := hbij.2 ⟨child, hc.1⟩
      have hword : entry.val.1.insertIdx entry.val.2 (n + 1) = child :=
        congrArg Subtype.val heq
      refine ⟨entry.val, ⟨entry.property.1, ?_⟩, hword⟩
      have hcases := (hclassify entry.val.1 entry.property.1 entry.val.2 entry.property.2.1
        entry.property.2.2).mp (by rw [hword]; exact hc.2)
      rcases hcases with hz | ⟨hi, hb⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hi, hb, entry.property.2.2⟩
    · intro p hp hn site hs hc hwhich
      dsimp only
      let cuts := (Finset.range (p.length + 1)).filter fun gap =>
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]
      let child := p.insertIdx site (n + 1)
      let childCuts := (Finset.range (child.length + 1)).filter fun gap =>
        child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]]
      let laterCuts := cuts.filter fun gap => site < gap
      change childCuts.card = if site = 0 then cuts.card else
        cuts.card + 1 - (cuts.filter fun gap => gap < site).card
      have hlength : child.length = p.length + 1 :=
        List.length_insertIdx_of_le_length hs _
      have hcuts (gap : ℕ) : gap ∈ cuts ↔ gap ≤ p.length ∧
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
        simp only [cuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      have hchildren (gap : ℕ) : gap ∈ childCuts ↔ gap ≤ child.length ∧
          child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
        simp only [childCuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      have hzero : 0 ∈ cuts := (hcuts 0).mpr ⟨Nat.zero_le _, hfront p hp⟩
      have hupdates := interval_site_updates n p hn hp site hs hc
      have hchildZero : 0 ∈ childCuts := by
        apply (hchildren 0).mpr
        refine ⟨Nat.zero_le _, (hupdates.1 0 (Nat.zero_le _)).mpr ?_⟩
        simp
      have himage (gap : ℕ) : gap ∈ laterCuts.image (· + 1) ↔
          ∃ old, old ∈ cuts ∧ site < old ∧ old + 1 = gap := by
        simp only [Finset.mem_image, laterCuts, Finset.mem_filter]
        aesop
      have hdisjoint : Disjoint ({0} : Finset ℕ) (laterCuts.image (· + 1)) := by
        apply Finset.disjoint_left.mpr
        intro gap hgap him
        obtain ⟨old, _, _, heq⟩ := (himage gap).mp him
        simp only [Finset.mem_singleton] at hgap
        omega
      have himageCard : (laterCuts.image (· + 1)).card = laterCuts.card :=
        Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
      have hpartition : laterCuts.card + (cuts.filter fun gap => gap < site).card + 1 =
          cuts.card := by
        have hsiteCut := (hcuts site).mpr ⟨hs, hc⟩
        have hlow : (cuts.filter fun gap => ¬ site < gap) =
            insert site (cuts.filter fun gap => gap < site) := by
          ext gap
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hb⟩
            by_cases heq : gap = site
            · exact Or.inl heq
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hb⟩)
            · exact ⟨hsiteCut, by omega⟩
            · exact ⟨hg, by omega⟩
        have hsplit := Finset.card_filter_add_card_filter_not (s := cuts) (site < ·)
        rw [hlow, Finset.card_insert_of_notMem (by simp)] at hsplit
        exact hsplit
      by_cases hz : site = 0
      · have hnoMaximum : n ∉ p.take site := by simp [hz]
        have hdecomp : childCuts = {0} ∪ laterCuts.image (· + 1) := by
          ext gap
          constructor
          · intro hg
            obtain ⟨hb, ha⟩ := (hchildren gap).mp hg
            by_cases hgap : gap = 0
            · simp [hgap]
            by_cases hone : gap = site + 1
            · subst gap
              exact (hnoMaximum (hupdates.2.1.mp ha)).elim
            have hprev : site < gap - 1 := by omega
            have hprevBound : gap - 1 ≤ p.length := by omega
            have hprevActive := (hupdates.2.2 (gap - 1) hprev hprevBound).mp
              (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using ha)
            apply Finset.mem_union_right
            exact (himage gap).mpr ⟨gap - 1,
              (hcuts _).mpr ⟨hprevBound, hprevActive⟩, hprev, by omega⟩
          · intro hg
            rcases Finset.mem_union.mp hg with hfrontGap | him
            · have heq := Finset.mem_singleton.mp hfrontGap
              simpa only [heq] using hchildZero
            · obtain ⟨old, hold, hafter, rfl⟩ := (himage gap).mp him
              obtain ⟨hb, ha⟩ := (hcuts old).mp hold
              exact (hchildren _).mpr ⟨by omega, (hupdates.2.2 old hafter hb).mpr ha⟩
        have hparentDecomp : cuts = insert 0 laterCuts := by
          ext gap
          simp only [Finset.mem_insert, laterCuts, Finset.mem_filter]
          constructor
          · intro hg
            by_cases hgap : gap = 0
            · exact Or.inl hgap
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, _⟩)
            · exact hzero
            · exact hg
        have hnot : 0 ∉ laterCuts := by simp [laterCuts, hz]
        change childCuts.card = _
        rw [if_pos hz, hdecomp, Finset.card_union_of_disjoint hdisjoint,
          Finset.card_singleton, himageCard, hparentDecomp, Finset.card_insert_of_notMem hnot]
        omega
      · obtain ⟨hindec, hproper⟩ := hwhich.resolve_left hz
        have hmaximum : n ∈ p.take site := by
          have hsum := interval_sum_sites 0 n [] p hn (by simp) hp
            (by simpa [directSum, shift] using hp)
          exact hsum.2.2.1 hindec site (by omega) hs hc
        have hnoBefore (gap : ℕ) (hpositive : 0 < gap) (hb : gap ≤ site) :
            gap ∉ childCuts := by
          intro hg
          have ha := (hchildren gap).mp hg |>.2
          have hsep := (hupdates.1 gap hb).mp ha
          obtain ⟨before, later, hbad⟩ := hindec ⟨gap, by omega⟩ hpositive
          have hbefore : (p.take gap).get before ∈ p.take gap := List.get_mem _ _
          have hlater : (p.drop gap).get later ∈ p.drop gap := List.get_mem _ _
          exact (not_lt_of_ge hbad) (hsep _ hbefore _ hlater)
        have hmiddle : site + 1 ∈ childCuts :=
          (hchildren _).mpr ⟨by omega, hupdates.2.1.mpr hmaximum⟩
        have hdecomp : childCuts = {0, site + 1} ∪ laterCuts.image (· + 1) := by
          ext gap
          constructor
          · intro hg
            obtain ⟨hb, ha⟩ := (hchildren gap).mp hg
            by_cases hgap : gap = 0 ∨ gap = site + 1
            · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inl hgap
            have hafter : site + 1 < gap := by
              by_contra hnot
              apply hnoBefore gap (by omega) (by omega) hg
            have hprevBound : gap - 1 ≤ p.length := by omega
            have hprevActive := (hupdates.2.2 (gap - 1) (by omega) hprevBound).mp
              (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using ha)
            apply Finset.mem_union_right
            exact (himage gap).mpr ⟨gap - 1,
              (hcuts _).mpr ⟨hprevBound, hprevActive⟩, by omega, by omega⟩
          · intro hg
            rcases Finset.mem_union.mp hg with hspecial | him
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hspecial
              rcases hspecial with rfl | rfl
              · exact hchildZero
              · exact hmiddle
            · obtain ⟨old, hold, hafter, rfl⟩ := (himage gap).mp him
              obtain ⟨hb, ha⟩ := (hcuts old).mp hold
              exact (hchildren _).mpr ⟨by omega, (hupdates.2.2 old hafter hb).mpr ha⟩
        have hdisjointPair : Disjoint ({0, site + 1} : Finset ℕ)
            (laterCuts.image (· + 1)) := by
          apply Finset.disjoint_left.mpr
          intro gap hgap him
          obtain ⟨old, _, hafter, heq⟩ := (himage gap).mp him
          simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
          omega
        change childCuts.card = _
        rw [if_neg hz, hdecomp, Finset.card_union_of_disjoint hdisjointPair,
          himageCard, Finset.card_pair (by omega : 0 ≠ site + 1)]
        omega
  refine ⟨hstructure, ?_⟩
  intro hn
  dsimp only
  let active (size : ℕ) (word : List ℕ) := (Finset.range (word.length + 1)).filter
    fun gap => word.insertIdx gap (size + 1) ∈
      avoiders (size + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]
  let parents : Set (List ℕ) :=
    {word | word ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧ sumIndecomposable word}
  let choices := Σ parent : parents, Fin ((active n parent.val).card - 2)
  let domain : Set (List ℕ × ℕ) := {entry |
    entry.1 ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
      (entry.2 = 0 ∨ sumIndecomposable entry.1 ∧ entry.2 < entry.1.length ∧
        entry.1.insertIdx entry.2 (n + 1) ∈
          avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])}
  let pick (parent : parents) : Fin ((active n parent.val).card - 2) ≃
      {gap : ℕ // gap ∈ active n parent.val ∧ 0 < gap ∧ gap < parent.val.length} :=
    Classical.choose (hstructure.2.2 parent.val parent.property.1 hn)
  have hpick (parent : parents) (index : Fin ((active n parent.val).card - 2)) :
      ((active n parent.val).filter fun gap => gap < (pick parent index).val).card =
        index.val + 1 := Classical.choose_spec
      (hstructure.2.2 parent.val parent.property.1 hn) index
  let raw : (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] ⊕ choices) → domain
    | Sum.inl parent => ⟨(parent.val, 0), parent.property, Or.inl rfl⟩
    | Sum.inr ⟨parent, index⟩ =>
      ⟨(parent.val, (pick parent index).val), parent.property.1,
        Or.inr ⟨parent.property.2, (pick parent index).property.2.2,
          (Finset.mem_filter.mp (pick parent index).property.1).2⟩⟩
  have hrawInjective : Function.Injective raw := by
    intro left right heq
    have hvalues := congrArg Subtype.val heq
    cases left with
    | inl left =>
      cases right with
      | inl right =>
        exact congrArg Sum.inl (Subtype.ext (congrArg Prod.fst hvalues))
      | inr right =>
        have hsite := congrArg Prod.snd hvalues
        have hpositive := (pick right.1 right.2).property.2.1
        change 0 = (pick right.1 right.2).val at hsite
        omega
    | inr left =>
      cases right with
      | inl right =>
        have hsite := congrArg Prod.snd hvalues
        have hpositive := (pick left.1 left.2).property.2.1
        change (pick left.1 left.2).val = 0 at hsite
        omega
      | inr right =>
        have hparent : left.1 = right.1 :=
          Subtype.ext (congrArg Prod.fst hvalues)
        rcases left with ⟨lp, li⟩
        rcases right with ⟨rp, ri⟩
        dsimp at hparent
        subst rp
        have hindex : li = ri :=
          (pick lp).injective (Subtype.ext (congrArg Prod.snd hvalues))
        subst ri
        rfl
  have hrawSurjective : Function.Surjective raw := by
    intro entry
    by_cases hz : entry.val.2 = 0
    · refine ⟨Sum.inl ⟨entry.val.1, entry.property.1⟩, Subtype.ext ?_⟩
      exact Prod.ext rfl hz.symm
    · obtain ⟨hindec, hbound, hchild⟩ := entry.property.2.resolve_left hz
      let parent : parents := ⟨entry.val.1, entry.property.1, hindec⟩
      let gap : {gap : ℕ // gap ∈ active n parent.val ∧
          0 < gap ∧ gap < parent.val.length} := ⟨entry.val.2,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          change entry.val.2 < entry.val.1.length + 1
          omega), hchild⟩,
        by omega, hbound⟩
      refine ⟨Sum.inr ⟨parent, (pick parent).symm gap⟩, Subtype.ext ?_⟩
      change (parent.val, (pick parent ((pick parent).symm gap)).val) = entry.val
      exact Prod.ext rfl (congrArg Subtype.val ((pick parent).apply_symm_apply gap))
  let construction := (Equiv.ofBijective raw ⟨hrawInjective, hrawSurjective⟩).trans
    hstructure.1.equiv
  have hfrontLabels (parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]) :
      (active (n + 1) (construction (Sum.inl parent)).val).card =
        (active n parent.val).card := by
    change (active (n + 1) (parent.val.insertIdx 0 (n + 1))).card =
      (active n parent.val).card
    have hformula := hstructure.2.1 parent.val parent.property hn 0 (Nat.zero_le _)
      (hfront parent.val parent.property) (Or.inl rfl)
    simpa only [if_pos rfl, ite_true] using hformula
  have hinternalLabels (parent : parents) (index : Fin ((active n parent.val).card - 2)) :
      (active (n + 1) (construction (Sum.inr ⟨parent, index⟩)).val).card =
        (active n parent.val).card - index.val := by
    let gap := (pick parent index).val
    have hb : gap ≤ parent.val.length := Nat.le_of_lt (pick parent index).property.2.2
    have ha := (Finset.mem_filter.mp (pick parent index).property.1).2
    have hformula := hstructure.2.1 parent.val parent.property.1 hn gap hb ha
      (Or.inr ⟨parent.property.2, (pick parent index).property.2.2⟩)
    have hz : gap ≠ 0 := by have := (pick parent index).property.2.1; omega
    have hrank := hpick parent index
    change (active (n + 1) (parent.val.insertIdx gap (n + 1))).card =
      (active n parent.val).card - index.val
    change (active (n + 1) (parent.val.insertIdx gap (n + 1))).card =
      if gap = 0 then (active n parent.val).card else
        (active n parent.val).card + 1 -
          ((active n parent.val).filter fun site => site < gap).card at hformula
    rw [if_neg hz, hrank] at hformula
    omega
  have hfinite : (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  let : Finite (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]) := hfinite.to_subtype
  let : Finite parents := (hfinite.subset (fun _ hw => hw.1)).to_subtype
  refine ⟨construction, hfrontLabels, hinternalLabels, ?_, ?_, ?_⟩
  · have hcard := Nat.card_congr construction
    rw [Nat.card_sum, Nat.card_coe_set_eq] at hcard
    exact hcard.symm
  · intro label
    have hinternalAll (entry : choices) :
        (active (n + 1) (construction (Sum.inr entry)).val).card =
          (active n entry.1.val).card - entry.2.val := hinternalLabels entry.1 entry.2
    let labelled := construction.subtypeEquivOfSubtype
      (p := fun child => (active (n + 1) child.val).card = label + 2)
    have hcard := Nat.card_congr (labelled.symm.trans Equiv.subtypeSum)
    let forget : {entry : choices //
        (active n entry.1.val).card - entry.2.val = label + 2} →
        {parent : parents // 0 < label ∧ label + 2 ≤ (active n parent.val).card} :=
      fun entry => ⟨entry.val.1, by
        have hi := entry.val.2.isLt
        have hl := entry.property
        omega⟩
    have hforgetInjective : Function.Injective forget := by
      intro left right heq
      have hparent := congrArg Subtype.val heq
      rcases left with ⟨⟨lp, li⟩, hl⟩
      rcases right with ⟨⟨rp, ri⟩, hr⟩
      change lp = rp at hparent
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
      intro parent
      let rank : Fin ((active n parent.val.val).card - 2) :=
        ⟨(active n parent.val.val).card - (label + 2), by
          have hp := parent.property
          omega⟩
      refine ⟨⟨⟨parent.val, rank⟩, ?_⟩, Subtype.ext rfl⟩
      change (active n parent.val.val).card - rank.val = label + 2
      dsimp only [rank]
      have hp := parent.property
      omega
    change Nat.card {child : {word : List ℕ |
        word ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
          sumIndecomposable word} // (active (n + 1) child.val).card = label + 2} =
      Nat.card {parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]] //
        (active n parent.val).card = label + 2} +
      Nat.card {parent : parents // 0 < label ∧ label + 2 ≤ (active n parent.val).card}
    simp only [Nat.card_sum, hfrontLabels, hinternalAll] at hcard
    rw [Nat.card_congr (Equiv.ofBijective forget
      ⟨hforgetInjective, hforgetSurjective⟩)] at hcard
    exact hcard
  · have hweighted (weight : ℕ → Polynomial ℚ) :
        (∑ᶠ child : {word : List ℕ |
          word ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ∧
            sumIndecomposable word}, weight ((active (n + 1) child.val).card - 2)) =
          (∑ᶠ parent : avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]],
            weight ((active n parent.val).card - 2)) +
          ∑ᶠ parent : parents, ∑ᶠ index : Fin ((active n parent.val).card - 2),
            weight ((active n parent.val).card - index.val - 2) := by
      let : Fintype (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]) := Fintype.ofFinite _
      let : Fintype parents := Fintype.ofFinite _
      rw [← finsum_comp_equiv construction]
      simp only [finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro parent _
        exact congrArg (fun count => weight (count - 2)) (hfrontLabels parent)
      · rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro parent _
        apply Finset.sum_congr rfl
        intro index _
        exact congrArg (fun count => weight (count - 2)) (hinternalLabels parent index)
    refine ⟨hweighted, ?_⟩
    let : Fintype (avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]]) := Fintype.ofFinite _
    let : Fintype parents := Fintype.ofFinite _
    constructor
    · simp only [finsum_eq_sum_of_fintype]
      rw [Finset.mul_sum]
      simp only [mul_neg_geom_sum,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, map_natCast]
    · rw [hweighted (fun label => (Polynomial.X : Polynomial ℚ) ^ label)]
      congr 1
      rw [mul_finsum]
      simp only [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro parent _
      rw [Fin.sum_univ_eq_sum_range (fun index =>
        (Polynomial.X : Polynomial ℚ) ^ ((active n parent.val).card - index - 2))]
      calc
        (∑ index ∈ Finset.range ((active n parent.val).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ ((active n parent.val).card - index - 2)) =
            ∑ index ∈ Finset.range ((active n parent.val).card - 2),
              (Polynomial.X : Polynomial ℚ) ^
                (((active n parent.val).card - 2) - 1 - index + 1) := by
          apply Finset.sum_congr rfl
          intro index hi
          have := Finset.mem_range.mp hi
          congr 1
          omega
        _ = ∑ index ∈ Finset.range ((active n parent.val).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ (index + 1) :=
          Finset.sum_range_reflect (fun index => (Polynomial.X : Polynomial ℚ) ^ (index + 1))
            ((active n parent.val).card - 2)
        _ = Polynomial.X * ∑ index ∈ Finset.range ((active n parent.val).card - 2),
            (Polynomial.X : Polynomial ℚ) ^ index := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index _
          rw [pow_succ, mul_comm]

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenAConstruction
