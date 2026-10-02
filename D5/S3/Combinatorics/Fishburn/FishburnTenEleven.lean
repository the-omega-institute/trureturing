/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenEleven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenEleven
   mirror-E: none(waiver:classical-fishburn-counting-equality)
   anchors: [mathlib/module/Mathlib.Data.Finset.Prod]
   utility: none
   digest: Reversible maximum insertion proves Egge's Fishburn versus classical equality. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenElevenRecovery
import D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalConstruction
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenEleven

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnClassicalDefs
open FishburnBasicInsertion FishburnTenElevenSites FishburnTenElevenFamily
open FishburnTenElevenRecovery FishburnTenElevenClassicalSites
open FishburnTenElevenClassicalPairs FishburnTenElevenClassicalConstruction

set_option maxHeartbeats 4000000 in
theorem result : FishburnClassicalDefs.claim1011 := by
  classical
  have hmaximum (n : ℕ) (patterns : List (List ℕ)) :
      Function.Bijective (fun entry : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n patterns ∧ entry.2 ≤ entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns} =>
        (⟨entry.val.1.insertIdx entry.val.2 (n + 1), entry.property.2.2⟩ :
          avoiders (n + 1) patterns)) := by
    constructor
    · intro first second heq
      have hchild : first.val.1.insertIdx first.val.2 (n + 1) =
          second.val.1.insertIdx second.val.2 (n + 1) := congrArg Subtype.val heq
      have hfirstlen : (first.val.1.insertIdx first.val.2 (n + 1)).length =
          first.val.1.length + 1 :=
        List.length_insertIdx_of_le_length first.property.2.1 _
      have hsecondlen : (second.val.1.insertIdx second.val.2 (n + 1)).length =
          second.val.1.length + 1 :=
        List.length_insertIdx_of_le_length second.property.2.1 _
      have hfirstbound : first.val.2 <
          (first.val.1.insertIdx first.val.2 (n + 1)).length := by omega
      have hsecondbound : second.val.2 <
          (first.val.1.insertIdx first.val.2 (n + 1)).length := by rw [hchild]; omega
      have hfirstat : (first.val.1.insertIdx first.val.2 (n + 1)).getD first.val.2 0 =
          n + 1 := by
        rw [List.getD_eq_getElem _ 0 hfirstbound]
        exact List.getElem_insertIdx_self _
      have hsecondat : (first.val.1.insertIdx first.val.2 (n + 1)).getD second.val.2 0 =
          n + 1 := by
        rw [hchild, List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_insertIdx_self _
      have hnodup : (first.val.1.insertIdx first.val.2 (n + 1)).Nodup :=
        first.property.2.2.1.nodup_iff.mpr (List.nodup_range' 1)
      have hsites : first.val.2 = second.val.2 :=
        (List.getD_inj hfirstbound hsecondbound hnodup).mp (hfirstat.trans hsecondat.symm)
      have hparents : first.val.1 = second.val.1 := by
        rw [hsites] at hchild
        exact List.insertIdx_injective _ _ hchild
      apply Subtype.ext
      exact Prod.ext hparents hsites
    · intro child
      have hlen : child.val.length = n + 1 := by
        simpa only [List.length_range'] using child.property.1.length_eq
      have hmaxmem : n + 1 ∈ child.val := by
        apply child.property.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n, by omega, by omega⟩
      obtain ⟨site, hsitechild, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
      let parent := child.val.eraseIdx site
      have hinverse : parent.insertIdx site (n + 1) = child.val := by
        simpa only [parent, hvalue] using List.insertIdx_eraseIdx_getElem hsitechild
      have hparentlen : parent.length = n := by
        simp only [parent, List.length_eraseIdx_of_lt hsitechild, hlen]
        omega
      have hsite : site ≤ parent.length := by omega
      have hparentperm : parent.Perm (List.range' 1 n) := by
        have hcons : ((n + 1) :: parent).Perm child.val := by
          simpa only [parent, hvalue] using List.getElem_cons_eraseIdx_perm hsitechild
        have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
          rw [List.range'_concat]
          simpa only [Nat.add_comm, Nat.one_mul, List.singleton_append] using
            (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
        exact (hcons.trans (child.property.1.trans hrange)).cons_inv
      have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
        intro value hvalue
        have hm := hparentperm.mem_iff.mp hvalue
        simp only [List.mem_range', Nat.one_mul] at hm
        obtain ⟨offset, hoffset, heq⟩ := hm
        omega
      have hparentmember : parent ∈ avoiders n patterns := by
        refine ⟨hparentperm, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
            (by rw [hinverse]; exact child.property.2.1) |>.1
        · intro pattern hpattern hocc
          obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
          apply child.property.2.2 pattern hpattern
          refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child.val site),
            by simp⟩
          intro rank hlow hhigh
          exact (List.eraseIdx_sublist child.val site).subset (hmem rank hlow hhigh)
      refine ⟨⟨(parent, site), hparentmember, hsite, ?_⟩, ?_⟩
      · rw [hinverse]
        exact child.property
      · exact Subtype.ext hinverse
  have hfishburn (n : ℕ) (hn : 1 ≤ n) :
      (avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]]).ncard =
        2 * (avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]]).ncard +
          {pair : ℕ × ℕ | 1 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n}.ncard := by
    classical
    let parents := avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]]
    let pairs : Set (ℕ × ℕ) := {pair | 1 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n}
    let active : Set (List ℕ × ℕ) := {entry | entry.1 ∈ parents ∧
      entry.2 ≤ entry.1.length ∧
        entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]]}
    let front := (fun p : List ℕ => (p, 0)) '' parents
    let middle := (fun p : List ℕ => (p, p.idxOf 1 + 1)) '' parents
    let extra := (fun pair : ℕ × ℕ => (pairPermutation n pair.2 (pair.1 + 1), n)) '' pairs
    have hlen (p : List ℕ) (hp : p ∈ parents) : p.length = n := by
      simpa using hp.1.length_eq
    have hnodup (p : List ℕ) (hp : p ∈ parents) : p.Nodup :=
      hp.1.nodup_iff.mpr (List.nodup_range' 1)
    have honemem (p : List ℕ) (hp : p ∈ parents) : 1 ∈ p := by
      apply hp.1.mem_iff.mpr
      simp only [List.mem_range'_1]
      omega
    have hone (p : List ℕ) (hp : p ∈ parents) :
        p.idxOf 1 < p.length ∧ p.getD (p.idxOf 1) 0 = 1 := by
      have hi := List.idxOf_lt_length_iff.mpr (honemem p hp)
      refine ⟨hi, ?_⟩
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_idxOf hi
    have hpair (pair : ℕ × ℕ) (hp : pair ∈ pairs) :
        pairPermutation n pair.2 (pair.1 + 1) ∈ parents ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] (pairPermutation n pair.2 (pair.1 + 1)) ∧
        (pairPermutation n pair.2 (pair.1 + 1)).getD (n - 1) 0 ≠ 1 :=
      pair_construction n pair.2 (pair.1 + 1) (by exact Nat.succ_le_succ hp.1)
        (by have hh := hp.2.1; omega) hp.2.2
    have hdecode (pair : ℕ × ℕ) (hp : pair ∈ pairs) :
        (pairPermutation n pair.2 (pair.1 + 1)).idxOf 1 = n - pair.2 ∧
        (pairPermutation n pair.2 (pair.1 + 1)).getLast? = some (pair.1 + 1) := by
      have hnot : 1 ∉ (List.range' (pair.2 + 1) (n - pair.2)).reverse := by
        simp only [List.mem_reverse, List.mem_range', Nat.one_mul]
        rintro ⟨offset, _, he⟩
        have hh := hp.2.1
        omega
      constructor
      · simp [pairPermutation, List.idxOf_append_of_notMem hnot]
      · have htail : List.range' 2 pair.1 =
            List.range' 2 (pair.1 - 1) ++ [pair.1 + 1] := by
          have hh : pair.1 = pair.1 - 1 + 1 := by have hh := hp.1; omega
          conv_lhs => rw [hh]
          rw [List.range'_concat]
          congr 1
          congr 1
          omega
        simp only [pairPermutation, Nat.add_sub_cancel, htail, ← List.append_assoc]
        exact List.getLast?_concat
    have hclass : active = (front ∪ middle) ∪ extra := by
      apply Set.Subset.antisymm
      · rintro ⟨p, site⟩ ⟨hp, hs, hc⟩
        obtain hzero | honeSite | hend := (fishburn_active_sites n p hp site hs).mp hc
        · subst site
          exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
        · obtain ⟨one, ho, hv, he⟩ := honeSite
          have hi : one = p.idxOf 1 := by
            apply (List.getD_inj ho (hone p hp).1 (hnodup p hp)).mp
            exact hv.trans (hone p hp).2.symm
          exact Or.inl (Or.inr ⟨p, hp, by simp [he, hi]⟩)
        · obtain ⟨he, ha⟩ := hend
          by_cases hl : p.getD (n - 1) 0 = 1
          · have hi : n - 1 = p.idxOf 1 := by
              apply (List.getD_inj (by rw [hlen p hp]; omega)
                (hone p hp).1 (hnodup p hp)).mp
              exact hl.trans (hone p hp).2.symm
            exact Or.inl (Or.inr ⟨p, hp, by
              apply Prod.ext
              · rfl
              dsimp
              rw [he, hlen p hp]
              omega⟩)
          · obtain ⟨upper, lower, hb, hba, han, heq⟩ := pair_recovery n p hp hn ha hl
            exact Or.inr ⟨(lower - 1, upper), ⟨by omega, by omega, han⟩, by
              apply Prod.ext
              · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ lower)] using heq.symm
              · exact (he.trans (hlen p hp)).symm⟩
      · rintro entry ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨pair, hp, rfl⟩)
        · change p ∈ parents ∧ 0 ≤ p.length ∧ _
          refine ⟨hp, by omega, ?_⟩
          exact (fishburn_active_sites n p hp 0 (by omega)).mpr (Or.inl rfl)
        · have ho := hone p hp
          change p ∈ parents ∧ p.idxOf 1 + 1 ≤ p.length ∧ _
          refine ⟨hp, by omega, ?_⟩
          exact (fishburn_active_sites n p hp (p.idxOf 1 + 1) (by omega)).mpr
            (Or.inr (Or.inl ⟨p.idxOf 1, ho.1, ho.2, rfl⟩))
        · obtain ⟨hpar, hav, _⟩ := hpair pair hp
          have hl := hlen _ hpar
          change pairPermutation n pair.2 (pair.1 + 1) ∈ parents ∧
            n ≤ (pairPermutation n pair.2 (pair.1 + 1)).length ∧ _
          refine ⟨hpar, by omega, ?_⟩
          exact (fishburn_active_sites n _ hpar n (by omega)).mpr
            (Or.inr (Or.inr ⟨hl.symm, hav⟩))
    have hfm : Disjoint front middle := by
      apply Set.disjoint_left.mpr
      rintro entry ⟨p, _, he⟩ ⟨q, _, hq⟩
      have hh := congrArg Prod.snd (he.trans hq.symm)
      dsimp at hh
      omega
    have hex : Disjoint (front ∪ middle) extra := by
      apply Set.disjoint_left.mpr
      rintro entry (⟨p, _, he⟩ | ⟨p, hp, he⟩) ⟨pair, hpairmem, heq⟩
      · have hh := congrArg Prod.snd (he.trans heq.symm)
        dsimp at hh
        omega
      · have hh := he.trans heq.symm
        have hparent := congrArg Prod.fst hh
        have hsite := congrArg Prod.snd hh
        dsimp at hparent hsite
        have honeval := (hone p hp).2
        have hi : p.idxOf 1 = n - 1 := by omega
        rw [hi, hparent] at honeval
        exact (hpair pair hpairmem).2.2 honeval
    have hfinite : parents.Finite := by
      apply (List.finite_toSet (List.range' 1 n).permutations).subset
      intro p hp
      exact List.mem_permutations.mpr hp.1
    have hpfinite : pairs.Finite := by
      apply ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).finite_toSet).subset
      intro pair hp
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      have hh := hp.2.1
      have hb := hp.2.2
      exact ⟨by omega, by omega⟩
    have hfrontcard : front.ncard = parents.ncard :=
      Set.ncard_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)
    have hmiddlecard : middle.ncard = parents.ncard :=
      Set.ncard_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)
    have hextracard : extra.ncard = pairs.ncard := by
      apply Set.InjOn.ncard_image
      intro first hf second hs he
      have hp := congrArg Prod.fst he
      dsimp at hp
      have ha := congrArg (fun p : List ℕ => p.idxOf 1) hp
      rw [(hdecode first hf).1, (hdecode second hs).1] at ha
      have hb := congrArg List.getLast? hp
      rw [(hdecode first hf).2, (hdecode second hs).2] at hb
      apply Prod.ext
      · have hh := Option.some.inj hb
        omega
      · have hfbound := hf.2.2
        have hsbound := hs.2.2
        omega
    have hchildren : active.ncard =
        (avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]]).ncard := by
      let insertion : List ℕ × ℕ → List ℕ := fun entry =>
        entry.1.insertIdx entry.2 (n + 1)
      have himage : insertion '' active =
          avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]] := by
        apply Set.Subset.antisymm
        · rintro p ⟨entry, he, rfl⟩
          exact he.2.2
        · intro p hp
          obtain ⟨entry, he⟩ := (hmaximum n
            [[1, 2, 4, 3], [2, 1, 3, 4]]).2 ⟨p, hp⟩
          exact ⟨entry.val, entry.property, congrArg Subtype.val he⟩
      have hinj : Set.InjOn insertion active := by
        intro first hf second hs he
        have hh := (hmaximum n [[1, 2, 4, 3], [2, 1, 3, 4]]).1
          (a₁ := ⟨first, hf⟩) (a₂ := ⟨second, hs⟩) (Subtype.ext he)
        exact congrArg Subtype.val hh
      rw [← himage, hinj.ncard_image]
    rw [← hchildren, hclass, Set.ncard_union_eq hex
      ((hfinite.image _).union (hfinite.image _)) (hpfinite.image _),
      Set.ncard_union_eq hfm (hfinite.image _) (hfinite.image _),
      hfrontcard, hmiddlecard, hextracard]
    change parents.ncard + parents.ncard + pairs.ncard = 2 * parents.ncard + pairs.ncard
    omega
  have hclassical (n : ℕ) (hn : 1 ≤ n) :
      (classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]]).ncard =
        2 * (classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]]).ncard +
          {pair : ℕ × ℕ | 1 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n}.ncard := by
    let parents := classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]]
    let pairs : Set (ℕ × ℕ) := {pair | 1 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n}
    let active : Set (List ℕ × ℕ) := {entry | entry.1 ∈ parents ∧
      entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
        classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]]}
    let template : ℕ × ℕ → List ℕ := fun pair =>
      pair.2 :: (List.range' 1 pair.1).reverse ++
        ((List.range' (pair.1 + 1) (n - pair.1)).reverse).erase pair.2
    let front := (fun p : List ℕ => (p, 0)) '' parents
    let middle := (fun p : List ℕ => (p, 1)) '' parents
    let extra := (fun pair : ℕ × ℕ => (template pair, pair.1 + 1)) '' pairs
    have hlen (p : List ℕ) (hp : p ∈ parents) : p.length = n := by
      simpa using hp.1.length_eq
    have hpair (pair : ℕ × ℕ) (hp : pair ∈ pairs) :
        template pair ∈ parents ∧ (template pair).insertIdx (pair.1 + 1) (n + 1) ∈
          classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]] :=
      exceptional_pair_construction n pair.1 pair.2 hp.1 hp.2.1 hp.2.2
    have hdecode (pair : ℕ × ℕ) (hp : pair ∈ pairs) :
        (template pair).getD 0 0 = pair.2 ∧ (template pair).getD 1 0 = pair.1 := by
      have hseq : (List.range' 1 pair.1).reverse =
          pair.1 :: (List.range' 1 (pair.1 - 1)).reverse := by
        have hh : pair.1 = pair.1 - 1 + 1 := by have hh := hp.1; omega
        conv_lhs => rw [hh]
        rw [List.range'_concat, List.reverse_append]
        simp only [List.reverse_singleton, List.singleton_append]
        congr 1
        omega
      simp [template, hseq]
    have hclass : active = (front ∪ middle) ∪ extra := by
      apply Set.Subset.antisymm
      · rintro ⟨p, site⟩ ⟨hp, hs, hc⟩
        by_cases hz : site = 0
        · subst site
          exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
        by_cases ho : site = 1
        · subst site
          exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
        obtain ⟨hm, hmk, hk, hsite, he⟩ :=
          exceptional_pair_recovery n p hp site hs (by omega) hc
        exact Or.inr ⟨(p.getD 1 0, p.getD 0 0), ⟨hm, hmk, hk⟩, by
          apply Prod.ext
          · exact he.symm
          · exact hsite.symm⟩
      · rintro entry ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨pair, hp, rfl⟩)
        · change p ∈ parents ∧ 0 ≤ p.length ∧ _
          refine ⟨hp, by omega, ?_⟩
          exact (classical_active_sites n p hp 0 (by omega)).mpr (Or.inl (by omega))
        · have hl := hlen p hp
          change p ∈ parents ∧ 1 ≤ p.length ∧ _
          refine ⟨hp, by omega, ?_⟩
          exact (classical_active_sites n p hp 1 (by omega)).mpr (Or.inl (by omega))
        · obtain ⟨hpar, hc⟩ := hpair pair hp
          change template pair ∈ parents ∧ pair.1 + 1 ≤ (template pair).length ∧ _
          have hl := hlen _ hpar
          have hh := hp.2.1
          have hb := hp.2.2
          exact ⟨hpar, by omega, hc⟩
    have hfm : Disjoint front middle := by
      apply Set.disjoint_left.mpr
      rintro entry ⟨p, _, he⟩ ⟨q, _, hq⟩
      have hh := congrArg Prod.snd (he.trans hq.symm)
      exact Nat.zero_ne_one hh
    have hex : Disjoint (front ∪ middle) extra := by
      apply Set.disjoint_left.mpr
      rintro entry (⟨p, _, he⟩ | ⟨p, _, he⟩) ⟨pair, hp, heq⟩
      · have hh := congrArg Prod.snd (he.trans heq.symm)
        dsimp at hh
        omega
      · have hh := congrArg Prod.snd (he.trans heq.symm)
        dsimp at hh
        have hb := hp.1
        omega
    have hfinite : parents.Finite := by
      apply (List.finite_toSet (List.range' 1 n).permutations).subset
      intro p hp
      exact List.mem_permutations.mpr hp.1
    have hpfinite : pairs.Finite := by
      apply ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).finite_toSet).subset
      intro pair hp
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      have hh := hp.2.1
      have hb := hp.2.2
      exact ⟨by omega, by omega⟩
    have hfrontcard : front.ncard = parents.ncard :=
      Set.ncard_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)
    have hmiddlecard : middle.ncard = parents.ncard :=
      Set.ncard_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)
    have hextracard : extra.ncard = pairs.ncard := by
      apply Set.InjOn.ncard_image
      intro first hf second hs he
      have hp := congrArg Prod.fst he
      dsimp at hp
      have ha := congrArg (fun p : List ℕ => p.getD 1 0) hp
      have hb := congrArg (fun p : List ℕ => p.getD 0 0) hp
      rw [(hdecode first hf).2, (hdecode second hs).2] at ha
      rw [(hdecode first hf).1, (hdecode second hs).1] at hb
      exact Prod.ext ha hb
    have hchildren : active.ncard =
        (classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]]).ncard := by
      apply Set.ncard_congr (fun entry _ => entry.1.insertIdx entry.2 (n + 1))
      · intro entry he
        exact he.2.2
      · intro first second hf hs he
        have hfirstlen : (first.1.insertIdx first.2 (n + 1)).length =
            first.1.length + 1 := List.length_insertIdx_of_le_length hf.2.1 _
        have hsecondlen : (second.1.insertIdx second.2 (n + 1)).length =
            second.1.length + 1 := List.length_insertIdx_of_le_length hs.2.1 _
        have hfirstbound : first.2 < (first.1.insertIdx first.2 (n + 1)).length :=
          by have hh := hf.2.1; omega
        have hsecondbound : second.2 < (first.1.insertIdx first.2 (n + 1)).length := by
          rw [he]
          have hh := hs.2.1
          omega
        have hfirstat : (first.1.insertIdx first.2 (n + 1)).getD first.2 0 = n + 1 := by
          rw [List.getD_eq_getElem _ 0 hfirstbound]
          exact List.getElem_insertIdx_self _
        have hsecondat : (first.1.insertIdx first.2 (n + 1)).getD second.2 0 = n + 1 := by
          rw [he, List.getD_eq_getElem _ 0 (by have hh := hs.2.1; omega)]
          exact List.getElem_insertIdx_self _
        have hnodup : (first.1.insertIdx first.2 (n + 1)).Nodup :=
          hf.2.2.1.nodup_iff.mpr (List.nodup_range' 1)
        have hsites : first.2 = second.2 :=
          (List.getD_inj hfirstbound hsecondbound hnodup).mp
            (hfirstat.trans hsecondat.symm)
        apply Prod.ext
        · rw [hsites] at he
          exact List.insertIdx_injective _ _ he
        · exact hsites
      · intro child hc
        have hl : child.length = n + 1 := by simpa using hc.1.length_eq
        have hm : n + 1 ∈ child := by
          apply hc.1.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n, by omega, by omega⟩
        obtain ⟨site, hs, hv⟩ := List.mem_iff_getElem.mp hm
        let parent := child.eraseIdx site
        have hinverse : parent.insertIdx site (n + 1) = child := by
          simpa only [parent, hv] using List.insertIdx_eraseIdx_getElem hs
        have hparentlen : parent.length = n := by
          simp only [parent, List.length_eraseIdx_of_lt hs, hl]
          omega
        have hparentperm : parent.Perm (List.range' 1 n) := by
          have hcons : ((n + 1) :: parent).Perm child := by
            simpa only [parent, hv] using List.getElem_cons_eraseIdx_perm hs
          have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
            rw [List.range'_concat]
            simpa only [Nat.add_comm, Nat.one_mul, List.singleton_append] using
              (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
          exact (hcons.trans (hc.1.trans hrange)).cons_inv
        have hparent : parent ∈ parents := by
          refine ⟨hparentperm, ?_⟩
          intro pattern hp ho
          obtain ⟨values, hstep, hmem, hsub, hrel⟩ := ho
          apply hc.2 pattern hp
          refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child site),
            by simp⟩
          intro rank hlow hhigh
          exact (List.eraseIdx_sublist child site).subset (hmem rank hlow hhigh)
        refine ⟨(parent, site), ⟨hparent, ?_, ?_⟩, hinverse⟩
        · change site ≤ parent.length
          omega
        rw [hinverse]
        exact hc
    rw [← hchildren, hclass, Set.ncard_union_eq hex
      ((hfinite.image _).union (hfinite.image _)) (hpfinite.image _),
      Set.ncard_union_eq hfm (hfinite.image _) (hfinite.image _),
      hfrontcard, hmiddlecard, hextracard]
    change parents.ncard + parents.ncard + pairs.ncard =
      2 * parents.ncard + pairs.ncard
    omega
  have hsmall (n : ℕ) (hn : n ≤ 1) :
      avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]] =
        classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]] := by
    have havoid (p : List ℕ) (hp : p.Perm (List.range' 1 n))
        (pattern : List ℕ) (hh : 2 ≤ pattern.length) : ¬ NonnestingDefs.Occurs pattern p := by
      rintro ⟨values, _, _, hsub, _⟩
      have hl := hsub.length_le
      have hplen : p.length = n := by simpa using hp.length_eq
      simp only [List.length_map] at hl
      omega
    ext p
    constructor
    · intro hp
      refine ⟨hp.1, ?_⟩
      intro pattern hpat
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpat
      rcases hpat with rfl | rfl
      · exact havoid p hp.1 _ (by simp)
      · exact havoid p hp.1 _ (by simp)
    · intro hp
      refine ⟨hp.1, ?_, ?_⟩
      · intro before later hgap hlater
        have hl : p.length = n := by simpa using hp.1.length_eq
        omega
      · intro pattern hpat
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpat
        rcases hpat with rfl | rfl
        · exact havoid p hp.1 _ (by simp)
        · exact havoid p hp.1 _ (by simp)
  intro n
  induction n with
  | zero => rw [hsmall 0 (by omega)]
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      rw [hsmall 1 (by omega)]
    · rw [hfishburn n (by omega), hclassical n (by omega), ih]

end D5.S3.Combinatorics.Fishburn.FishburnTenEleven
