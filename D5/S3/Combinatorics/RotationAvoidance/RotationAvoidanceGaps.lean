/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGaps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGaps
   mirror-E: none(waiver:disjoint-contracted-circle-estimate)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Contracted families and endpoint estimates separate three one-bad-cut pairs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMarkedContraction
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixed
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmptyCount
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSlices
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceConsecutive
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingSplit
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingSplit
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescending
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEndpoints
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGaps

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
-- Rooting the disjoint contracted families and reindexing endpoint partitions need this budget.
theorem three_strict_count_gaps (size : ℕ) (hsize : 7 ≤ size) :
    (singleBadCircles size [2, 1, 4, 3]).ncard <
        (singleBadCircles size [1, 2, 3, 4]).ncard ∧
    (singleBadCircles size [1, 2, 3, 4]).ncard <
        (singleBadCircles size [1, 4, 3, 2]).ncard ∧
    (singleBadCircles size [1, 2, 4, 3]).ncard <
        (singleBadCircles size [1, 3, 4, 2]).ncard := by
  classical
  have sumSlices (q : List ℕ) (limit : ℕ)
      (endpoints : ∀ p : List ℕ,
        p.Perm (List.range' 1 size) ∧
          (∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0) →
        ∃ a b interior, p = a :: interior ++ [b] ∧ a < limit ∧ b < limit)
      (term : ℕ → ℕ → ℕ)
      (sliceCounts : ∀ a b : Fin limit,
        {p : List ℕ | (p.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0) ∧
          p.head? = some a.val ∧ p.getLast? = some b.val}.ncard = term a.val b.val) :
      (singleBadCircles size q).ncard =
        ∑ a ∈ Finset.range limit, ∑ b ∈ Finset.range limit, term a b := by
    let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
      ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
    have lengthEq (p : List ℕ) (hp : p.Perm (List.range' 1 size)) : p.length = size := by
      simpa using hp.length_eq
    have rotateSum (p : List ℕ) (hp : p.Perm (List.range' 1 size)) (a b : ℕ) :
        (p.rotate a).rotate b = p.rotate ((a + b) % size) := by
      rw [List.rotate_rotate, ← List.rotate_mod, lengthEq p hp]
    have shiftZero (a b : ℕ) (ha : a < size) (hb : b < size) :
        (a + b) % size = a ↔ b = 0 := by
      by_cases hs : a + b < size
      · rw [Nat.mod_eq_of_lt hs]; omega
      · have hh : size ≤ a + b := by omega
        rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega : a + b - size < size)]; omega
    let bad := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) =>
      Classical.choose hp.2.2
    have badSpec (p : List ℕ) (hp : p ∈ singleBadCircles size q) :
        bad p hp < size ∧ ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = bad p hp :=
      Classical.choose_spec hp.2.2
    let emit := fun (p : List ℕ) (hp : p ∈ singleBadCircles size q) => p.rotate (bad p hp)
    have emitMember (p : List ℕ) (hp : p ∈ singleBadCircles size q) : emit p hp ∈ words := by
      have hs := badSpec p hp; refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
      intro cut hc; change Occurs q ((p.rotate (bad p hp)).rotate cut) ↔ cut = 0
      rw [rotateSum p hp.1, hs.2 _ (Nat.mod_lt _ (by omega))]; exact shiftZero _ _ hs.1 hc
    have rootUnique (u v : List ℕ) (hu : u.Perm (List.range' 1 size))
        (headU : u.head? = some 1) (headV : v.head? = some 1)
        (hr : List.IsRotated u v) : u = v := by
      obtain ⟨cut, he⟩ := hr
      have hb : cut % u.length < u.length := by rw [lengthEq u hu]; exact Nat.mod_lt _ (by omega)
      have hz : 0 < u.length := by rw [lengthEq u hu]; omega
      have hg : u[cut % u.length]? = u[0]? := by
        rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?, headU, headV]
      rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz, Option.some.injEq] at hg
      have hzero := (hu.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hg
      rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he; exact he
    have emitInjective (u v : List ℕ) (hu : u ∈ singleBadCircles size q)
        (hv : v ∈ singleBadCircles size q) (he : emit u hu = emit v hv) : u = v := by
      apply rootUnique u v hu.1 hu.2.1 hv.2.1
      have hrU : List.IsRotated u (emit u hu) := (List.IsRotated.forall u (bad u hu)).symm
      have hrV : List.IsRotated (emit v hv) v := List.IsRotated.forall v (bad v hv)
      exact hrU.trans (he.symm ▸ hrV)
    have emitSurjective (p : List ℕ) (hp : p ∈ words) :
        ∃ (circle : List ℕ) (hc : circle ∈ singleBadCircles size q), emit circle hc = p := by
      have hm : 1 ∈ p := hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi : p.idxOf 1 < size := by
        have hh := List.idxOf_lt_length_iff.mpr hm; rw [lengthEq p hp.1] at hh; exact hh
      let root := p.rotate (p.idxOf 1)
      let back := (size - p.idxOf 1) % size
      have reverseRoot : root.rotate back = p := by
        rw [rotateSum p hp.1]; have he : (p.idxOf 1 + back) % size = 0 := by
          dsimp [back]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show p.idxOf 1 + (size - p.idxOf 1) = size by omega, Nat.mod_self]
        rw [he, List.rotate_zero]
      have rootMember : root ∈ singleBadCircles size q := by
        refine ⟨(List.rotate_perm _ _).trans hp.1, ?_, back, Nat.mod_lt _ (by omega), ?_⟩
        · rw [List.head?_rotate (by rwa [lengthEq p hp.1])]
          exact List.getElem?_idxOf hm
        · intro cut hc
          rw [rotateSum p hp.1, hp.2 _ (Nat.mod_lt _ (by omega))]
          change (p.idxOf 1 + cut) % size = 0 ↔ cut = (size - p.idxOf 1) % size
          by_cases hz : p.idxOf 1 = 0
          · simp [hz, Nat.mod_eq_of_lt hc]
          · have hb : size - p.idxOf 1 < size := by omega
            rw [Nat.mod_eq_of_lt hb]; by_cases hs : p.idxOf 1 + cut < size
            · rw [Nat.mod_eq_of_lt hs]; omega
            · rw [Nat.mod_eq_sub_mod (by omega : size ≤ p.idxOf 1 + cut),
                Nat.mod_eq_of_lt (by omega : p.idxOf 1 + cut - size < size)]; omega
      have badEq : bad root rootMember = back := by
        have ho : Occurs q (root.rotate back) := by
          rw [reverseRoot]; simpa using (hp.2 0 (by omega)).mpr rfl
        exact ((badSpec root rootMember).2 _ (Nat.mod_lt _ (by omega))).mp ho |>.symm
      exact ⟨root, rootMember, by simp only [emit, badEq, reverseRoot]⟩
    have rootCard := Set.ncard_congr (s := singleBadCircles size q) (t := words)
      emit emitMember emitInjective emitSurjective
    let slice := fun first last : Fin limit => {p : List ℕ | p ∈ words ∧
      p.head? = some first.val ∧ p.getLast? = some last.val}
    have finiteSlice (a b : Fin limit) : (slice a b).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro p hp; exact List.mem_permutations.mpr hp.1.1
    letI (a b : Fin limit) : Finite (slice a b) := (finiteSlice a b).to_subtype
    let family := Σ a : Fin limit, Σ b : Fin limit, slice a b
    let forget := fun element : family => element.2.2.val
    have forgetMember (element : family) : forget element ∈ words := element.2.2.property.1
    have forgetInjective : Function.Injective forget := by
      rintro ⟨a, b, p, hp⟩ ⟨c, d, r, hr⟩ he
      change p = r at he
      subst r; have hab : a = c := Fin.ext (Option.some.inj (hp.2.1.symm.trans hr.2.1))
      have hbd : b = d := Fin.ext (Option.some.inj (hp.2.2.symm.trans hr.2.2))
      subst c; subst d; rfl
    have forgetSurjective (p : List ℕ) (hp : p ∈ words) : ∃ element : family, forget element =
      p := by
      obtain ⟨a, b, interior, he, ha, hb⟩ := endpoints p hp
      have ah : p.head? = some a := by simp [he]
      have bh : p.getLast? = some b := by
        rw [he]; change ((a :: interior) ++ [b]).getLast? = some b
        rw [List.getLast?_append_cons]; rfl
      exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨p, hp, ah, bh⟩⟩, rfl⟩
    let f : family → words := fun element => ⟨forget element, forgetMember element⟩
    have fBijective : Function.Bijective f := by
      constructor
      · intro a b he; exact forgetInjective (congrArg Subtype.val he)
      · rintro ⟨p, hp⟩
        obtain ⟨element, he⟩ := forgetSurjective p hp
        exact ⟨element, Subtype.ext he⟩
    have familyCard := Nat.card_congr (Equiv.ofBijective f fBijective)
    change (singleBadCircles size q).ncard = _
    rw [rootCard, ← Nat.card_coe_set_eq, ← familyCard]
    change Nat.card (Σ a : Fin limit, Σ b : Fin limit, slice a b) = _
    rw [Nat.card_sigma]
    have counts (a b : Fin limit) : (slice a b).ncard = term a.val b.val := sliceCounts a b
    simp only [Nat.card_sigma, Nat.card_coe_set_eq, counts]
    change (∑ a : Fin limit, ∑ b : Fin limit, term a.val b.val) = _
    calc
      _ = ∑ a : Fin limit, ∑ b ∈ Finset.range limit, term a.val b := by
        apply Finset.sum_congr rfl; intro a ha; exact Fin.sum_univ_eq_sum_range (term a.val) limit
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range limit, term a b) limit
  have recoverEndpoints (r1 r2 r3 r4 : ℕ)
      (hq : [r1, r2, r3, r4].Perm [1, 2, 3, 4]) (p : List ℕ)
      (hp : p.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs [r1, r2, r3, r4] (p.rotate cut) ↔ cut = 0) :
      ∃ chosen : ℕ → ℕ, ∃ interior : List ℕ,
        p = chosen r1 :: interior ++ [chosen r4] ∧
        chosen 1 < chosen 2 ∧ chosen 2 < chosen 3 ∧ chosen 3 < chosen 4 ∧
        1 ≤ chosen 1 ∧ chosen 4 ≤ size := by
    let q := [r1, r2, r3, r4]
    have hl : p.length = size := by simpa using hp.1.length_eq
    have lettersEq : letters q = 4 := by simpa [letters, q] using hq.foldr_eq (f := max) 0
    have ranks (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ 4) : rank ∈ q := by
      apply hq.mem_iff.mpr; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    obtain ⟨first, tail, split⟩ : ∃ first tail, p = first :: tail := by
      cases p with
      | nil => simp at hl; omega
      | cons first tail => exact ⟨first, tail, rfl⟩
    obtain ⟨last, interior, splitP⟩ : ∃ last interior, p = first :: interior ++ [last] := by
      have ht : tail.length = size - 1 := by rw [split] at hl; simp at hl; omega
      cases hr : tail.reverse with
      | nil => have hh := congrArg List.length hr; simp [ht] at hh; omega
      | cons last rest =>
        have hh := congrArg List.reverse hr
        simp only [List.reverse_reverse, List.reverse_cons] at hh
        exact ⟨last, rest.reverse, by rw [split, hh]; rfl⟩
    have criterion := (unique_bad_cut_iff size (by omega) q p hq hp.1).mp hp.2
    obtain ⟨chosen, hi, hm, selected, _⟩ := criterion.1
    have h12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by simp [lettersEq])
    have h23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by simp [lettersEq])
    have h34 : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by simp [lettersEq])
    have firstUsed : chosen r1 = first := by
      by_contra hn
      apply criterion.2.2.1; have ht : (q.map chosen).Sublist p.tail := by
        rw [splitP] at selected ⊢; exact List.Sublist.of_cons_of_ne hn selected
      refine ⟨chosen, hi, ?_, ht, by simp⟩
      intro rank hlo hhi
      exact ht.subset (List.mem_map.mpr ⟨rank, ranks rank hlo (lettersEq ▸ hhi), rfl⟩)
    have lastUsed : chosen r4 = last := by
      by_contra hn
      apply criterion.2.2.2; have selected' : [chosen r4, chosen r3, chosen r2, chosen r1].Sublist
          (last :: (first :: interior).reverse) := by
        simpa [q, splitP, List.reverse_append] using selected.reverse
      have ht := List.Sublist.of_cons_of_ne hn selected'
      have dropP : p.dropLast = first :: interior := by
        rw [splitP]; change ((first :: interior) ++ [last]).dropLast = _
        rw [List.dropLast_append_cons]; simp
      have ht : (q.map chosen).Sublist p.dropLast := by simpa [q, dropP] using ht.reverse
      refine ⟨chosen, hi, ?_, ht, by simp⟩
      intro rank hlo hhi
      exact ht.subset (List.mem_map.mpr ⟨rank, ranks rank hlo (lettersEq ▸ hhi), rfl⟩)
    have low := List.mem_range'_1.mp
      (hp.1.mem_iff.mp (hm 1 (by omega) (by simp [lettersEq])))
    have high := List.mem_range'_1.mp
      (hp.1.mem_iff.mp (hm 4 (by omega) (by simp [lettersEq])))
    exact ⟨chosen, interior, by rwa [firstUsed, lastUsed], h12, h23, h34, low.1, by omega⟩
  have binary : (singleBadCircles size [1, 2, 4, 3]).ncard <
      (singleBadCircles size [1, 3, 4, 2]).ncard := by
    classical
    let N := size - 2
    have hN : 5 ≤ N := by dsimp [N]; omega
    have sizeEq : size = N + 2 := by dsimp [N]; omega
    let q : List ℕ := [1, 3, 4, 2]
    let slice := fun a b : ℕ => {word : List ℕ |
      word.Perm (List.range' 1 size) ∧ word.head? = some a ∧ word.getLast? = some b ∧
        ∀ cut < size, Occurs q (word.rotate cut) ↔ cut = 0}
    let selected := slice 1 2 ∪ slice 2 3
    have selectedSpec (word : List ℕ) (hw : word ∈ selected) :
        word.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (word.rotate cut) ↔ cut = 0 := by
      rcases hw with hw | hw <;> exact ⟨hw.1, hw.2.2.2⟩
    have lengthEq (word : List ℕ) (hw : word.Perm (List.range' 1 size)) :
        word.length = size := by simpa using hw.length_eq
    have rotateSum (word : List ℕ) (hw : word.Perm (List.range' 1 size)) (a b : ℕ) :
        (word.rotate a).rotate b = word.rotate ((a + b) % size) := by
      rw [List.rotate_rotate, ← List.rotate_mod, lengthEq word hw]
    let root := fun word : List ℕ => word.rotate (word.idxOf 1)
    have rootMember (word : List ℕ) (hw : word ∈ selected) :
        root word ∈ singleBadCircles size q := by
      obtain ⟨hp, hcuts⟩ := selectedSpec word hw
      have hm : 1 ∈ word := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi : word.idxOf 1 < size := by
        simpa [lengthEq word hp] using List.idxOf_lt_length_iff.mpr hm
      refine ⟨(List.rotate_perm _ _).trans hp, ?_,
        (size - word.idxOf 1) % size, Nat.mod_lt _ (by omega), ?_⟩
      · rw [List.head?_rotate (by rwa [lengthEq word hp])]
        exact List.getElem?_idxOf hm
      · intro cut hc
        rw [rotateSum word hp, hcuts _ (Nat.mod_lt _ (by omega))]; by_cases hz : word.idxOf 1 = 0
        · simp [hz, Nat.mod_eq_of_lt hc]
        · have hb : size - word.idxOf 1 < size := by omega
          rw [Nat.mod_eq_of_lt hb]; by_cases hs : word.idxOf 1 + cut < size
          · rw [Nat.mod_eq_of_lt hs]; omega
          · rw [Nat.mod_eq_sub_mod (by omega : size ≤ word.idxOf 1 + cut),
              Nat.mod_eq_of_lt (by omega : word.idxOf 1 + cut - size < size)]
            omega
    have rootInjective : Set.InjOn root selected := by
      intro u hu v hv he; obtain ⟨hp, hcuts⟩ := selectedSpec u hu
      obtain ⟨vp, vcuts⟩ := selectedSpec v hv
      have hm : 1 ∈ v := vp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi : v.idxOf 1 < size := by simpa [lengthEq v vp] using List.idxOf_lt_length_iff.mpr hm
      have undo : (root v).rotate (size - v.idxOf 1) = v := by
        rw [rotateSum v vp, Nat.add_sub_of_le hi.le, Nat.mod_self, List.rotate_zero]
      have eq : u.rotate ((u.idxOf 1 + (size - v.idxOf 1)) % size) = v := by
        rw [← rotateSum u hp, show u.rotate (u.idxOf 1) = root u by rfl, he, undo]
      have occurrence : Occurs q v := by simpa using (vcuts 0 (by omega)).mpr rfl
      have zero := (hcuts _ (Nat.mod_lt _ (by omega))).mp (eq.symm ▸ occurrence)
      rwa [zero, List.rotate_zero] at eq
    have finiteCircles : (singleBadCircles size q).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset; intro word hw
      exact List.mem_permutations.mpr hw.1
    have finiteSlice (a b : ℕ) : (slice a b).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset; intro word hw
      exact List.mem_permutations.mpr hw.1
    have disjoint : Disjoint (slice 1 2) (slice 2 3) := by
      apply Set.disjoint_left.mpr; intro word h1 h2; have hh := h1.2.1.symm.trans h2.2.1; simp at hh
    have lower := Set.ncard_le_ncard_of_injOn root rootMember rootInjective finiteCircles
    have firstCount : (slice 1 2).ncard = 2 ^ N - N - 1 := by
      simpa only [slice, q, sizeEq] using
        RotationAvoidanceBinaryContraction.binary_least_consecutive_endpoint_count N (by omega)
    have secondCount : (slice 2 3).ncard = 2 ^ N - 2 * N := by
      simpa only [slice, q, sizeEq] using
        RotationAvoidanceMarkedContraction.binary_second_consecutive_endpoint_count N (by omega)
    rw [show selected = slice 1 2 ∪ slice 2 3 by rfl,
      Set.ncard_union_eq disjoint (finiteSlice 1 2) (finiteSlice 2 3),
      firstCount, secondCount] at lower
    have exponential : ∀ t : ℕ, 5 ≤ t → t * (t + 1) < 2 ^ t + 2 := by
      intro t ht; induction t, ht using Nat.le_induction with
      | base => decide
      | succ t ht ih =>
        rw [pow_succ]; nlinarith
    have powerBound := exponential N hN; let term := fun a b : ℕ => if 1 ≤ a ∧ a + 1 < b then
      if a = 1 then N.choose (b - 2) + (size - b) - 2
      else if b = a + 2 then (N - 1).choose (a - 1) else 0 else 0
    have total : (singleBadCircles size [1, 2, 4, 3]).ncard =
        ∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b := by
      have mixed_single_bad_count :
          (singleBadCircles size [1, 2, 4, 3]).ncard =
            ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
              if 1 ≤ first ∧ first + 1 < last then
                if first = 1 then (size - 2).choose (last - 2) + (size - last) - 2
                else if last = first + 2 then (size - 3).choose (first - 1) else 0
              else 0 := by
        classical
        let q : List ℕ := [1, 2, 4, 3]
        let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
        have endpoints (p : List ℕ) (hp : p ∈ words) :
            ∃ first last interior, p = first :: interior ++ [last] ∧
              1 ≤ first ∧ first + 1 < last ∧ last < size := by
          obtain ⟨chosen, interior, splitP, h12, h23, h34, low, high⟩ :=
            recoverEndpoints 1 2 4 3 (by decide) p hp
          exact ⟨chosen 1, chosen 3, interior, splitP,
            by omega, by omega, by omega⟩
        let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
          p.head? = some first.val ∧ p.getLast? = some last.val}
        have sliceCounts (a b : Fin size) : (slice a b).ncard =
            if 1 ≤ a.val ∧ a.val + 1 < b.val then
              if a.val = 1 then (size - 2).choose (b.val - 2) + (size - b.val) - 2
              else if b.val = a.val + 2 then (size - 3).choose (a.val - 1) else 0
            else 0 := by
          by_cases hh : 1 ≤ a.val ∧ a.val + 1 < b.val
          · rw [if_pos hh]
            have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
                p.head? = some a.val ∧ p.getLast? = some b.val ∧
                ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
              ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
            rw [he]; by_cases hc : a.val = 1
            · rw [if_pos hc]
              have count := RotationAvoidanceMixedEmptyCount.mixed_empty_lower_endpoint_count
                size b.val (by omega) b.isLt
              simpa only [hc, q] using count
            · rw [if_neg hc]
              by_cases hgap : b.val = a.val + 2
              · rw [if_pos hgap]
                have count := RotationAvoidanceMixed.mixed_nonempty_lower_endpoint_count
                  size a.val (by omega) (by omega)
                simpa only [hgap, q] using count
              · rw [if_neg hgap]
                have empty : {p : List ℕ | p.Perm (List.range' 1 size) ∧
                    p.head? = some a.val ∧ p.getLast? = some b.val ∧
                    ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} = ∅ := by
                  apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
                  obtain ⟨first, last, interior, split, ha, hab, hb⟩ :=
                    endpoints p ⟨hp.1, hp.2.2.2⟩
                  have head : first = a.val := by simpa [split] using hp.2.1
                  have tail : last = b.val := by
                    have he : p.getLast? = some last := by
                      rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                      rw [List.getLast?_append_cons]; rfl
                    exact Option.some.inj (he.symm.trans hp.2.2.1)
                  have form := RotationAvoidanceMixed.mixed_nonempty_lower_normal_form
                    size first last interior (by omega) (by omega) (by omega)
                    (split ▸ hp.1) (split ▸ hp.2.2.2)
                  exact hgap (by omega)
                rw [empty, Set.ncard_empty]
          · rw [if_neg hh]
            have he : slice a b = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
              obtain ⟨first, last, interior, split, ha, hab, hb⟩ := endpoints p hp.1
              have head : first = a.val := by simpa [split] using hp.2.1
              have tail : last = b.val := by
                have he : p.getLast? = some last := by
                  rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                  rw [List.getLast?_append_cons]; rfl
                exact Option.some.inj (he.symm.trans hp.2.2)
              exact hh (by omega)
            rw [he, Set.ncard_empty]
        let term := fun first last : ℕ =>
          if 1 ≤ first ∧ first + 1 < last then
            if first = 1 then (size - 2).choose (last - 2) + (size - last) - 2
            else if last = first + 2 then (size - 3).choose (first - 1) else 0
          else 0
        apply sumSlices q size ?_ term sliceCounts; intro p hp
        obtain ⟨a, b, interior, he, ha, hab, hb⟩ := endpoints p hp
        exact ⟨a, b, interior, he, by omega, hb⟩
      rw [mixed_single_bad_count]; simp only [term, N, show size - 2 - 1 = size - 3 by omega]
    have arithmetic : 2 * (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b) +
        8 + 4 * (N - 1) = 6 * 2 ^ (N - 1) + N * (N - 1) := by
      have middleChoose (M : ℕ) (hM : 1 ≤ M) :
          (∑ b ∈ Finset.range (M - 1), M.choose (b + 1)) + 2 = 2 ^ M := by
        have all := Nat.sum_range_choose M; have split : (∑ b ∈ Finset.range M, M.choose b) =
            (∑ b ∈ Finset.range (M - 1), M.choose (b + 1)) + 1 := by
          simpa only [show M - 1 + 1 = M by omega, Nat.choose_zero_right] using
            Finset.sum_range_succ' (fun b => M.choose b) (M - 1)
        rw [Finset.sum_range_succ, split, Nat.choose_self] at all; omega
      let A := fun b : ℕ => if 3 ≤ b then N.choose (b - 2) + (size - b) - 2 else 0
      let B := fun a : ℕ => if 2 ≤ a ∧ a < N then (N - 1).choose (a - 1) else 0
      have splitTerm (a b : ℕ) (hb : b < size) :
          term a b = (if a = 1 then A b else 0) +
            (if 2 ≤ a ∧ b = a + 2 then (N - 1).choose (a - 1) else 0) := by
        dsimp [term, A]; split_ifs <;> omega
      have rowB (a : ℕ) :
          (∑ b ∈ Finset.range size,
            if 2 ≤ a ∧ b = a + 2 then (N - 1).choose (a - 1) else 0) = B a := by
        by_cases ha : 2 ≤ a
        · have cond : a + 2 < size ↔ a < N := by omega
          simp only [B, ha, true_and, Finset.sum_ite_eq', Finset.mem_range, cond]
        · simp [ha, B]
      have doubleSum : (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b) =
          (∑ b ∈ Finset.range size, A b) + ∑ a ∈ Finset.range size, B a := by
        simp_rw [Finset.sum_congr rfl (fun b hb => splitTerm _ b (Finset.mem_range.mp hb)),
          Finset.sum_add_distrib, rowB]
        have rowA (a : ℕ) : (∑ b ∈ Finset.range size, if a = 1 then A b else 0) =
            if a = 1 then ∑ b ∈ Finset.range size, A b else 0 := by
          by_cases ha : a = 1 <;> simp [ha]
        simp_rw [rowA]
        simp [Finset.sum_ite_eq', show 1 < size by omega]
      have sumA : (∑ b ∈ Finset.range size, A b) =
          ∑ b ∈ Finset.range (N - 1), (N.choose (b + 1) + (N - 1 - b) - 2) := by
        rw [show size = 3 + (N - 1) by omega, Finset.sum_range_add]
        have small : (∑ b ∈ Finset.range 3, A b) = 0 := by
          norm_num [Finset.sum_range_succ, A]
        rw [small, zero_add]; apply Finset.sum_congr rfl
        intro b hb; have hb' := Finset.mem_range.mp hb
        dsimp [A]; rw [if_pos (by omega : 3 ≤ 3 + b), show 3 + b - 2 = b + 1 by omega,
          show size - (3 + b) = N - 1 - b by omega]
      have sumB : (∑ a ∈ Finset.range size, B a) =
          ∑ b ∈ Finset.range (N - 2), (N - 1).choose (b + 1) := by
        have extend : (∑ a ∈ Finset.range size, B a) = ∑ a ∈ Finset.range N, B a := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega)); intro a ha hnot
          have hn : ¬ a < N := by simpa using hnot
          simp [B, hn]
        rw [extend]; conv_lhs => rw [show N = 2 + (N - 2) by omega, Finset.sum_range_add]
        have small : (∑ a ∈ Finset.range 2, B a) = 0 := by
          norm_num [Finset.sum_range_succ, B]
        rw [small, zero_add]; apply Finset.sum_congr rfl
        intro b hb; have hb' := Finset.mem_range.mp hb
        dsimp [B]; rw [if_pos (by omega : 2 ≤ 2 + b ∧ 2 + b < N),
          show 2 + b - 1 = b + 1 by omega]
      have sumAAdd : (∑ b ∈ Finset.range (N - 1),
          (N.choose (b + 1) + (N - 1 - b) - 2)) + 2 * (N - 1) =
          (∑ b ∈ Finset.range (N - 1), N.choose (b + 1)) +
            ∑ b ∈ Finset.range (N - 1), (N - 1 - b) := by
        have each (b : ℕ) (hb : b ∈ Finset.range (N - 1)) :
            (N.choose (b + 1) + (N - 1 - b) - 2) + 2 =
              N.choose (b + 1) + (N - 1 - b) := by
          have hb' := Finset.mem_range.mp hb; have pos := Nat.choose_pos (show b + 1 ≤ N by omega)
          omega
        have sums := Finset.sum_congr rfl each
        simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          smul_eq_mul, mul_comm (N - 1) 2] using sums
      have triangular : 2 * (∑ b ∈ Finset.range (N - 1), (N - 1 - b)) = N * (N - 1) := by
        have reflect := Finset.sum_range_reflect (fun b : ℕ => b) (N - 1)
        have split : (∑ b ∈ Finset.range (N - 1), (N - 1 - b)) =
            (∑ b ∈ Finset.range (N - 1), (N - 2 - b)) + (N - 1) := by
          have each (b : ℕ) (hb : b ∈ Finset.range (N - 1)) :
              N - 1 - b = (N - 2 - b) + 1 := by
            have hb' := Finset.mem_range.mp hb; omega
          rw [Finset.sum_congr rfl each, Finset.sum_add_distrib]; simp
        rw [show N - 1 - 1 = N - 2 by omega] at reflect; rw [split, reflect]
        have ids := Finset.sum_range_id_mul_two (N - 1); rw [show N - 1 - 1 = N - 2 by omega] at ids
        have hi : N - 2 + 2 = N := by omega
        nlinarith
      rw [doubleSum, sumA, sumB]; have ac := middleChoose N (by omega)
      have bc := middleChoose (N - 1) (by omega); rw [show N - 1 - 1 = N - 2 by omega] at bc
      have powerSplit : 2 ^ N = 2 * 2 ^ (N - 1) := by
        conv_lhs => rw [show N = N - 1 + 1 by omega]
        rw [pow_succ]; omega
      omega
    rw [total]; change (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size, term a b) <
      (singleBadCircles size q).ncard
    have powerSplit : 2 ^ N = 2 * 2 ^ (N - 1) := by
      conv_lhs => rw [show N = N - 1 + 1 by omega]
      rw [pow_succ]; omega
    have hm : N - 1 + 1 = N := by omega
    have enough : 2 * N ≤ 2 ^ N := by nlinarith
    have cleanLower : 2 * 2 ^ N ≤ (singleBadCircles size q).ncard + 3 * N + 1 := by omega
    nlinarith
  have ascendingOrder : (singleBadCircles size [2, 1, 4, 3]).ncard <
        (singleBadCircles size [1, 2, 3, 4]).ncard ∧
      (singleBadCircles size [1, 2, 3, 4]).ncard <
        (singleBadCircles size [1, 4, 3, 2]).ncard := by
    classical
    let N := size - 2
    have hN : 5 ≤ N := by dsimp [N]; omega
    have sizeEq : size = N + 2 := by dsimp [N]; omega
    let g := fun t : ℕ => 2 ^ t - t - 1
    let f := fun t : ℕ => 2 ^ (t + 1) - 2 * t - 2 - (t + 1).choose 3
    have gap (t : ℕ) : g t ≤ f t ∧ (4 ≤ t → g t < f t) := by
      dsimp [g, f]; by_cases hsmall : t < 5
      · interval_cases t <;> decide
      · have ht : 5 ≤ t := by omega
        have exponential_bounds (index : ℕ) :
            index + 5 + (index + 5).choose 3 < 2 ^ (index + 4) ∧
            1 + (index + 5).choose 2 < 2 ^ (index + 4) ∧
            index + 5 < 2 ^ (index + 4) := by
          induction index with
          | zero => decide
          | succ index ih =>
            have hthree := Nat.choose_succ_succ' (index + 5) 2
            have htwo := Nat.choose_succ_succ' (index + 5) 1
            simp only [Nat.choose_one_right] at htwo
            have hpower : 2 ^ (index + 1 + 4) = 2 * 2 ^ (index + 4) := by
              rw [show index + 1 + 4 = (index + 4) + 1 by omega, pow_succ, Nat.mul_comm]
            simp only [Nat.add_assoc, Nat.reduceAdd] at hthree htwo hpower ⊢
            rw [hpower]
            omega
        have bound := (exponential_bounds (t - 4)).1
        rw [show t - 4 + 5 = t + 1 by omega,
          show t - 4 + 4 = t by omega] at bound
        have power : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
        have positive : t < 2 ^ t := Nat.lt_two_pow_self
        constructor <;> omega
    have rowConstant (value upper : ℕ) (hu : upper ≤ size + 1) :
        (∑ a ∈ Finset.range (size + 1), if 1 ≤ a ∧ a < upper then value else 0) =
          (upper - 1) * value := by
      have eq : (Finset.range (size + 1)).filter (fun a => 1 ≤ a ∧ a < upper) =
          Finset.Ico 1 upper := by
        ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [← Finset.sum_filter, eq, Finset.sum_const]; simp
    have band (F : ℕ → ℕ → ℕ) :
        (∑ a ∈ Finset.range (size + 1), ∑ b ∈ Finset.range (size + 1),
          if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then F a b else 0) =
        ∑ t ∈ Finset.range (size + 1), ∑ a ∈ Finset.range (size + 1),
          if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then F a (a + t + 1) else 0 := by
      let domain := ((Finset.range (size + 1)) ×ˢ (Finset.range (size + 1))).filter
        (fun ab : ℕ × ℕ => 1 ≤ ab.1 ∧ ab.1 + 2 < ab.2 ∧ ab.2 ≤ size)
      let target := ((Finset.range (size + 1)) ×ˢ (Finset.range (size + 1))).filter
        (fun ta : ℕ × ℕ => 2 ≤ ta.1 ∧ 1 ≤ ta.2 ∧ ta.2 + ta.1 < size)
      have hm (ab : ℕ × ℕ) : ab ∈ domain ↔
          ab.1 < size + 1 ∧ ab.2 < size + 1 ∧
            1 ≤ ab.1 ∧ ab.1 + 2 < ab.2 ∧ ab.2 ≤ size := by
        simp only [domain, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
      have ht (ta : ℕ × ℕ) : ta ∈ target ↔
          ta.1 < size + 1 ∧ ta.2 < size + 1 ∧
            2 ≤ ta.1 ∧ 1 ≤ ta.2 ∧ ta.2 + ta.1 < size := by
        simp only [target, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
      have reindex : (∑ ab ∈ domain, F ab.1 ab.2) =
          ∑ ta ∈ target, F ta.2 (ta.2 + ta.1 + 1) := by
        apply Finset.sum_bij (fun ab _ => (ab.2 - ab.1 - 1, ab.1))
        · intro ab hab
          apply (ht _).mpr; have hab' := (hm ab).mp hab; dsimp; omega
        · intro ab hab cd hcd he
          have hab' := (hm ab).mp hab; have hcd' := (hm cd).mp hcd
          have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
          apply Prod.ext <;> dsimp at * <;> omega
        · intro ta hta
          have hta' := (ht ta).mp hta; refine ⟨(ta.2, ta.2 + ta.1 + 1), (hm _).mpr ?_, ?_⟩
          · dsimp; omega
          · apply Prod.ext <;> dsimp <;> omega
        · intro ab hab
          have hab' := (hm ab).mp hab; dsimp; congr 1; omega
      simpa only [domain, target, Finset.sum_filter, Finset.sum_product] using reindex
    have ascending : (singleBadCircles size [1, 2, 3, 4]).ncard =
        f N + ∑ t ∈ Finset.Ico 2 N, (N - t + 1) * g t := by
      have ascending_single_bad_count :
          (singleBadCircles size [1, 2, 3, 4]).ncard =
            ∑ first ∈ Finset.range (size + 1), ∑ last ∈ Finset.range (size + 1),
              if 1 ≤ first ∧ first + 2 < last ∧ last ≤ size then
                if first = 1 ∧ last = size then
                  2 ^ (size - 1) - 2 * (size - 2) - 2 - (size - 1).choose 3
                else 2 ^ (last - first - 1) - (last - first - 1) - 1
              else 0 := by
        classical
        let q : List ℕ := [1, 2, 3, 4]
        let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
        have endpoints (p : List ℕ) (hp : p ∈ words) :
            ∃ first last interior, p = first :: interior ++ [last] ∧
              1 ≤ first ∧ first + 2 < last ∧ last ≤ size ∧ last < size + 1 := by
          obtain ⟨chosen, interior, splitP, h12, h23, h34, low, high⟩ :=
            recoverEndpoints 1 2 3 4 (by decide) p hp
          exact ⟨chosen 1, chosen 4, interior, splitP,
            by omega, by omega, by omega, by omega⟩
        let slice := fun first last : Fin (size + 1) => {p : List ℕ | p ∈ words ∧
          p.head? = some first.val ∧ p.getLast? = some last.val}
        have sliceCounts (a b : Fin (size + 1)) : (slice a b).ncard =
            if 1 ≤ a.val ∧ a.val + 2 < b.val ∧ b.val ≤ size then
              if a.val = 1 ∧ b.val = size then
                2 ^ (size - 1) - 2 * (size - 2) - 2 - (size - 1).choose 3
              else 2 ^ (b.val - a.val - 1) - (b.val - a.val - 1) - 1
            else 0 := by
          by_cases hh : 1 ≤ a.val ∧ a.val + 2 < b.val ∧ b.val ≤ size
          · rw [if_pos hh]
            have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
                p.head? = some a.val ∧ p.getLast? = some b.val ∧
                ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
              ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
            rw [he]; by_cases hc : a.val = 1 ∧ b.val = size
            · rw [if_pos hc]
              have count := RotationAvoidanceEndpoints.ascending_extreme_endpoint_count
                (size - 2) (by omega)
              have hs : size - 2 + 2 = size := by omega
              have hs' : size - 2 + 1 = size - 1 := by omega
              simpa only [hc.1, hc.2, hs, hs', q] using count
            · rw [if_neg hc]
              have count := RotationAvoidanceAscendingSplit.ascending_nonextreme_endpoint_count
                size a.val b.val hh.1 hh.2.1 hh.2.2 (by omega)
              simpa only [q] using count
          · rw [if_neg hh]
            have he : slice a b = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
              obtain ⟨first, last, interior, split, ha, hab, hu, hb⟩ := endpoints p hp.1
              have head : first = a.val := by simpa [split] using hp.2.1
              have tail : last = b.val := by
                have he : p.getLast? = some last := by
                  rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                  rw [List.getLast?_append_cons]; rfl
                exact Option.some.inj (he.symm.trans hp.2.2)
              exact hh (by omega)
            rw [he, Set.ncard_empty]
        let term := fun first last : ℕ =>
          if 1 ≤ first ∧ first + 2 < last ∧ last ≤ size then
            if first = 1 ∧ last = size then
              2 ^ (size - 1) - 2 * (size - 2) - 2 - (size - 1).choose 3
            else 2 ^ (last - first - 1) - (last - first - 1) - 1
          else 0
        apply sumSlices q (size + 1) ?_ term sliceCounts; intro p hp
        obtain ⟨a, b, interior, he, ha, hab, hu, hb⟩ := endpoints p hp
        exact ⟨a, b, interior, he, by omega, hb⟩
      rw [ascending_single_bad_count]
      have reindex := band (fun a b => if a = 1 ∧ b = size then f N else g (b - a - 1))
      have original : (∑ a ∈ Finset.range (size + 1),
          ∑ b ∈ Finset.range (size + 1),
          if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then
            if a = 1 ∧ b = size then f N else g (b - a - 1) else 0) =
          ∑ a ∈ Finset.range (size + 1), ∑ b ∈ Finset.range (size + 1),
            if 1 ≤ a ∧ a + 2 < b ∧ b ≤ size then
              if a = 1 ∧ b = size then
                2 ^ (size - 1) - 2 * (size - 2) - 2 - (size - 1).choose 3
              else 2 ^ (b - a - 1) - (b - a - 1) - 1 else 0 := by
        simp only [f, g, N, show size - 2 + 1 = size - 1 by omega]
      rw [← original, reindex]; have row (t : ℕ) (ht : t < size + 1) :
          (∑ a ∈ Finset.range (size + 1),
            if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then
              if a = 1 ∧ a + t + 1 = size then f N else g (a + t + 1 - a - 1)
            else 0) =
            if t = N then f N else if 2 ≤ t ∧ t < N then (N - t + 1) * g t else 0 := by
        by_cases he : t = N
        · subst t
          have each (a : ℕ) :
              (if 2 ≤ N ∧ 1 ≤ a ∧ a + N < size then
                if a = 1 ∧ a + N + 1 = size then f N else g (a + N + 1 - a - 1)
              else 0) = if a = 1 then f N else 0 := by
            split_ifs <;> omega
          simp_rw [each]
          simp [Finset.sum_ite_eq', show 1 < size + 1 by omega]
        · rw [if_neg he]
          by_cases hi : 2 ≤ t ∧ t < N
          · rw [if_pos hi]
            have each (a : ℕ) :
                (if 2 ≤ t ∧ 1 ≤ a ∧ a + t < size then
                  if a = 1 ∧ a + t + 1 = size then f N else g (a + t + 1 - a - 1)
                else 0) = if 1 ≤ a ∧ a < size - t then g t else 0 := by
              have index : a + t + 1 - a - 1 = t := by omega
              rw [index]; split_ifs <;> omega
            rw [Finset.sum_congr rfl (fun a _ => each a), rowConstant _ _ (by omega),
              show size - t - 1 = N - t + 1 by omega]
          · rw [if_neg hi]
            apply Finset.sum_eq_zero; intro a ha; have ha' := Finset.mem_range.mp ha
            have falseCond : ¬ (2 ≤ t ∧ 1 ≤ a ∧ a + t < size) := by omega
            simp [falseCond]
      rw [Finset.sum_congr rfl (fun t ht => row t (Finset.mem_range.mp ht))]; have each (t : ℕ) :
          (if t = N then f N else if 2 ≤ t ∧ t < N then (N - t + 1) * g t else 0) =
          (if t = N then f N else 0) +
            (if 2 ≤ t ∧ t < N then (N - t + 1) * g t else 0) := by
        split_ifs <;> omega
      rw [Finset.sum_congr rfl (fun t _ => each t), Finset.sum_add_distrib]
      have filtered : (Finset.range (size + 1)).filter (fun t => 2 ≤ t ∧ t < N) =
          Finset.Ico 2 N := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [Finset.sum_ite_eq']; simp only [Finset.mem_range, show N < size + 1 by omega, if_true]
      congr 1
      rw [← Finset.sum_filter, filtered]
    have descending : (singleBadCircles size [1, 4, 3, 2]).ncard =
        ∑ t ∈ Finset.Ico 2 (N + 1), (f t + (N - t) * g t) := by
      have descending_single_bad_count :
          (singleBadCircles size [1, 4, 3, 2]).ncard =
            ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
              if 1 ≤ first ∧ first < last ∧ last + 2 ≤ size then
                if last = first + 1 then 2 ^ (size - first) - 2 * (size - first - 1) - 2 -
                  (size - first).choose 3
                else 2 ^ (size - last) - (size - last) - 1
              else 0 := by
        classical
        let q : List ℕ := [1, 4, 3, 2]
        let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
        have endpoints (p : List ℕ) (hp : p ∈ words) :
            ∃ first last interior, p = first :: interior ++ [last] ∧
              1 ≤ first ∧ first < last ∧ last + 2 ≤ size ∧ last < size := by
          obtain ⟨chosen, interior, splitP, h12, h23, h34, low, high⟩ :=
            recoverEndpoints 1 4 3 2 (by decide) p hp
          exact ⟨chosen 1, chosen 2, interior, splitP,
            by omega, by omega, by omega, by omega⟩
        let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
          p.head? = some first.val ∧ p.getLast? = some last.val}
        have sliceCounts (a b : Fin size) : (slice a b).ncard =
            if 1 ≤ a.val ∧ a.val < b.val ∧ b.val + 2 ≤ size then
              if b.val = a.val + 1 then 2 ^ (size - a.val) - 2 * (size - a.val - 1) - 2 -
                (size - a.val).choose 3
              else 2 ^ (size - b.val) - (size - b.val) - 1
            else 0 := by
          by_cases hh : 1 ≤ a.val ∧ a.val < b.val ∧ b.val + 2 ≤ size
          · rw [if_pos hh]
            have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
                p.head? = some a.val ∧ p.getLast? = some b.val ∧
                ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
              ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
            rw [he]; by_cases hc : b.val = a.val + 1
            · rw [if_pos hc]
              have count := RotationAvoidanceDescending.descending_consecutive_endpoint_count
                size a.val hh.1 (by omega)
              simpa only [hc, q] using count
            · rw [if_neg hc]
              have count :=
                RotationAvoidanceDescendingSplit.descending_positive_middle_endpoint_count
                size a.val b.val hh.1 (by omega) hh.2.2
              simpa only [q] using count
          · rw [if_neg hh]
            have he : slice a b = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
              obtain ⟨first, last, interior, split, ha, hab, hu, hb⟩ := endpoints p hp.1
              have head : first = a.val := by simpa [split] using hp.2.1
              have tail : last = b.val := by
                have he : p.getLast? = some last := by
                  rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                  rw [List.getLast?_append_cons]; rfl
                exact Option.some.inj (he.symm.trans hp.2.2)
              exact hh (by omega)
            rw [he, Set.ncard_empty]
        let term := fun first last : ℕ =>
          if 1 ≤ first ∧ first < last ∧ last + 2 ≤ size then
            if last = first + 1 then
              2 ^ (size - first) - 2 * (size - first - 1) - 2 - (size - first).choose 3
            else 2 ^ (size - last) - (size - last) - 1
          else 0
        apply sumSlices q size ?_ term sliceCounts; intro p hp
        obtain ⟨a, b, interior, he, ha, hab, hu, hb⟩ := endpoints p hp
        exact ⟨a, b, interior, he, by omega, hb⟩
      rw [descending_single_bad_count,
        Finset.sum_comm]
      have row (b : ℕ) (hb : b < size) :
          (∑ a ∈ Finset.range size, if 1 ≤ a ∧ a < b ∧ b + 2 ≤ size then
            if b = a + 1 then 2 ^ (size - a) - 2 * (size - a - 1) - 2 -
              (size - a).choose 3 else g (size - b) else 0) =
          if 2 ≤ b ∧ b + 2 ≤ size then f (size - b) + (b - 2) * g (size - b) else 0 := by
        by_cases hi : 2 ≤ b ∧ b + 2 ≤ size
        · rw [if_pos hi]
          have each (a : ℕ) :
              (if 1 ≤ a ∧ a < b ∧ b + 2 ≤ size then
                if b = a + 1 then 2 ^ (size - a) - 2 * (size - a - 1) - 2 -
                  (size - a).choose 3 else g (size - b) else 0) =
              (if a = b - 1 then f (size - b) else 0) +
                (if 1 ≤ a ∧ a < b - 1 then g (size - b) else 0) := by
            have index (he : a = b - 1) : size - a = size - b + 1 := by omega
            dsimp [f]
            split_ifs <;> try omega
            all_goals
              rw [index (by omega), show size - b + 1 - 1 = size - b by omega]; simp only [add_zero]
          rw [Finset.sum_congr rfl (fun a _ => each a), Finset.sum_add_distrib,
            Finset.sum_ite_eq']
          simp only [Finset.mem_range, show b - 1 < size by omega, if_true]
          have filterEq : (Finset.range size).filter (fun a => 1 ≤ a ∧ a < b - 1) =
              Finset.Ico 1 (b - 1) := by
            ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
          rw [← Finset.sum_filter, filterEq, Finset.sum_const]
          simp [show b - 1 - 1 = b - 2 by omega]
        · rw [if_neg hi]
          apply Finset.sum_eq_zero; intro a ha
          have hn : ¬ (1 ≤ a ∧ a < b ∧ b + 2 ≤ size) := by omega
          simp [hn]
      change (∑ b ∈ Finset.range size, ∑ a ∈ Finset.range size,
        if 1 ≤ a ∧ a < b ∧ b + 2 ≤ size then
          if b = a + 1 then 2 ^ (size - a) - 2 * (size - a - 1) - 2 -
            (size - a).choose 3 else g (size - b) else 0) = _
      rw [Finset.sum_congr rfl (fun b hb => row b (Finset.mem_range.mp hb))]
      have filterEq : (Finset.range size).filter (fun b => 2 ≤ b ∧ b + 2 ≤ size) =
          Finset.Ico 2 (size - 1) := by
        ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [← Finset.sum_filter, filterEq]; have each (b : ℕ) (hb : b ∈ Finset.Ico 2 (size - 1)) :
          f (size - b) + (b - 2) * g (size - b) =
            f (size - b) + (N - (size - b)) * g (size - b) := by
        have hb' := Finset.mem_Ico.mp hb; rw [show b - 2 = N - (size - b) by omega]
      rw [Finset.sum_congr rfl each,
        Finset.sum_Ico_reflect (fun t => f t + (N - t) * g t) 2 (by omega : size - 1 ≤ size + 1),
        show size + 1 - (size - 1) = 2 by omega, show size + 1 - 2 = N + 1 by omega]
    have paired : (singleBadCircles size [2, 1, 4, 3]).ncard =
        g N + ∑ t ∈ Finset.Ico 2 N, ∑ l ∈ Finset.Ico 1 t, l * (t - l) := by
      have paired_single_bad_count :
          (singleBadCircles size [2, 1, 4, 3]).ncard =
            ∑ first ∈ Finset.range size, ∑ last ∈ Finset.range size,
              if 2 ≤ first ∧ first < last then
                if last = first + 1 then (size - 2).choose (first - 1) - 1
                else (first - 1) * (size - last)
              else 0 := by
        classical
        let q : List ℕ := [2, 1, 4, 3]
        let words := {p : List ℕ | p.Perm (List.range' 1 size) ∧
          ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0}
        have endpoints (p : List ℕ) (hp : p ∈ words) :
            ∃ first last interior, p = first :: interior ++ [last] ∧
              2 ≤ first ∧ first < last ∧ last < size := by
          obtain ⟨chosen, interior, splitP, h12, h23, h34, low, high⟩ :=
            recoverEndpoints 2 1 4 3 (by decide) p hp
          exact ⟨chosen 2, chosen 3, interior, splitP,
            by omega, by omega, by omega⟩
        let slice := fun first last : Fin size => {p : List ℕ | p ∈ words ∧
          p.head? = some first.val ∧ p.getLast? = some last.val}
        have sliceCounts (a b : Fin size) : (slice a b).ncard =
            if 2 ≤ a.val ∧ a.val < b.val then
              if b.val = a.val + 1 then (size - 2).choose (a.val - 1) - 1
              else (a.val - 1) * (size - b.val)
            else 0 := by
          by_cases hh : 2 ≤ a.val ∧ a.val < b.val
          · rw [if_pos hh]
            have he : slice a b = {p : List ℕ | p.Perm (List.range' 1 size) ∧
                p.head? = some a.val ∧ p.getLast? = some b.val ∧
                ∀ cut < size, Occurs q (p.rotate cut) ↔ cut = 0} := by
              ext p; simp only [slice, words, Set.mem_setOf_eq]; tauto
            rw [he]; by_cases hc : b.val = a.val + 1
            · rw [if_pos hc]
              have count := RotationAvoidanceConsecutive.consecutive_shuffle_endpoint_count
                (a.val - 1) (size - a.val - 1) (by omega) (by omega)
              have hs : a.val - 1 + (size - a.val - 1) + 2 = size := by omega
              have hsum : a.val - 1 + (size - a.val - 1) = size - 2 := by omega
              have hf : a.val - 1 + 1 = a.val := by omega
              have hl : a.val - 1 + 2 = b.val := by omega
              simpa only [hsum, show size - 2 + 2 = size by omega, hf, hl, q] using count
            · rw [if_neg hc]
              have count := RotationAvoidanceConsecutive.positive_middle_endpoint_count
                size a.val b.val hh.1 (by omega) b.isLt
              simpa only [q, Nat.mul_comm] using count
          · rw [if_neg hh]
            have he : slice a b = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp
              obtain ⟨first, last, interior, split, ha, hab, hb⟩ := endpoints p hp.1
              have head : first = a.val := by simpa [split] using hp.2.1
              have tail : last = b.val := by
                have he : p.getLast? = some last := by
                  rw [split]; change ((first :: interior) ++ [last]).getLast? = some last
                  rw [List.getLast?_append_cons]; rfl
                exact Option.some.inj (he.symm.trans hp.2.2)
              exact hh (by omega)
            rw [he, Set.ncard_empty]
        let term := fun first last : ℕ =>
          if 2 ≤ first ∧ first < last then
            if last = first + 1 then (size - 2).choose (first - 1) - 1
            else (first - 1) * (size - last)
          else 0
        apply sumSlices q size ?_ term sliceCounts; intro p hp
        obtain ⟨a, b, interior, he, ha, hab, hb⟩ := endpoints p hp
        exact ⟨a, b, interior, he, by omega, hb⟩
      rw [paired_single_bad_count]; have split (a b : ℕ) (ha : a < size) (hb : b < size) :
          (if 2 ≤ a ∧ a < b then
            if b = a + 1 then N.choose (a - 1) - 1 else (a - 1) * (size - b) else 0) =
          (if 2 ≤ a ∧ b = a + 1 then N.choose (a - 1) - 1 else 0) +
            (if 2 ≤ a ∧ a + 1 < b then (a - 1) * (size - b) else 0) := by
        split_ifs <;> omega
      change (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size,
        if 2 ≤ a ∧ a < b then
          if b = a + 1 then N.choose (a - 1) - 1 else (a - 1) * (size - b) else 0) = _
      rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl
        (fun b hb => split a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)))]
      simp_rw [Finset.sum_add_distrib]
      have diagonal : (∑ a ∈ Finset.range size, ∑ b ∈ Finset.range size,
          if 2 ≤ a ∧ b = a + 1 then N.choose (a - 1) - 1 else 0) = g N := by
        have row (a : ℕ) : (∑ b ∈ Finset.range size,
            if 2 ≤ a ∧ b = a + 1 then N.choose (a - 1) - 1 else 0) =
            if 2 ≤ a ∧ a < N + 1 then N.choose (a - 1) - 1 else 0 := by
          by_cases ha : 2 ≤ a
          · have cond : a + 1 < size ↔ a < N + 1 := by omega
            simp only [ha, true_and, Finset.sum_ite_eq', Finset.mem_range, cond]
          · simp [ha]
        rw [Finset.sum_congr rfl (fun a _ => row a)]
        have filterEq : (Finset.range size).filter (fun a => 2 ≤ a ∧ a < N + 1) =
            Finset.Ico 2 (N + 1) := by
          ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [← Finset.sum_filter, filterEq]
        have shift : (∑ a ∈ Finset.Ico 2 (N + 1), (N.choose (a - 1) - 1)) =
            ∑ l ∈ Finset.Ico 1 N, (N.choose l - 1) := by
          apply Finset.sum_bij (fun a _ => a - 1)
          · intro a ha
            have ha' := Finset.mem_Ico.mp ha; apply Finset.mem_Ico.mpr; omega
          · intro a ha b hb he
            have ha' := Finset.mem_Ico.mp ha; have hb' := Finset.mem_Ico.mp hb; omega
          · intro l hl
            have hl' := Finset.mem_Ico.mp hl; exact ⟨l + 1, Finset.mem_Ico.mpr (by omega), by omega⟩
          · intro a ha; rfl
        rw [shift]; have middle : (∑ l ∈ Finset.Ico 1 N, N.choose l) + 2 = 2 ^ N := by
          have all := Nat.sum_range_choose N; rw [Finset.sum_range_succ] at all
          have split := Finset.sum_range_add_sum_Ico (fun l => N.choose l) (show 1 ≤ N by omega)
          norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
            Nat.choose_self, zero_add] at split all
          omega
        have balance : (∑ l ∈ Finset.Ico 1 N, (N.choose l - 1)) + (N - 1) =
            ∑ l ∈ Finset.Ico 1 N, N.choose l := by
          have each (l : ℕ) (hl : l ∈ Finset.Ico 1 N) : (N.choose l - 1) + 1 = N.choose l := by
            have pos := Nat.choose_pos (Finset.mem_Ico.mp hl).2.le; omega
          have sums := Finset.sum_congr rfl each
          simpa only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
            mul_one] using sums
        dsimp [g]; omega
      rw [diagonal]; congr 1; let domain := ((Finset.range size) ×ˢ (Finset.range size)).filter
        (fun ab : ℕ × ℕ => 2 ≤ ab.1 ∧ ab.1 + 1 < ab.2)
      let target := ((Finset.range size) ×ˢ (Finset.range size)).filter
        (fun tl : ℕ × ℕ => 2 ≤ tl.1 ∧ tl.1 < N ∧ 1 ≤ tl.2 ∧ tl.2 < tl.1)
      have hm (ab : ℕ × ℕ) : ab ∈ domain ↔
          ab.1 < size ∧ ab.2 < size ∧ 2 ≤ ab.1 ∧ ab.1 + 1 < ab.2 := by
        simp only [domain, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
      have ht (tl : ℕ × ℕ) : tl ∈ target ↔
          tl.1 < size ∧ tl.2 < size ∧ 2 ≤ tl.1 ∧ tl.1 < N ∧ 1 ≤ tl.2 ∧ tl.2 < tl.1 := by
        simp only [target, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto
      have reindex : (∑ ab ∈ domain, (ab.1 - 1) * (size - ab.2)) =
          ∑ tl ∈ target, tl.2 * (tl.1 - tl.2) := by
        apply Finset.sum_bij (fun ab _ => (ab.1 - 1 + (size - ab.2), ab.1 - 1))
        · intro ab hab
          have hab' := (hm ab).mp hab; apply (ht _).mpr; dsimp; omega
        · intro ab hab cd hcd he
          have hab' := (hm ab).mp hab; have hcd' := (hm cd).mp hcd
          have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he
          apply Prod.ext <;> dsimp at * <;> omega
        · intro tl htl
          have htl' := (ht tl).mp htl; refine ⟨(tl.2 + 1, size - (tl.1 - tl.2)), (hm _).mpr ?_, ?_⟩
          · dsimp; omega
          · apply Prod.ext <;> dsimp <;> omega
        · intro ab hab
          have hab' := (hm ab).mp hab; dsimp
          rw [show ab.1 - 1 + (size - ab.2) - (ab.1 - 1) = size - ab.2 by omega]
      have expanded : (∑ t ∈ Finset.Ico 2 N, ∑ l ∈ Finset.Ico 1 t, l * (t - l)) =
          ∑ tl ∈ target, tl.2 * (tl.1 - tl.2) := by
        have each (t : ℕ) (ht : t ∈ Finset.Ico 2 N) :
            (∑ l ∈ Finset.Ico 1 t, l * (t - l)) =
            ∑ l ∈ Finset.range size, if 1 ≤ l ∧ l < t then l * (t - l) else 0 := by
          have ht' := Finset.mem_Ico.mp ht
          have filterEq : (Finset.range size).filter (fun l => 1 ≤ l ∧ l < t) =
              Finset.Ico 1 t := by
            ext l; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
          rw [← Finset.sum_filter, filterEq]
        rw [Finset.sum_congr rfl each]
        have filterEq : (Finset.range size).filter (fun t => 2 ≤ t ∧ t < N) =
            Finset.Ico 2 N := by
          ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [← filterEq, Finset.sum_filter]
        simp only [target, Finset.sum_filter, Finset.sum_product, ite_and]
        apply Finset.sum_congr rfl; intro t ht
        by_cases h2 : 2 ≤ t <;> by_cases hn : t < N <;> simp [h2, hn]
      rw [expanded, ← reindex]; simp only [domain, Finset.sum_filter, Finset.sum_product]
    let H := fun t : ℕ => ∑ l ∈ Finset.Ico 1 t, l * (t - l)
    have powerLinear : ∀ t : ℕ, 2 ≤ t → t + 2 ≤ 2 ^ t := by
      intro t ht; induction t, ht using Nat.le_induction with
      | base => decide
      | succ t ht ih => rw [pow_succ]; omega
    have triangleBound : ∀ t : ℕ, 2 ≤ t →
        (∑ l ∈ Finset.Ico 1 (t + 1), l) ≤ 2 ^ t - 1 := by
      intro t ht; induction t, ht using Nat.le_induction with
      | base => decide
      | succ t ht ih =>
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t + 1), pow_succ]; have hp := powerLinear t ht
        omega
    have fiberBound : ∀ t : ℕ, 2 ≤ t → H t ≤ g t := by
      intro t ht; induction t, ht using Nat.le_induction with
      | base => decide
      | succ t ht ih =>
        have step : H (t + 1) = H t + ∑ l ∈ Finset.Ico 1 (t + 1), l := by
          dsimp [H]; rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ t)]
          have each (l : ℕ) (hl : l ∈ Finset.Ico 1 t) :
              l * (t + 1 - l) = l * (t - l) + l := by
            have hl' := Finset.mem_Ico.mp hl; rw [show t + 1 - l = (t - l) + 1 by omega]; ring
          rw [Finset.sum_congr rfl each, Finset.sum_add_distrib,
            Finset.sum_Ico_succ_top (by omega : 1 ≤ t)]
          simp [Nat.add_assoc]
        have gs : g (t + 1) = g t + (2 ^ t - 1) := by
          have hp := powerLinear t ht; dsimp [g]; rw [pow_succ]; omega
        rw [step, gs]; exact Nat.add_le_add ih (triangleBound t ht)
    constructor
    · rw [paired, ascending]
      have sums : (∑ t ∈ Finset.Ico 2 N, H t) <
          ∑ t ∈ Finset.Ico 2 N, (N - t + 1) * g t := by
        apply Finset.sum_lt_sum
        · intro t ht
          have ht' := Finset.mem_Ico.mp ht; have hb := fiberBound t ht'.1
          have hn : 1 ≤ N - t + 1 := by omega
          nlinarith
        · refine ⟨2, Finset.mem_Ico.mpr (by omega), ?_⟩
          norm_num [H, g, Finset.sum_Ico_succ_top]
          omega
      have hg := (gap N).1; change g N + (∑ t ∈ Finset.Ico 2 N, H t) < _; omega
    · rw [ascending, descending, Finset.sum_Ico_succ_top (by omega : 2 ≤ N)]
      simp only [Nat.sub_self, zero_mul, add_zero]
      have sums : (∑ t ∈ Finset.Ico 2 N, (N - t + 1) * g t) <
          ∑ t ∈ Finset.Ico 2 N, (f t + (N - t) * g t) := by
        apply Finset.sum_lt_sum
        · intro t ht
          have hg := (gap t).1; nlinarith
        · refine ⟨4, Finset.mem_Ico.mpr (by omega), ?_⟩
          have hg := (gap 4).2 (by omega); nlinarith
      omega
  exact ⟨ascendingOrder.1, ascendingOrder.2, binary⟩

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGaps
