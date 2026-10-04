/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMarkedContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMarkedContraction
   mirror-E: none(waiver:marked-binary-contraction-slice)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Marked binary circles exclude exactly one descending input for each lower position. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceBinaryContraction
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMarkedContraction

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular RotationAvoidanceBinaryContraction

set_option maxHeartbeats 2400000 in
-- The marked-circle inverse and every failure position are checked in one counting proof.
set_option maxRecDepth 4096 in
theorem binary_second_consecutive_endpoint_count (width : ℕ) (hwidth : 3 ≤ width) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
      word.head? = some 2 ∧ word.getLast? = some 3 ∧
      ∀ cut < width + 2, Occurs [1, 3, 4, 2] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = 2 ^ width - 2 * width := by
  classical
  let q : List ℕ := [1, 3, 4, 2]
  let parents := {p : List ℕ | p ∈ rotationAvoiders (width + 1) (width + 1) q ∧
    p.head? = some 2}
  let upper := fun p : List ℕ => p.tail.filter (fun value => decide (2 < value))
  let failures := {p : List ℕ | p ∈ parents ∧ (upper p).Pairwise (· > ·)}
  let accepted := parents \ failures
  let target := {word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
    word.head? = some 2 ∧ word.getLast? = some 3 ∧
    ∀ cut < width + 2, Occurs q (word.rotate cut) ↔ cut = 0}
  have rotatedGood (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q) (cut : ℕ) :
      p.rotate cut ∈ rotationAvoiders (width + 1) (width + 1) q := by
    refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
    intro start hs ho
    rw [List.rotate_rotate, ← List.rotate_mod,
      show p.length = width + 1 by simpa using hp.1.length_eq] at ho
    exact hp.2 _ (Nat.mod_lt _ (by omega)) ho
  let root := fun value (p : List ℕ) => p.rotate (p.idxOf value)
  have rootHead (value : ℕ) (p : List ℕ) (hm : value ∈ p) :
      (root value p).head? = some value := by
    change (p.rotate (p.idxOf value)).head? = some value
    rw [List.head?_rotate (List.idxOf_lt_length_iff.mpr hm)]
    exact List.getElem?_idxOf hm
  have rootedUnique (u v : List ℕ) (hu : u.Nodup) (value : ℕ)
      (hh : u.head? = some value) (hv : v.head? = some value)
      (hr : List.IsRotated u v) : u = v := by
    obtain ⟨cut, he⟩ := hr
    have hn : u ≠ [] := by intro he; simp [he] at hh
    have hz : 0 < u.length := List.length_pos_of_ne_nil hn
    have hb : cut % u.length < u.length := Nat.mod_lt _ hz
    have hg : u[cut % u.length]? = u[0]? := by
      rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?, hh, hv]
    rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz,
      Option.some.injEq] at hg
    have hzero : cut % u.length = 0 := hu.getElem_inj_iff.mp hg
    rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he
    exact he
  have rootMember (value : ℕ) (hv : 1 ≤ value ∧ value ≤ width + 1) (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q) :
      root value p ∈ rotationAvoiders (width + 1) (width + 1) q ∧
        (root value p).head? = some value := by
    exact ⟨rotatedGood p hp _, rootHead value p
      (hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega)))⟩
  have rootTwice (a b : ℕ) (hb : 1 ≤ b ∧ b ≤ width + 1) (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q)
      (hhead : p.head? = some a) : root a (root b p) = p := by
    have hm := rootMember b hb p hp
    have hmem : a ∈ root b p :=
      (List.rotate_perm p _).mem_iff.mpr (List.mem_of_head? hhead)
    apply rootedUnique (root a (root b p)) p
      (List.nodup_rotate.mpr (hm.1.1.nodup_iff.mpr List.nodup_range')) a
      (rootHead a _ hmem) hhead
    exact (List.IsRotated.forall _ _).trans (List.IsRotated.forall _ _)
  have parentsCount : parents.ncard = (circularAvoiders (width + 1) q).ncard := by
    have hc := Set.ncard_congr (s := circularAvoiders (width + 1) q) (t := parents)
      (fun p _ => root 2 p) (fun p hp => rootMember 2 (by omega) p hp.1) (by
        intro u v hu hv he
        have hh := congrArg (root 1) he
        rwa [rootTwice 1 2 (by omega) u hu.1 hu.2,
          rootTwice 1 2 (by omega) v hv.1 hv.2] at hh) (by
        intro p hp
        refine ⟨root 1 p, rootMember 1 (by omega) p hp.1, ?_⟩
        exact rootTwice 2 1 (by omega) p hp.1 hp.2)
    exact hc.symm
  have parentSplit (p : List ℕ) (hp : p ∈ parents) : p = 2 :: p.tail := by
    cases p with
    | nil => simp [parents] at hp
    | cons head tail =>
      have hh : head = 2 := by simpa using hp.2
      simp [hh]
  have descendingGood (p : List ℕ) (hp : p.Perm (List.range' 1 (width + 1)))
      (hh : p.head? = some 2) (hd : (upper p).Pairwise (· > ·)) : p ∈ parents := by
    have splitP : p = 2 :: p.tail := by
      cases p with
      | nil => simp at hh
      | cons head tail =>
        have he : head = 2 := by simpa using hh
        simp [he]
    have proto : p ∈ parents := by
      refine ⟨⟨hp, ?_⟩, hh⟩
      intro cut hc
      apply (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q p
        (by decide) hp).mpr ?_ |>.2 cut hc
      intro shift hs ho
      obtain ⟨chosen, hi, hm, selected, _⟩ := ho
      have hperm : (q.rotate shift).Perm [1, 2, 3, 4] :=
        (List.rotate_perm _ _).trans (by decide)
      have hl : letters (q.rotate shift) = 4 := by
        simpa [letters] using hperm.foldr_eq (f := max) 0
      have h12 : chosen 1 < chosen 2 := by simpa only [hl] using hi 1 (by omega) (by omega)
      have h23 : chosen 2 < chosen 3 := by simpa only [hl] using hi 2 (by omega) (by omega)
      have h34 : chosen 3 < chosen 4 := by simpa only [hl] using hi 3 (by omega) (by omega)
      have hmin : 1 ≤ chosen 1 := by
        have hh := List.mem_range'_1.mp (hp.mem_iff.mp (hm 1 (by omega) (by rw [hl]; omega)))
        omega
      have pair (i j : ℕ) (ht : [i, j].Sublist (q.rotate shift))
          (hbi : 2 < chosen i) (hbj : 2 < chosen j) : chosen i > chosen j := by
        have ht := (ht.map chosen).trans selected
        rw [splitP] at ht
        have ht := List.Sublist.of_cons_of_ne (by omega : chosen i ≠ 2) ht
        have hf := ht.filter (fun value => decide (2 < value))
        have hf : [chosen i, chosen j].Sublist (upper p) := by
          simpa [upper, hbi, hbj] using hf
        exact List.pairwise_iff_forall_sublist.mp hd hf
      interval_cases shift
      · have ht := pair 3 4 (by decide) (by omega) (by omega); omega
      · have ht := pair 3 4 (by decide) (by omega) (by omega); omega
      · have secondHigh : 2 < chosen 2 := by
          by_contra hn
          have he : chosen 2 = 2 := by omega
          have ht : [chosen 4, chosen 2].Sublist p :=
            ((by decide : ([4, 2] : List ℕ).Sublist (q.rotate 2)).map chosen).trans selected
          rw [splitP] at ht
          have ht := List.Sublist.of_cons_of_ne (by omega : chosen 4 ≠ 2) ht
          have hm : 2 ∈ p.tail := he ▸ ht.subset (by simp)
          exact (List.nodup_cons.mp (splitP ▸ hp.nodup_iff.mpr List.nodup_range')).1 hm
        have ht := pair 2 3 (by decide) secondHigh (by omega); omega
      · have ht := pair 3 4 (by decide) (by omega) (by omega); omega
    exact proto
  let high := (List.range' 3 (width - 1)).reverse
  let insert := fun cut : Fin width => 2 :: high.take cut.val ++ [1] ++ high.drop cut.val
  have highLength : high.length = width - 1 := by simp [high]
  have highDesc : high.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have highBounds (value : ℕ) (hv : value ∈ high) : 2 < value ∧ value ≤ width + 1 := by
    have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
  have insertMember (cut : Fin width) : insert cut ∈ failures := by
    have hp : (insert cut).Perm (List.range' 1 (width + 1)) := by
      have move := List.perm_middle (a := 1) (l₁ := high.take cut.val)
        (l₂ := high.drop cut.val)
      have hmove : (high.take cut.val ++ [1] ++ high.drop cut.val).Perm (1 :: high) := by
        simpa only [List.append_assoc, List.singleton_append, List.take_append_drop] using move
      have hl := (hmove.cons 2).trans (List.Perm.swap 1 2 high)
      have hr : List.range' 1 (width + 1) = 1 :: 2 :: List.range' 3 (width - 1) := by
        rw [show width + 1 = ((width - 1) + 1) + 1 by omega,
          List.range'_succ, List.range'_succ]
      rw [hr]
      exact hl.trans ((List.reverse_perm _).cons 2 |>.cons 1)
    have filtered : upper (insert cut) = high := by
      have keep (part : List ℕ) (hs : part.Sublist high) :
          part.filter (fun value => decide (2 < value)) = part := by
        apply List.filter_eq_self.mpr
        intro value hv
        simp only [decide_eq_true_eq]
        exact (highBounds value (hs.subset hv)).1
      simp only [upper, insert, List.cons_append, List.tail_cons, List.filter_append,
        List.filter_singleton, show decide (2 < (1 : ℕ)) = false from rfl,
        Bool.cond_false,
        List.append_nil, keep _ (List.take_sublist _ _), keep _ (List.drop_sublist _ _),
        List.take_append_drop]
    have hd : (upper (insert cut)).Pairwise (· > ·) := filtered ▸ highDesc
    exact ⟨descendingGood _ hp (by simp [insert]) hd, hd⟩
  have insertDecode (cut : Fin width) : (insert cut).tail.idxOf 1 = cut.val := by
    have hn : 1 ∉ high.take cut.val := by
      intro hv
      have hh := highBounds 1 ((List.take_sublist _ _).subset hv); omega
    simp only [insert, List.cons_append, List.tail_cons, List.append_assoc, List.singleton_append,
      List.idxOf_append_of_notMem hn, List.idxOf_cons_self, Nat.add_zero, List.length_take]
    rw [highLength, Nat.min_eq_left (by omega : cut.val ≤ width - 1)]
  have insertSurjective (p : List ℕ) (hp : p ∈ failures) : ∃ cut, insert cut = p := by
    have splitP := parentSplit p hp.1
    have hnodup := hp.1.1.1.nodup_iff.mpr List.nodup_range'
    have notTwo := (List.nodup_cons.mp (splitP ▸ hnodup)).1
    have tailBounds (value : ℕ) (hv : value ∈ p.tail) : value = 1 ∨ 2 < value := by
      have hh := List.mem_range'_1.mp (hp.1.1.1.mem_iff.mp (List.mem_of_mem_tail hv))
      have hn : value ≠ 2 := fun he => notTwo (he ▸ hv)
      omega
    have lowerMem : 1 ∈ p.tail := by
      have hh := hp.1.1.1.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega : 1 ≤ 1 ∧ 1 < 1 + (width + 1)))
      rw [splitP] at hh
      simpa using hh
    obtain ⟨left, right, hsplit⟩ := List.append_of_mem lowerMem
    have hn := List.nodup_append.mp (hsplit ▸ (List.nodup_cons.mp (splitP ▸ hnodup)).2)
    have noOneLeft : 1 ∉ left := fun hv => hn.2.2 1 hv 1 (by simp) rfl
    have noOneRight : 1 ∉ right := (List.nodup_cons.mp hn.2.1).1
    have keep (part : List ℕ) (hs : part.Sublist p.tail) (hne : 1 ∉ part) :
        part.filter (fun value => decide (2 < value)) = part := by
      apply List.filter_eq_self.mpr
      intro value hv
      rcases tailBounds value (hs.subset hv) with he | hh
      · exact False.elim (hne (he ▸ hv))
      · simpa using hh
    have filterEq : upper p = left ++ right := by
      change p.tail.filter (fun value => decide (2 < value)) = _
      rw [hsplit, List.filter_append]
      rw [keep left (hsplit ▸ List.sublist_append_left _ _) noOneLeft]
      have sr : right.Sublist p.tail := hsplit ▸
        (List.sublist_cons_self 1 right).trans (List.sublist_append_right _ _)
      simp only [List.filter_cons, show decide (2 < (1 : ℕ)) = false from rfl,
        Bool.false_eq_true, if_false, keep right sr noOneRight]
    have upperPerm : (upper p).Perm (List.range' 3 (width - 1)) := by
      apply (List.perm_ext_iff_of_nodup
        (((List.nodup_cons.mp (splitP ▸ hnodup)).2).filter _) List.nodup_range').mpr
      intro value
      simp only [upper, List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
      constructor
      · rintro ⟨hv, hh⟩
        have hb := List.mem_range'_1.mp (hp.1.1.1.mem_iff.mp (List.mem_of_mem_tail hv)); omega
      · intro hh
        refine ⟨?_, by omega⟩
        have hv := hp.1.1.1.mem_iff.mpr
          (List.mem_range'_1.mpr (by omega : 1 ≤ value ∧ value < 1 + (width + 1)))
        rw [splitP] at hv
        exact (List.mem_cons.mp hv).resolve_left (by omega)
    have sorted : upper p = high :=
      (upperPerm.trans (List.reverse_perm _).symm).eq_of_pairwise
        (by intro a b hab hba; omega) hp.2 highDesc
    have joined : left ++ right = high := filterEq.symm.trans sorted
    have hl : left.length < width := by
      have hh := congrArg List.length joined
      simp only [List.length_append, highLength] at hh
      omega
    refine ⟨⟨left.length, hl⟩, ?_⟩
    have takeEq : high.take left.length = left := by rw [← joined, List.take_left]
    have dropEq : high.drop left.length = right := by rw [← joined, List.drop_left]
    simp only [insert, takeEq, dropEq, List.cons_append, List.append_assoc,
      List.singleton_append, List.nil_append]
    rw [← hsplit, ← splitP]
  have failuresCount : failures.ncard = width := by
    let f : Fin width → failures := fun cut => ⟨insert cut, insertMember cut⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b he
        apply Fin.ext
        have hh := congrArg (fun p : failures => p.val.tail.idxOf 1) he
        simpa only [f, insertDecode] using hh
      · rintro ⟨p, hp⟩
        obtain ⟨cut, he⟩ := insertSurjective p hp
        exact ⟨cut, Subtype.ext he⟩
    have hh := Nat.card_congr (Equiv.ofBijective f hf)
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using hh.symm
  let lift := fun value : ℕ => if value < 2 then value else value + 1
  let lower := fun value : ℕ => if value < 2 then value else value - 1
  have liftStrict : StrictMono lift := by
    intro a b hh; dsimp [lift]; split_ifs <;> omega
  have lowerLift (value : ℕ) : lower (lift value) = value := by
    dsimp [lower, lift]; split_ifs <;> omega
  let emit := fun p : List ℕ => 2 :: p.tail.map lift ++ [3]
  have liftRange : (List.range' 1 (width + 1)).map lift =
      1 :: List.range' 3 width := by
    rw [List.range'_succ, List.map_cons]
    simp only [lift, show (1 : ℕ) < 2 by omega, if_true]
    congr 1
    have he : (List.range' 2 width).map lift = (List.range' 2 width).map (1 + ·) := by
      apply List.map_congr_left
      intro value hv
      have hb := List.mem_range'_1.mp hv
      dsimp [lift]; split_ifs <;> omega
    rw [he, List.map_add_range']
  have emitPerm (p : List ℕ) (hp : p ∈ parents) :
      (emit p).Perm (List.range' 1 (width + 2)) := by
    have hm := hp.1.1.map lift
    rw [parentSplit p hp, List.map_cons, show lift 2 = 3 by rfl, liftRange] at hm
    have moved : (p.tail.map lift ++ [3]).Perm (3 :: p.tail.map lift) := by
      simpa using List.perm_middle (a := 3) (l₁ := p.tail.map lift) (l₂ := [])
    have ht := ((moved.trans hm).cons 2).trans (List.Perm.swap 1 2 (List.range' 3 width))
    have hr : List.range' 1 (width + 2) = 1 :: 2 :: List.range' 3 width := by
      rw [show width + 2 = (width + 1) + 1 by omega, List.range'_succ, List.range'_succ]
    simpa only [emit, hr, List.cons_append] using ht
  have emitCycles (p : List ℕ) (hp : p ∈ parents) :
      ∀ shift < 4, ¬ Occurs (q.rotate shift) (p.tail.map lift ++ [3]) := by
    have hg := rotatedGood p hp.1 1
    have ha := (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q (p.rotate 1)
      (by decide) hg.1).mp hg
    have mapped : (p.rotate 1).map lift = p.tail.map lift ++ [3] := by
      rw [parentSplit p hp]
      simp [List.rotate_cons_succ, lift]
    intro shift hs ho
    rw [← mapped] at ho
    have hr := (List.rotate_perm q shift).trans (by decide : q.Perm [1, 2, 3, 4])
    have hl : letters (q.rotate shift) = (q.rotate shift).length := by
      have hh : letters (q.rotate shift) = 4 := by simpa [letters] using hr.foldr_eq (f := max) 0
      simpa [q] using hh
    apply ha shift hs
    unfold Occurs at ho ⊢
    rw [hl] at ho ⊢
    exact (ArcherCyclicPadovanPatterns.contains_map_iff _ _ lift liftStrict).mp ho
  have targetIff (p : List ℕ) (hp : p ∈ parents) :
      Occurs q (emit p) ↔ ¬ (upper p).Pairwise (· > ·) := by
    constructor
    · intro ho hd
      have hc := (consecutive_endpoint_contraction (width + 2) 2 (p.tail.map lift) q
        (by omega) (Or.inr rfl) (emitPerm p hp)).mpr ⟨emitCycles p hp, ho⟩
      have test := (unique_bad_cut_iff (width + 2) (by omega) q (emit p)
        (by decide) (emitPerm p hp)).mp hc
      obtain ⟨chosen, hi, _, selected, _⟩ := ho
      change [chosen 1, chosen 3, chosen 4, chosen 2].Sublist
        (2 :: (p.tail.map lift ++ [3])) at selected
      have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
      have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
      have firstUsed : chosen 1 = 2 := by
        by_contra hn
        apply test.2.2.1
        refine ⟨chosen, hi, ?_, List.Sublist.of_cons_of_ne hn selected, by simp⟩
        intro rank hlo hhi
        apply (List.Sublist.of_cons_of_ne hn selected).subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have pair : [chosen 3, chosen 4].Sublist (p.tail.map lift) := by
        have ht : [chosen 3, chosen 4, chosen 2].Sublist (p.tail.map lift ++ [3]) :=
          selected.of_cons_cons
        have ht : [chosen 2, chosen 4, chosen 3].Sublist (3 :: (p.tail.map lift).reverse) := by
          simpa using ht.reverse
        simpa using ht.of_cons_cons.reverse
      have ht := pair.map lower
      have restored : (p.tail.map lift).map lower = p.tail := by
        simp [List.map_map, Function.comp_def, lowerLift]
      rw [restored] at ht
      have h3 : 2 < lower (chosen 3) := by dsimp [lower]; split_ifs <;> omega
      have h4 : 2 < lower (chosen 4) := by dsimp [lower]; split_ifs <;> omega
      have hf : [lower (chosen 3), lower (chosen 4)].Sublist (upper p) := by
        simpa [upper, h3, h4] using ht.filter (fun value => decide (2 < value))
      have hh := List.pairwise_iff_forall_sublist.mp hd hf
      dsimp [lower] at hh
      split_ifs at hh <;> omega
    · intro hd
      obtain ⟨low, highValue, pair, hh⟩ :
          ∃ low highValue, [low, highValue].Sublist (upper p) ∧ ¬ low > highValue := by
        simpa only [List.pairwise_iff_forall_sublist, not_forall, Classical.not_imp,
          exists_prop] using hd
      have hn := hp.1.1.nodup_iff.mpr List.nodup_range'
      have ht := pair.trans (List.filter_sublist (p := fun value => decide (2 < value)))
      have ht := ht.trans (List.tail_sublist p)
      have ne : low ≠ highValue := by simpa using (List.nodup_cons.mp (hn.sublist ht)).1
      have hl := of_decide_eq_true (List.mem_filter.mp (pair.subset (by simp : low ∈ _))).2
      have hhigh := of_decide_eq_true (List.mem_filter.mp (pair.subset (by simp : highValue ∈ _))).2
      let chosen := fun rank : ℕ => if rank = 1 then 2 else if rank = 2 then 3
        else if rank = 3 then lift low else lift highValue
      have liftLow : lift low = low + 1 := by
        dsimp [lift]; exact if_neg (by omega)
      have liftHigh : lift highValue = highValue + 1 := by
        dsimp [lift]; exact if_neg (by omega)
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank < 4 at hhi; omega
        rcases hc with rfl | rfl | rfl <;> simp [chosen, liftLow, liftHigh] <;> omega
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
        have hlow := (List.filter_sublist (p := fun value => decide (2 < value))).subset
          (pair.subset (by simp : low ∈ _))
        have hhigh := (List.filter_sublist (p := fun value => decide (2 < value))).subset
          (pair.subset (by simp : highValue ∈ _))
        rcases hc with rfl | rfl | rfl | rfl
        · simp [chosen, emit]
        · simp [chosen, emit]
        · change lift low ∈ 2 :: p.tail.map lift ++ [3]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hlow))
        · change lift highValue ∈ 2 :: p.tail.map lift ++ [3]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hhigh))
      · have ht := pair.trans (List.filter_sublist (p := fun value => decide (2 < value)))
        simpa [q, chosen, emit] using ((ht.map lift).append (List.Sublist.refl [3])).cons_cons 2
  have emitMember (p : List ℕ) (hp : p ∈ accepted) : emit p ∈ target := by
    have hd : ¬ (upper p).Pairwise (· > ·) := fun hh => hp.2 ⟨hp.1, hh⟩
    refine ⟨emitPerm p hp.1, by simp [emit], ?_, ?_⟩
    · change ((2 :: p.tail.map lift) ++ [3]).getLast? = some 3
      rw [List.getLast?_append_cons]; rfl
    · exact (consecutive_endpoint_contraction (width + 2) 2 (p.tail.map lift) q
        (by omega) (Or.inr rfl) (emitPerm p hp.1)).mpr
          ⟨emitCycles p hp.1, (targetIff p hp.1).mpr hd⟩
  have decode (p : List ℕ) (hp : p ∈ parents) :
      2 :: (emit p).tail.dropLast.map lower = p := by
    simp only [emit, List.cons_append, List.tail_cons, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil, List.map_map, Function.comp_def,
      lowerLift]
    simpa using (parentSplit p hp).symm
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ p ∈ accepted, emit p = word := by
    obtain ⟨front, lastEq⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, wordEq⟩ : ∃ interior, word = 2 :: interior ++ [3] := by
      cases front with
      | nil => have hh := hw.1.length_eq; simp [lastEq] at hh
      | cons head interior =>
        have hh : head = 2 := by simpa [lastEq] using hw.2.1
        exact ⟨interior, by simpa [hh] using lastEq⟩
    let p := 2 :: interior.map lower
    have notTwo : 2 ∉ interior := fun hv =>
      (List.nodup_cons.mp ((wordEq ▸ hw.1).nodup_iff.mpr List.nodup_range')).1
        (List.mem_append_left _ hv)
    have notThree : 3 ∉ interior := by
      have hn := List.nodup_append.mp
        (List.nodup_cons.mp ((wordEq ▸ hw.1).nodup_iff.mpr List.nodup_range')).2
      exact fun hv => hn.2.2 3 hv 3 (by simp) rfl
    have restore : (interior.map lower).map lift = interior := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hv
      have hn : value ≠ 2 := fun he => notTwo (he ▸ hv)
      have hn' : value ≠ 3 := fun he => notThree (he ▸ hv)
      dsimp [lift, lower]; split_ifs <;> omega
    have pPerm : p.Perm (List.range' 1 (width + 1)) := by
      have hr : List.range' 1 (width + 2) = 1 :: 2 :: List.range' 3 width := by
        rw [show width + 2 = (width + 1) + 1 by omega, List.range'_succ, List.range'_succ]
      have hh := wordEq ▸ hw.1
      rw [hr] at hh
      have hh := List.Perm.cons_inv (hh.trans (List.Perm.swap 2 1 (List.range' 3 width)))
      have move : (3 :: interior).Perm (interior ++ [3]) := by
        simpa using (List.perm_middle (a := 3) (l₁ := interior) (l₂ := [])).symm
      have hh := (move.trans hh).map lower
      rw [← liftRange, List.map_map] at hh
      simpa [List.map_cons, show lower 3 = 2 by rfl, Function.comp_def,
        lowerLift, p] using hh
    have hc := (consecutive_endpoint_contraction (width + 2) 2 interior q
      (by omega) (Or.inr rfl) (wordEq ▸ hw.1)).mp (wordEq ▸ hw.2.2.2)
    have hg : p ∈ rotationAvoiders (width + 1) (width + 1) q := by
      have mapped : (p.rotate 1).map lift = interior ++ [3] := by
        simp only [p, List.rotate_cons_succ, List.rotate_zero, List.map_append,
          List.map_singleton, show lift 2 = 3 by rfl, restore]
      have hrot := (List.rotate_perm p 1).trans pPerm
      have hrotGood := (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q (p.rotate 1)
        (by decide) hrot).mpr (by
          intro shift hs ho
          apply hc.1 shift hs
          rw [← mapped]
          have hr := (List.rotate_perm q shift).trans (by decide : q.Perm [1, 2, 3, 4])
          have hl : letters (q.rotate shift) = (q.rotate shift).length := by
            have hh : letters (q.rotate shift) = 4 := by
              simpa [letters] using hr.foldr_eq (f := max) 0
            simpa [q] using hh
          unfold Occurs at ho ⊢
          rw [hl] at ho ⊢
          exact (ArcherCyclicPadovanPatterns.contains_map_iff _ _ lift liftStrict).mpr ho)
      have back := rotatedGood (p.rotate 1) hrotGood width
      have lengthP : p.length = width + 1 := by simpa using pPerm.length_eq
      have he : (p.rotate 1).rotate width = p := by
        rw [List.rotate_rotate, show 1 + width = p.length by omega, List.rotate_length]
      exact he ▸ back
    have hp : p ∈ parents := ⟨hg, by simp [p]⟩
    have he : emit p = word := by simp only [emit, p, List.tail_cons, restore, ← wordEq]
    have notFail : p ∉ failures := by
      rintro ⟨_, hd⟩
      exact (targetIff p hp).mp (he.symm ▸ (wordEq.symm ▸ hc.2)) hd
    exact ⟨p, ⟨hp, notFail⟩, he⟩
  have cardTarget := Set.ncard_congr (s := accepted) (t := target) (fun p _ => emit p)
    emitMember (by
      intro p r hp hr he
      have hh := congrArg (fun word : List ℕ => 2 :: word.tail.dropLast.map lower) he
      rwa [decode p hp.1, decode r hr.1] at hh) (by
      intro word hw
      obtain ⟨p, hp, he⟩ := emitSurjective word hw
      exact ⟨p, hp, he⟩)
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 (width + 1)).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1.1
  have subsetFailures : failures ⊆ parents := fun _ hp => hp.1
  have rejected := Set.ncard_sdiff_add_ncard_of_subset subsetFailures finiteParents
  have rooted_count (q : List ℕ) (patterns : List (List ℕ))
      (hletters : ∀ pattern ∈ patterns, letters pattern = pattern.length)
      (hreduction : ∀ tail, (1 :: tail).Perm (List.range' 1 (width + 1)) →
        ((1 :: tail) ∈ circularAvoiders (width + 1) q ↔
          ∀ pattern ∈ patterns, ¬ Occurs pattern tail)) :
      (circularAvoiders (width + 1) q).ncard =
        (Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns).ncard := by
    let emit := fun word : List ℕ => 1 :: word.map Nat.succ
    have shift (pattern word : List ℕ) (hpattern : pattern ∈ patterns) :
        Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
      unfold Occurs
      rw [hletters pattern hpattern]
      exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
        (by intro low high hlt; omega)
    have emitPerm (word : List ℕ) (hword : word.Perm (List.range' 1 width)) :
        (emit word).Perm (List.range' 1 (width + 1)) := by
      have hrange : (List.range' 1 width).map Nat.succ = List.range' 2 width := by
        simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
          funext value; omega, Nat.reduceAdd] using
          List.map_add_range' (a := 1) 1 width 1
      simpa only [emit, hrange, List.range'_succ, Nat.reduceAdd, Nat.mul_one] using
        (hword.map Nat.succ).cons 1
    have emitMember (word : List ℕ)
        (hword : word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns) :
        emit word ∈ circularAvoiders (width + 1) q := by
      apply (hreduction _ (emitPerm word hword.1)).mpr
      intro pattern hpattern
      exact fun hocc => hword.2 pattern hpattern ((shift pattern word hpattern).mp hocc)
    have emitInjective : Function.Injective emit := by
      intro first second heq
      exact List.map_injective_iff.mpr Nat.succ_injective (List.cons.inj heq).2
    have emitSurjective (circle : List ℕ)
        (hcircle : circle ∈ circularAvoiders (width + 1) q) :
        ∃ word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns,
          emit word = circle := by
      obtain ⟨tail, rfl⟩ : ∃ tail, circle = 1 :: tail := by
        cases circle with
        | nil => simp [circularAvoiders] at hcircle
        | cons head tail =>
          have hhead : head = 1 := by simpa using hcircle.2
          exact ⟨tail, by simp [hhead]⟩
      have htailPerm : tail.Perm (List.range' 2 width) := by
        have hp := hcircle.1.1
        rw [List.range'_succ] at hp
        exact List.Perm.cons_inv hp
      let word := tail.map (· - 1)
      have restore : word.map Nat.succ = tail := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id tail]
        apply List.map_congr_left
        intro value hvalue
        have := List.mem_range'.mp (htailPerm.mem_iff.mp hvalue)
        dsimp
        omega
      have wordPerm : word.Perm (List.range' 1 width) := by
        have hp := htailPerm.map (fun value => value - 1)
        simpa only [word, List.map_sub_range' (by omega : 1 ≤ 2), Nat.reduceSub] using hp
      have tailAvoid := (hreduction tail hcircle.1.1).mp hcircle
      refine ⟨word, ⟨wordPerm, ?_⟩, by simp only [emit, restore]⟩
      intro pattern hpattern hocc
      exact tailAvoid pattern hpattern
        (restore ▸ (shift pattern word hpattern).mpr hocc)
    exact (Set.ncard_congr (fun word _ => emit word) emitMember
      (fun first second _ _ heq => emitInjective heq) (by
        intro circle hcircle
        obtain ⟨word, hword, heq⟩ := emitSurjective circle hcircle
        exact ⟨word, hword, heq⟩)).symm
  have count : (circularAvoiders (width + 1) [1, 3, 4, 2]).ncard = 2 ^ width - width := by
    rw [rooted_count [1, 3, 4, 2] [[2, 3, 1], [2, 1, 3, 4], [4, 2, 1, 3]] (by
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl <;> rfl) (by
        intro tail hp
        simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] using (RotationAvoidanceCounts.minimum_rooted_reductions width tail hp).2.1)]
    exact RotationAvoidanceLinear.binary_separator_count width
  change (circularAvoiders (width + 1) q).ncard = 2 ^ width - width at count
  change accepted.ncard + failures.ncard = parents.ncard at rejected
  rw [failuresCount, parentsCount, count] at rejected
  change target.ncard = _
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMarkedContraction
