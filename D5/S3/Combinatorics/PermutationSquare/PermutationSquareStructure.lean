/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareStructure
   mirror-E: none(waiver:permutation-square-component-structure)
   anchors: []
   utility: none
   digest: Pattern witnesses constrain indecomposable components and direct-sum squares. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareDefs
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareStructure

open D5.S3.Combinatorics Nonnesting
open NonnestingBasicSum PermutationSquareDefs

theorem component_ends_one (p : List ℕ) (hp : p ≠ [])
    (hperm : p.Perm (List.range' 1 p.length)) (hindecomp : sumIndecomposable p)
    (havoid : ¬ NonnestingDefs.Occurs [3, 1, 2] p) : p.getLast? = some 1 := by
  have hbound (value : ℕ) (hv : value ∈ p) : 1 ≤ value := by
    have hr := hperm.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, _, heq⟩ := hr
    omega
  have hone : 1 ∈ p := by
    apply hperm.mem_iff.mpr
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp
    simp only [List.mem_range', Nat.one_mul]
    exact ⟨0, hlen, by omega⟩
  obtain ⟨before, after, heq, _⟩ := List.eq_append_cons_of_mem hone
  by_cases hafter : after = []
  · subst after
    simp [heq]
  · have hcut : before.length + 1 < p.length := by
      rw [heq]
      simp only [List.length_append, List.length_cons]
      have := List.length_pos_iff.mpr hafter
      omega
    obtain ⟨first, last, hle⟩ :=
      hindecomp ⟨before.length + 1, hcut⟩ (Nat.zero_lt_succ _)
    have htake : p.take (before.length + 1) = before ++ [1] := by
      rw [heq]
      simp [List.take_append, List.take_of_length_le (by omega :
        before.length ≤ before.length + 1)]
    have hdrop : p.drop (before.length + 1) = after := by
      simp [heq, List.drop_append]
    have hfirst : (p.take (before.length + 1)).get first ∈ before ++ [1] := by
      rw [← htake]
      exact List.get_mem _ first
    have hlast : (p.drop (before.length + 1)).get last ∈ after := by
      rw [← hdrop]
      exact List.get_mem _ last
    let low := (p.drop (before.length + 1)).get last
    let high := (p.take (before.length + 1)).get first
    change low ≤ high at hle
    change high ∈ before ++ [1] at hfirst
    change low ∈ after at hlast
    have hlowmem : low ∈ p := by
      rw [heq]
      exact List.mem_append_right before (List.mem_cons_of_mem 1 hlast)
    have hlow : 1 < low := by
      have hpositive := hbound low hlowmem
      have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
      rw [heq, List.nodup_append] at hnodup
      have hne : low ≠ 1 := by
        intro hequal
        have : 1 ∈ after := hequal ▸ hlast
        exact (List.nodup_cons.mp hnodup.2.1).1 this
      omega
    have hhigh : high ∈ before := by
      rcases List.mem_append.mp hfirst with hbefore | hone
      · exact hbefore
      · simp only [List.mem_singleton] at hone
        omega
    have hneq : low ≠ high := by
      have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
      rw [heq, List.nodup_append] at hnodup
      intro hequal
      exact hnodup.2.2 high hhigh low (List.mem_cons_of_mem _ hlast) hequal.symm
    have hstrict : low < high := by
      omega
    exfalso
    apply havoid
    let values : ℕ → ℕ := fun rank => if rank = 1 then 1 else if rank = 2 then low else high
    refine ⟨values, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hranklt
      change rank < 3 at hranklt
      have : rank = 1 ∨ rank = 2 := by omega
      rcases this with rfl | rfl <;> simp [values, hlow, hstrict]
    · intro rank hrank hrankle
      change rank ≤ 3 at hrankle
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl
      · simpa [values] using hone
      · simpa [values] using (show low ∈ p by rw [heq]; simp [hlast])
      · simpa [values] using (show high ∈ p by rw [heq]; simp [hhigh])
    · change [high, 1, low].Sublist p
      rw [heq]
      exact (List.singleton_sublist.mpr hhigh).append
        (List.Sublist.cons_cons 1 (List.singleton_sublist.mpr hlast))

theorem square_tail_identity (m n : ℕ) (left right : List ℕ)
    (hleft : left.Perm (List.range' 1 m)) (hright : right.Perm (List.range' 1 n))
    (hpositive : 0 < m) :
    square (directSum m left right) = directSum m (square left) (square right) ∧
      (¬ NonnestingDefs.Occurs [1, 3, 2] (square (directSum m left right)) →
        square right = List.range' 1 n) := by
  have hbounds (size : ℕ) (word : List ℕ) (hw : word.Perm (List.range' 1 size))
      (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hr := hw.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
    omega
  have hsquareperm (size : ℕ) (word : List ℕ)
      (hw : word.Perm (List.range' 1 size)) :
      (square word).Perm (List.range' 1 size) := by
    have hlength : word.length = size := by simpa using hw.length_eq
    have hmap : (List.range' 1 size).map (fun value => word.getD (value - 1) 0) =
        word := by
      apply List.ext_getElem (by simp [hlength])
      intro index hindex hword
      simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
      have hindexeq : 1 + index - 1 = index := by omega
      rw [hindexeq]
      exact List.getD_eq_getElem word 0 hword
    have hmapped := hw.map (fun value => word.getD (value - 1) 0)
    rw [hmap] at hmapped
    exact hmapped.trans hw
  have hlength : left.length = m := by simpa using hleft.length_eq
  have hrlength : right.length = n := by simpa using hright.length_eq
  have hsum : square (directSum m left right) =
      directSum m (square left) (square right) := by
    unfold square directSum shift
    simp only [List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro value hvalue
      have hb := hbounds m left hleft value hvalue
      exact List.getD_append _ _ _ _ (by omega)
    · apply List.map_congr_left
      intro value hvalue
      have hb := hbounds n right hright value hvalue
      change (left ++ right.map (fun entry => entry + m)).getD (value + m - 1) 0 =
        right.getD (value - 1) 0 + m
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hindex : value + m - 1 - left.length = value - 1 := by omega
      rw [hindex, List.getD_eq_getElem _ 0 (by simp; omega),
        List.getD_eq_getElem right 0 (by omega)]
      simp
  refine ⟨hsum, ?_⟩
  intro havoid
  rw [hsum] at havoid
  have hleftsq := hsquareperm m left hleft
  have hrightsq := hsquareperm n right hright
  have hsqlength : (square left).length = m := by simpa using hleftsq.length_eq
  let small := (square left).get ⟨0, by omega⟩
  have hsmallmem : small ∈ square left := List.get_mem _ _
  have hsmallbound := hbounds m (square left) hleftsq small hsmallmem
  have hsorted : (square right).Pairwise (· ≤ ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro high low hpair
    by_contra hle
    have hlmem : low ∈ square right := hpair.subset (by simp)
    have hlowbound := hbounds n (square right) hrightsq low hlmem
    have hstrict : low < high := by omega
    have htriple : [small, high + m, low + m].Sublist
        (directSum m (square left) (square right)) := by
      exact (List.singleton_sublist.mpr hsmallmem).append (hpair.map (fun value =>
        value + m))
    apply havoid
    let values : ℕ → ℕ := fun rank =>
      if rank = 1 then small else if rank = 2 then low + m else high + m
    refine ⟨values, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hranklt
      change rank < 3 at hranklt
      have : rank = 1 ∨ rank = 2 := by omega
      rcases this with rfl | rfl
      · change small < low + m
        omega
      · change low + m < high + m
        omega
    · intro rank hrank hrankle
      change rank ≤ 3 at hrankle
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      apply htriple.subset
      rcases this with rfl | rfl | rfl <;> simp [values]
    · exact htriple
  exact List.Perm.eq_of_sortedLE hsorted.sortedLE (List.sortedLE_range' 1 n 1) hrightsq

theorem component_involution_decreasing (p : List ℕ) (hp : p ≠ [])
    (hperm : p.Perm (List.range' 1 p.length)) (hindecomp : sumIndecomposable p)
    (havoid : ¬ NonnestingDefs.Occurs [3, 1, 2] p)
    (hinvolution : square p = List.range' 1 p.length) :
    p = (List.range' 1 p.length).reverse := by
  have hend := component_ends_one p hp hperm hindecomp havoid
  obtain ⟨initial, heq⟩ := List.getLast?_eq_some_iff.mp hend
  have hfirst : p.getD 0 0 = p.length := by
    have hlast := congrArg List.getLast? hinvolution
    simp only [square, heq, List.map_append, List.map_cons, List.map_nil,
      Nat.sub_self, List.getLast?_append, List.getLast?_singleton,
      List.getLast?_range', List.length_append, List.length_singleton] at hlast
    simpa [heq] using hlast
  have hbounds (value : ℕ) (hv : value ∈ p) : value ≤ p.length := by
    have hr := hperm.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
    omega
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hdecreasing : p.Pairwise (fun high low => low ≤ high) := by
    cases p with
    | nil => contradiction
    | cons first rest =>
      have hmax : first = (first :: rest).length := by simpa using hfirst
      apply List.pairwise_cons.mpr
      refine ⟨?_, ?_⟩
      · intro value hv
        have := hbounds value (List.mem_cons_of_mem first hv)
        omega
      · apply List.pairwise_iff_forall_sublist.mpr
        intro high low hpair
        by_contra hle
        have hlowmem : low ∈ rest := hpair.subset (by simp)
        have hbound := hbounds low (List.mem_cons_of_mem first hlowmem)
        have hne : low ≠ first := by
          intro hequal
          exact (List.nodup_cons.mp hnodup).1 (hequal ▸ hlowmem)
        have hstrict : high < low ∧ low < first := by omega
        have htriple : [first, high, low].Sublist (first :: rest) :=
          List.Sublist.cons_cons first hpair
        apply havoid
        let values : ℕ → ℕ := fun rank =>
          if rank = 1 then high else if rank = 2 then low else first
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hrank hranklt
          change rank < 3 at hranklt
          have : rank = 1 ∨ rank = 2 := by omega
          rcases this with rfl | rfl
          · exact hstrict.1
          · exact hstrict.2
        · intro rank hrank hrankle
          change rank ≤ 3 at hrankle
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          apply htriple.subset
          rcases this with rfl | rfl | rfl <;> simp [values]
        · exact htriple
  have hreverse := List.Perm.eq_of_sortedLE hdecreasing.reverse.sortedLE
    (List.sortedLE_range' 1 p.length 1) ((List.reverse_perm p).trans hperm)
  simpa using congrArg List.reverse hreverse

theorem avoider_layered_tail (n : ℕ) (p : List ℕ) (hn : 0 < n)
    (hp : p ∈ avoiders n) :
    ∃ first : List ℕ, ∃ tail : List (List ℕ),
      p = directSum first.length first
        (FishburnTenThirteen.FishburnBasicComponents.assemble tail) ∧
      first ≠ [] ∧ first ∈ avoiders first.length ∧ sumIndecomposable first ∧
      ∀ block ∈ tail, block ≠ [] ∧ block = (List.range' 1 block.length).reverse ∧
        block.length ≤ 4 := by
  classical
  let assemble := FishburnTenThirteen.FishburnBasicComponents.assemble
  have hbounds (word : List ℕ) (hw : word.Perm (List.range' 1 word.length))
      (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ word.length := by
    have hr := hw.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
    omega
  have hassemble (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
      (assemble parts).Perm (List.range' 1 (assemble parts).length) := by
    induction parts with
    | nil => simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble]
    | cons block rest ih =>
      have hb := hparts block (by simp)
      have ht := ih (fun item hi => hparts item (by simp [hi]))
      have hshift : (shift block.length (assemble rest)).Perm
          (List.range' (1 + block.length) (assemble rest).length) := by
        have hmapped := ht.map (fun value => block.length + value)
        rw [List.map_add_range'] at hmapped
        simpa only [shift, Nat.add_comm] using hmapped
      have hadd := hb.append hshift
      simpa [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble,
        directSum, shift] using hadd
  have hlocal (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block.Perm (List.range' 1 block.length))
      (pattern : List ℕ) (hpattern : sumIndecomposable pattern)
      (hpositive : ∀ value ∈ pattern, 1 ≤ value)
      (hfull : ∀ rank, 1 ≤ rank →
        rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern)
      (havoid : ¬ NonnestingDefs.Occurs pattern (assemble parts)) :
      ∀ block ∈ parts, ¬ NonnestingDefs.Occurs pattern block := by
    induction parts with
    | nil => simp
    | cons block rest ih =>
      have hb := hparts block (by simp)
      have ht := hassemble rest (fun item hi => hparts item (by simp [hi]))
      have hiff := occurs_directSum_iff block.length block (assemble rest) pattern
        (fun value hv => (hbounds block hb value hv).2)
        (fun value hv => (hbounds (assemble rest) ht value hv).1)
        hpattern hpositive hfull
      have hnone : ¬ NonnestingDefs.Occurs pattern block ∧
          ¬ NonnestingDefs.Occurs pattern (assemble rest) := by
        simpa only [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble,
          hiff, not_or] using havoid
      intro item hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hnone.1
      · exact ih (fun item hi => hparts item (by simp [hi])) hnone.2 item hi
  have h312 : sumIndecomposable [3, 1, 2] := by unfold sumIndecomposable; decide
  have h54321 : sumIndecomposable [5, 4, 3, 2, 1] := by
    unfold sumIndecomposable
    decide
  have hpos312 : ∀ value ∈ [3, 1, 2], 1 ≤ value := by simp
  have hpos54321 : ∀ value ∈ [5, 4, 3, 2, 1], 1 ≤ value := by simp
  have hfull312 : ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters [3, 1, 2] →
      rank ∈ [3, 1, 2] := by
    intro rank hlow hhigh
    change rank ≤ 3 at hhigh
    simp
    omega
  have hfull54321 : ∀ rank, 1 ≤ rank →
      rank ≤ NonnestingDefs.letters [5, 4, 3, 2, 1] → rank ∈ [5, 4, 3, 2, 1] := by
    intro rank hlow hhigh
    change rank ≤ 5 at hhigh
    simp
    omega
  have hidavoid (size : ℕ) : ¬ NonnestingDefs.Occurs [1, 3, 2] (List.range' 1 size) := by
    rintro ⟨values, hmono, _, hsub, _⟩
    have hpair : [values 3, values 2].Sublist (List.range' 1 size) :=
      (List.sublist_cons_self (values 1) _).trans hsub
    have hlt := (List.pairwise_lt_range' 1 (by simp) :
      (List.range' 1 size).Pairwise (· < ·)).forall_sublist hpair
    have hgt : values 2 < values 3 := by
      simpa using hmono 2 (by omega) (by change 2 < 3; omega)
    omega
  have hlayers (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block)
      (hsquare : square (assemble parts) = List.range' 1 (assemble parts).length)
      (hav312 : ∀ block ∈ parts, ¬ NonnestingDefs.Occurs [3, 1, 2] block)
      (hav54321 : ∀ block ∈ parts, ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] block) :
      ∀ block ∈ parts, block ≠ [] ∧ block = (List.range' 1 block.length).reverse ∧
        block.length ≤ 4 := by
    induction parts with
    | nil => simp
    | cons block rest ih =>
      have hb := hparts block (by simp)
      have hrest := fun item hi => hparts item (List.mem_cons_of_mem block hi)
      have ht := hassemble rest (fun item hi => (hrest item hi).2.1)
      have hsqavoid : ¬ NonnestingDefs.Occurs [1, 3, 2]
          (square (directSum block.length block (assemble rest))) := by
        change ¬ NonnestingDefs.Occurs [1, 3, 2] (square (assemble (block :: rest)))
        rw [hsquare]
        exact hidavoid _
      have hsplit := square_tail_identity block.length (assemble rest).length block
        (assemble rest) hb.2.1 ht (List.length_pos_iff.mpr hb.1)
      have hblock : square block = List.range' 1 block.length := by
        have heq := congrArg (List.take block.length) hsplit.1
        change (square (assemble (block :: rest))).take block.length = _ at heq
        rw [hsquare] at heq
        have hlen : (square block).length = block.length := by simp [square]
        have htotal : block.length ≤ (assemble (block :: rest)).length := by
          simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble,
            directSum, shift]
        rw [List.take_range'_of_length_ge htotal] at heq
        simpa [directSum, List.take_append, hlen] using heq.symm
      have hdecreasing := component_involution_decreasing block hb.1 hb.2.1 hb.2.2
        (hav312 block (by simp)) hblock
      have hsmall : block.length ≤ 4 := by
        by_contra hlarge
        have hbase : (List.range' 1 5).Sublist (List.range' 1 block.length) :=
          List.range'_sublist_right.mpr (by omega)
        have hsub : [5, 4, 3, 2, 1].Sublist block := by
          rw [hdecreasing]
          exact hbase.reverse
        apply hav54321 block (by simp)
        refine ⟨id, ?_, ?_, hsub, by simp⟩
        · intro rank hlow hhigh
          simp
        · intro rank hlow hhigh
          exact hsub.subset (hfull54321 rank hlow hhigh)
      intro item hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨hb.1, hdecreasing, hsmall⟩
      · exact ih hrest (hsplit.2 hsqavoid)
          (fun item hi => hav312 item (List.mem_cons_of_mem block hi))
          (fun item hi => hav54321 item (List.mem_cons_of_mem block hi)) item hi
  obtain ⟨parts, ⟨hassembleeq, hparts, _⟩, _⟩ :=
    (FishburnTenThirteen.FishburnBasicComponents.unique_sum_components n p hp.1 []
      (by simp)).1
  have hnonempty : parts ≠ [] := by
    intro heq
    subst parts
    have hlength := hp.1.length_eq
    have hpempty : p = [] := by
      simpa only [FishburnTenThirteen.FishburnBasicComponents.assemble] using hassembleeq.symm
    rw [hpempty] at hlength
    simp at hlength
    omega
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
  have hfirst := hparts first (by simp)
  have htail := fun item hi => hparts item (List.mem_cons_of_mem first hi)
  have hperms := fun item hi => (hparts item hi).2.1
  have hglobal312 : ¬ NonnestingDefs.Occurs [3, 1, 2] (assemble (first :: tail)) := by
    change ¬ NonnestingDefs.Occurs [3, 1, 2]
      (FishburnTenThirteen.FishburnBasicComponents.assemble (first :: tail))
    rw [hassembleeq]
    exact hp.2.1
  have hav312 := hlocal (first :: tail) hperms [3, 1, 2] h312 hpos312 hfull312 hglobal312
  have hglobal54321 : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1]
      (assemble (first :: tail)) := by
    change ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1]
      (FishburnTenThirteen.FishburnBasicComponents.assemble (first :: tail))
    rw [hassembleeq]
    exact hp.2.2.1
  have hav54321 := hlocal (first :: tail) hperms [5, 4, 3, 2, 1] h54321
    hpos54321 hfull54321 hglobal54321
  have ht := hassemble tail (fun item hi => (htail item hi).2.1)
  have hsqavoid : ¬ NonnestingDefs.Occurs [1, 3, 2]
      (square (directSum first.length first (assemble tail))) := by
    change ¬ NonnestingDefs.Occurs [1, 3, 2]
      (square (FishburnTenThirteen.FishburnBasicComponents.assemble (first :: tail)))
    rw [hassembleeq]
    exact hp.2.2.2
  have hsplit := square_tail_identity first.length (assemble tail).length first
    (assemble tail) hfirst.2.1 ht (List.length_pos_iff.mpr hfirst.1)
  have htailidentity := hsplit.2 hsqavoid
  have hfirstsq : ¬ NonnestingDefs.Occurs [1, 3, 2] (square first) := by
    rw [hsplit.1] at hsqavoid
    rintro ⟨values, hmono, hmem, hsub, _⟩
    apply hsqavoid
    refine ⟨values, hmono, ?_, hsub.trans (List.sublist_append_left _ _), by simp⟩
    intro rank hlow hhigh
    exact List.mem_append_left _ (hmem rank hlow hhigh)
  refine ⟨first, tail, hassembleeq.symm, hfirst.1,
    ⟨hfirst.2.1, hav312 first (by simp), hav54321 first (by simp), hfirstsq⟩,
    hfirst.2.2, ?_⟩
  exact hlayers tail htail htailidentity
    (fun item hi => hav312 item (List.mem_cons_of_mem first hi))
    (fun item hi => hav54321 item (List.mem_cons_of_mem first hi))

theorem admissible_layered_tail (first : List ℕ) (tail : List (List ℕ))
    (hfirst : first ≠ []) (hadmissible : first ∈ avoiders first.length)
    (htail : ∀ block ∈ tail, block ≠ [] ∧
      block = (List.range' 1 block.length).reverse ∧ block.length ≤ 4) :
    let word := directSum first.length first
      (FishburnTenThirteen.FishburnBasicComponents.assemble tail)
    word ∈ avoiders word.length := by
  let assemble := FishburnTenThirteen.FishburnBasicComponents.assemble
  have hbounds (word : List ℕ) (hw : word.Perm (List.range' 1 word.length))
      (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ word.length := by
    have hr := hw.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
    omega
  have hsumperm (left right : List ℕ)
      (hl : left.Perm (List.range' 1 left.length))
      (hr : right.Perm (List.range' 1 right.length)) :
      (directSum left.length left right).Perm
        (List.range' 1 (directSum left.length left right).length) := by
    have hmapped := hr.map (fun value => left.length + value)
    rw [List.map_add_range'] at hmapped
    have hshift : (shift left.length right).Perm
        (List.range' (1 + left.length) right.length) := by
      simpa only [shift, Nat.add_comm] using hmapped
    simpa [directSum, shift] using hl.append hshift
  have h312 : sumIndecomposable [3, 1, 2] := by unfold sumIndecomposable; decide
  have h54321 : sumIndecomposable [5, 4, 3, 2, 1] := by
    unfold sumIndecomposable
    decide
  have hfull312 : ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters [3, 1, 2] →
      rank ∈ [3, 1, 2] := by
    intro rank hlow hhigh
    change rank ≤ 3 at hhigh
    simp
    omega
  have hfull54321 : ∀ rank, 1 ≤ rank →
      rank ≤ NonnestingDefs.letters [5, 4, 3, 2, 1] → rank ∈ [5, 4, 3, 2, 1] := by
    intro rank hlow hhigh
    change rank ≤ 5 at hhigh
    simp
    omega
  have hblock (block : List ℕ) (hb : block = (List.range' 1 block.length).reverse)
      (hsmall : block.length ≤ 4) : block ∈ avoiders block.length ∧
      square block = List.range' 1 block.length := by
    have hperm : block.Perm (List.range' 1 block.length) := by
      exact (List.Perm.of_eq hb).trans (List.reverse_perm _)
    have hdescending : block.Pairwise (fun high low => low < high) := by
      rw [hb]
      exact (List.pairwise_lt_range' 1 (by simp)).reverse
    have havoid312 : ¬ NonnestingDefs.Occurs [3, 1, 2] block := by
      rintro ⟨values, hmono, _, hsub, _⟩
      have hpair : [values 1, values 2].Sublist block :=
        (List.sublist_cons_self (values 3) _).trans hsub
      have hlt := hdescending.forall_sublist hpair
      have hgt : values 1 < values 2 := by
        simpa using hmono 1 (by omega) (by change 1 < 3; omega)
      omega
    have havoid54321 : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] block := by
      rintro ⟨_, _, _, hsub, _⟩
      have hlength := hsub.length_le
      simp only [List.length_map, List.length_cons, List.length_nil] at hlength
      omega
    have hentry (index : ℕ) (hindex : index < block.length) :
        block.getD index 0 = block.length - index := by
      have hbindex := congrArg (fun word => word.getD index 0) hb
      rw [hbindex, List.getD_eq_getElem _ 0 (by
        simp only [List.length_reverse, List.length_range']
        exact hindex)]
      simp only [List.getElem_reverse, List.getElem_range', List.length_range', Nat.one_mul]
      omega
    have hsquare : square block = List.range' 1 block.length := by
      apply List.ext_getElem (by simp [square])
      intro index hindex hrange
      have hi : index < block.length := by simpa [square] using hindex
      simp only [square, List.getElem_map, List.getElem_range', Nat.one_mul]
      rw [← List.getD_eq_getElem block 0 hi, hentry index hi,
        hentry (block.length - index - 1) (by omega)]
      omega
    have havoid132 : ¬ NonnestingDefs.Occurs [1, 3, 2] (square block) := by
      rw [hsquare]
      rintro ⟨values, hmono, _, hsub, _⟩
      have hpair : [values 3, values 2].Sublist (List.range' 1 block.length) :=
        (List.sublist_cons_self (values 1) _).trans hsub
      have hlt := (List.pairwise_lt_range' 1 (by simp)).forall_sublist hpair
      have hgt : values 2 < values 3 := by
        simpa using hmono 2 (by omega) (by change 2 < 3; omega)
      omega
    exact ⟨⟨hperm, havoid312, havoid54321, havoid132⟩, hsquare⟩
  have htailclass (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block ≠ [] ∧
        block = (List.range' 1 block.length).reverse ∧ block.length ≤ 4) :
      (assemble parts).Perm (List.range' 1 (assemble parts).length) ∧
      ¬ NonnestingDefs.Occurs [3, 1, 2] (assemble parts) ∧
      ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] (assemble parts) ∧
      square (assemble parts) = List.range' 1 (assemble parts).length := by
    induction parts with
    | nil =>
      simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble,
        square, NonnestingDefs.Occurs, ArrowWilfDefs.Contains]
    | cons block rest ih =>
      have hb := hparts block (by simp)
      have hbc := hblock block hb.2.1 hb.2.2
      have hrc := ih (fun item hi => hparts item (List.mem_cons_of_mem block hi))
      have hl : ∀ value ∈ block, value ≤ block.length :=
        fun value hv => (hbounds block hbc.1.1 value hv).2
      have hr : ∀ value ∈ assemble rest, 1 ≤ value :=
        fun value hv => (hbounds (assemble rest) hrc.1 value hv).1
      have hsquare := (square_tail_identity block.length (assemble rest).length
        block (assemble rest) hbc.1.1 hrc.1 (List.length_pos_iff.mpr hb.1)).1
      change (directSum block.length block (assemble rest)).Perm _ ∧
        ¬ NonnestingDefs.Occurs [3, 1, 2] (directSum block.length block (assemble rest)) ∧
        ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1]
          (directSum block.length block (assemble rest)) ∧
        square (directSum block.length block (assemble rest)) = _
      refine ⟨hsumperm block (assemble rest) hbc.1.1 hrc.1, ?_, ?_, ?_⟩
      · rw [occurs_directSum_iff block.length block (assemble rest) [3, 1, 2]
          hl hr h312 (by simp) hfull312]
        exact not_or.mpr ⟨hbc.1.2.1, hrc.2.1⟩
      · rw [occurs_directSum_iff block.length block (assemble rest) [5, 4, 3, 2, 1]
          hl hr h54321 (by simp) hfull54321]
        exact not_or.mpr ⟨hbc.1.2.2.1, hrc.2.2.1⟩
      · rw [hsquare, hbc.2, hrc.2.2.2]
        simp only [directSum, shift]
        have hmap := List.map_add_range' (a := block.length) 1 (assemble rest).length 1
        have hshift : (List.range' 1 (assemble rest).length).map (fun value =>
            value + block.length) = List.range' (1 + block.length) (assemble rest).length := by
          simpa only [Nat.add_comm] using hmap
        rw [hshift, List.range'_append_1]
        simp [assemble, FishburnTenThirteen.FishburnBasicComponents.assemble, directSum, shift]
  have htc := htailclass tail htail
  have hleft : ∀ value ∈ first, value ≤ first.length :=
    fun value hv => (hbounds first hadmissible.1 value hv).2
  have hright : ∀ value ∈ assemble tail, 1 ≤ value :=
    fun value hv => (hbounds (assemble tail) htc.1 value hv).1
  change directSum first.length first (assemble tail) ∈ _
  refine ⟨hsumperm first (assemble tail) hadmissible.1 htc.1, ?_, ?_, ?_⟩
  · rw [occurs_directSum_iff first.length first (assemble tail) [3, 1, 2]
      hleft hright h312 (by simp) hfull312]
    exact not_or.mpr ⟨hadmissible.2.1, htc.2.1⟩
  · rw [occurs_directSum_iff first.length first (assemble tail) [5, 4, 3, 2, 1]
      hleft hright h54321 (by simp) hfull54321]
    exact not_or.mpr ⟨hadmissible.2.2.1, htc.2.2.1⟩
  · rw [(square_tail_identity first.length (assemble tail).length first (assemble tail)
      hadmissible.1 htc.1 (List.length_pos_iff.mpr hfirst)).1, htc.2.2.2]
    let word := directSum first.length (square first) (List.range' 1 (assemble tail).length)
    have hsqlength : (square first).length = first.length := by simp [square]
    have hprefix (value : ℕ) (hv : value ∈ square first) : value ≤ first.length := by
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hv
      have hb := hbounds first hadmissible.1 source hs
      have hi : source - 1 < first.length := by omega
      rw [List.getD_eq_getElem first 0 hi]
      exact hleft _ (List.getElem_mem hi)
    have hsuffix (index : ℕ) (hlo : first.length ≤ index) (hi : index < word.length) :
        word.getD index 0 = index + 1 := by
      change (square first ++ shift first.length (List.range' 1 (assemble tail).length)).getD
        index 0 = _
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hindex : index - (square first).length < (assemble tail).length := by
        simp only [word, directSum, shift, List.length_append, List.length_map,
          List.length_range', hsqlength] at hi
        omega
      rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hindex)]
      simp only [shift, List.getElem_map, List.getElem_range', Nat.one_mul]
      omega
    rintro ⟨values, hmono, _, hsub, _⟩
    change [values 1, values 3, values 2].Sublist word at hsub
    obtain ⟨embedding, hembedding⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let second := embedding ⟨1, by simp⟩
    let third := embedding ⟨2, by simp⟩
    have horder : second.val < third.val :=
      embedding.strictMono (by change (1 : ℕ) < 2; omega)
    have hsecond : word.getD second.val 0 = values 3 := by
      simpa [second, List.getD_eq_getElem _ 0 (embedding ⟨1, by simp⟩).isLt] using
        (hembedding ⟨1, by simp⟩).symm
    have hthird : word.getD third.val 0 = values 2 := by
      simpa [third, List.getD_eq_getElem _ 0 (embedding ⟨2, by simp⟩).isLt] using
        (hembedding ⟨2, by simp⟩).symm
    have hinc : values 1 < values 2 ∧ values 2 < values 3 := by
      constructor
      · simpa using hmono 1 (by omega) (by change 1 < 3; omega)
      · simpa using hmono 2 (by omega) (by change 2 < 3; omega)
    have hsecondleft : second.val < first.length := by
      by_contra hnot
      have hs := hsuffix second.val (by omega) second.isLt
      have ht := hsuffix third.val (by omega) third.isLt
      omega
    have hlarge : values 3 ≤ first.length := by
      rw [← hsecond]
      change (square first ++ shift first.length (List.range' 1 (assemble tail).length)).getD
        second.val 0 ≤ first.length
      rw [List.getD_append _ _ _ _ (by omega),
        List.getD_eq_getElem _ 0 (by omega)]
      exact hprefix _ (List.getElem_mem (by omega))
    have hleftsub : [values 1, values 3, values 2].Sublist (square first) := by
      apply List.Sublist.of_sublist_append_left _ hsub
      intro value hv hshift
      have hsmall : value ≤ first.length := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      obtain ⟨source, hs, heq⟩ := List.mem_map.mp hshift
      have hrange : 1 ≤ source := by
        simp only [List.mem_range', Nat.one_mul] at hs
        obtain ⟨offset, hoffset, heq⟩ := hs
        omega
      omega
    apply hadmissible.2.2.2
    refine ⟨values, hmono, ?_, hleftsub, by simp⟩
    intro rank hlow hhigh
    apply hleftsub.subset
    change rank ≤ 3 at hhigh
    have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp

end D5.S3.Combinatorics.PermutationSquare.PermutationSquareStructure
