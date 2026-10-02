/- GID: D5/S3/Combinatorics/PopStack/PopStackFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackFamilies
   mirror-E: none(waiver:prefix-only-family-classification)
   anchors: []
   utility: none
   digest: Deleting a terminal minimum classifies all prefix-only members of the auxiliary class. -/

import D5.S3.Combinatorics.PopStack.PopStackPrime
import D5.S3.Combinatorics.PopStack.PopStackPrefixShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackFamilies

open PopStackDefs PopStackChains PopStackParallel PopStackInflation
open PopStackPrefixShape

def A (size : ℕ) : List ℕ :=
  if size % 2 = 0 then P (size / 2) else inflate (P (size / 2)) 0 [2, 1]

def B (size : ℕ) : List ℕ :=
  if size = 2 then [2, 1] else (A (size - 1)).map Nat.succ ++ [1]

theorem prefix_families (size : ℕ) (hsize : 2 ≤ size) :
    (A size).getD (size - 1) 0 ≠ 1 ∧ (B size).getD (size - 1) 0 = 1 ∧
      (∀ permutation : List ℕ,
        (permutation.Perm (List.range' 1 size) ∧ InD permutation ∧
          (∀ start count lower, 2 ≤ count → count < size → start + count ≤ size →
            ((permutation.drop start).take count).Perm (List.range' lower count) →
            start = 0)) ↔ permutation = A size ∨ permutation = B size) := by
  have hskewPrefix (permutation : List ℕ) (hlength : 2 ≤ permutation.length)
      (hperm : permutation.Perm (List.range' 1 permutation.length))
      (hD : InD permutation)
      (hprefix : ∀ start size lower, 2 ≤ size → size < permutation.length →
        start + size ≤ permutation.length →
        ((permutation.drop start).take size).Perm (List.range' lower size) → start = 0) :
      let extended := permutation.map Nat.succ ++ [1]
      extended.Perm (List.range' 1 (permutation.length + 1)) ∧ InD extended ∧
        ((∀ start size lower, 2 ≤ size → size < extended.length →
          start + size ≤ extended.length →
          ((extended.drop start).take size).Perm (List.range' lower size) → start = 0) ↔
          permutation.getD (permutation.length - 1) 0 ≠ 1) := by
    let extended := permutation.map Nat.succ ++ [1]
    change extended.Perm _ ∧ InD extended ∧
      ((∀ start size lower, 2 ≤ size → size < extended.length →
        start + size ≤ extended.length →
        ((extended.drop start).take size).Perm (List.range' lower size) → start = 0) ↔
        permutation.getD (permutation.length - 1) 0 ≠ 1)
    have hsize : extended.length = permutation.length + 1 := by
      simp only [extended, List.length_append, List.length_map, List.length_singleton]
    have hbounds : ∀ entry ∈ permutation, 1 ≤ entry ∧ entry ≤ permutation.length := by
      intro entry hentry
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hentry)
      omega
    have hshiftRange : ∀ lower size,
        (List.range' lower size).map Nat.succ = List.range' (lower + 1) size := by
      intro lower size
      simpa only [Nat.succ_eq_add_one] using
        (List.range'_succ_left (s := lower) (n := size)).symm
    have hpredRange : ∀ lower size, 1 ≤ lower →
        (List.range' lower size).map Nat.pred = List.range' (lower - 1) size := by
      intro lower size hpositive
      induction size generalizing lower with
      | zero => simp
      | succ size ih =>
        simp only [List.range'_succ, List.map_cons, Nat.pred_eq_sub_one,
          ih (lower + 1) (by omega)]
        congr 2
        omega
    have hshiftPerm : (permutation.map Nat.succ).Perm
        (List.range' 2 permutation.length) := by
      simpa only [hshiftRange] using hperm.map Nat.succ
    have hpermExtended : extended.Perm (List.range' 1 (permutation.length + 1)) := by
      have hh := (hshiftPerm.append (List.Perm.refl [1])).trans List.perm_append_comm
      change (permutation.map Nat.succ ++ [1]).Perm _
      rw [List.range'_succ]
      simpa only [List.singleton_append] using hh
    have hnodup : permutation.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
    have hnodupExtended : extended.Nodup :=
      hpermExtended.nodup_iff.mpr (List.nodup_range' _)
    obtain ⟨cut, hchain⟩ := (two_decreasing_chains permutation hnodup).1.mp hD
    have hchainExtended : extended.Pairwise (fun first second =>
        (first ≤ cut + 1 ↔ second ≤ cut + 1) → second < first) := by
      apply List.pairwise_append.mpr
      refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · apply hchain.map
        intro first second hrel hside
        have hh := hrel (by omega)
        omega
      · intro first hfirst second hsecond _
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hfirst
        have hh := hbounds old hold
        simp only [List.mem_singleton] at hsecond
        omega
    have hDExtended : InD extended :=
      (two_decreasing_chains extended hnodupExtended).1.mpr ⟨cut + 1, hchainExtended⟩
    have hinside : ∀ start size, start + size ≤ permutation.length →
        ((extended.drop start).take size) = ((permutation.drop start).take size).map Nat.succ := by
      intro start size hbound
      change ((((permutation.map Nat.succ ++ [1]).drop start).take size)) = _
      rw [List.drop_append_of_le_length (by simp only [List.length_map]; omega),
        List.take_append_of_le_length (by
          simp only [List.length_drop, List.length_map]; omega),
        ← List.map_drop, ← List.map_take]
    have hterminal : ∀ start size, start < permutation.length →
        start + size = permutation.length + 1 →
        ((extended.drop start).take size) = (permutation.drop start).map Nat.succ ++ [1] := by
      intro start size hstart hend
      change ((((permutation.map Nat.succ ++ [1]).drop start).take size)) = _
      rw [List.drop_append_of_le_length (by simp only [List.length_map]; omega),
        ← List.map_drop]
      apply List.take_of_length_le
      simp only [List.length_append, List.length_map, List.length_drop, List.length_singleton]
      omega
    have hlast : permutation.drop (permutation.length - 1) =
        [permutation.getD (permutation.length - 1) 0] := by
      apply List.ext_getElem
      · simp only [List.length_drop, List.length_cons, List.length_nil]
        omega
      · intro index hleft hright
        have hzero : index = 0 := by
          simp only [List.length_cons, List.length_nil] at hright
          omega
        subst index
        simp only [List.getElem_drop, Nat.add_zero]
        rw [List.getD_eq_getElem _ _ (by omega)]
        rfl
    refine ⟨hpermExtended, hDExtended, ?_⟩
    constructor
    · intro hnewPrefix heq
      have hsegment := hterminal (permutation.length - 1) 2 (by omega) (by omega)
      rw [hlast, heq] at hsegment
      have hinterval : ((extended.drop (permutation.length - 1)).take 2).Perm
          (List.range' 1 2) := by
        rw [hsegment]
        exact List.Perm.swap 1 2 []
      have hh := hnewPrefix (permutation.length - 1) 2 1 (by omega) (by omega) (by omega)
        hinterval
      omega
    · intro hnotLast start size lower hnontrivial hproper hbound hinterval
      by_cases hcontained : start + size ≤ permutation.length
      · have hsegment := hinside start size hcontained
        have hlowerMem : lower ∈ ((extended.drop start).take size) :=
          hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        rw [hsegment] at hlowerMem
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hlowerMem
        have holdMem : old ∈ permutation :=
          ((List.take_sublist size _).trans (List.drop_sublist start _)).subset hold
        have hpositive := (hbounds old holdMem).1
        have hlower : 2 ≤ lower := by omega
        have holdInterval : ((permutation.drop start).take size).Perm
            (List.range' (lower - 1) size) := by
          have hh := hinterval.map Nat.pred
          rw [hsegment, List.map_map, hpredRange lower size (by omega)] at hh
          simpa only [Function.comp_def, Nat.pred_succ, List.map_id_fun', id_eq] using hh
        by_cases hfull : size = permutation.length
        · omega
        · exact hprefix start size (lower - 1) hnontrivial (by omega) hcontained holdInterval
      · have hend : start + size = permutation.length + 1 := by omega
        have hstart : start < permutation.length := by omega
        have hsegment := hterminal start size hstart hend
        have hone : 1 ∈ (extended.drop start).take size := by rw [hsegment]; simp
        have hmin := List.mem_range'_1.mp (hinterval.mem_iff.mp hone)
        have hpositive : 1 ≤ lower := by
          have hlowerMem : lower ∈ ((extended.drop start).take size) :=
            hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          rw [hsegment] at hlowerMem
          rcases List.mem_append.mp hlowerMem with hshift | hlast
          · obtain ⟨old, hold, heq⟩ := List.mem_map.mp hshift
            omega
          · simp only [List.mem_singleton] at hlast
            omega
        have hlower : lower = 1 := by omega
        have hshiftedSuffix : ((permutation.drop start).map Nat.succ).Perm
            (List.range' 2 (size - 1)) := by
          have hrange : List.range' lower size = 1 :: List.range' 2 (size - 1) := by
            have hsizeEq : size = (size - 1) + 1 := by omega
            conv_lhs => rw [hlower, hsizeEq, List.range'_succ]
          rw [hsegment, hrange] at hinterval
          exact ((List.perm_append_singleton 1 _).symm.trans hinterval).cons_inv
        have holdSuffix : (permutation.drop start).Perm (List.range' 1 (size - 1)) := by
          have hh := hshiftedSuffix.map Nat.pred
          rw [List.map_map, hpredRange 2 (size - 1) (by omega)] at hh
          simpa only [Function.comp_def, Nat.pred_succ, List.map_id_fun', id_eq,
            Nat.reduceSub] using hh
        have hstartPositive : 1 ≤ start := by omega
        by_cases hpair : size = 2
        · have hstartLast : start = permutation.length - 1 := by omega
          rw [hstartLast, hlast] at holdSuffix
          have hentry := holdSuffix.mem_iff.mp
            (show permutation.getD (permutation.length - 1) 0 ∈
              [permutation.getD (permutation.length - 1) 0] by simp)
          simp only [hpair, List.range'_succ, List.range'_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hentry
          exact False.elim (hnotLast hentry)
        · have holdInterval : ((permutation.drop start).take (size - 1)).Perm
              (List.range' 1 (size - 1)) := by
            have hfull : (permutation.drop start).length = size - 1 := by
              simp only [List.length_drop]
              omega
            rw [List.take_of_length_le (by omega)]
            exact holdSuffix
          have hh := hprefix start (size - 1) 1 (by omega) (by omega) (by omega) holdInterval
          omega
  have hfirstBond : ∀ half : ℕ, 1 ≤ half →
      let permutation := inflate (P half) 0 [2, 1]
      permutation.Perm (List.range' 1 (2 * half + 1)) ∧ InD permutation ∧
        permutation.getD (2 * half) 0 = half + 2 ∧
        (∀ start count lower, 2 ≤ count → count < 2 * half + 1 →
          start + count ≤ 2 * half + 1 →
          (((permutation.drop start).take count).Perm (List.range' lower count) ↔
            start = 0 ∧ count = 2 ∧ lower = half)) := by
    intro half hhalf
    let tail := (P half).drop 1
    let shift := fun entry => if half < entry then entry + 1 else entry
    let permutation := inflate (P half) 0 [2, 1]
    change permutation.Perm _ ∧ InD permutation ∧ _ ∧ _
    obtain ⟨hPperm, _, _, hPsimple⟩ := parallel_simple half hhalf
    have hPlength : (P half).length = 2 * half := List.length_ofFn
    have hPfirst : (P half).getD 0 0 = half := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [P, List.getElem_ofFn, Nat.zero_mod, Nat.zero_div, ite_true, Nat.sub_zero]
    have hPhead : P half = half :: tail := by
      have hget : (P half)[0]? = some half := by
        rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega),
          hPfirst]
      have hh := List.drop_eq_getElem?_toList_append (l := P half) (i := 0)
      simpa only [List.drop_zero, hget, Option.toList_some, List.singleton_append] using hh
    have hshape : permutation = (half + 1) :: half :: tail.map shift := by
      dsimp only [permutation, inflate]
      rw [hPfirst]
      simp [tail, shift]
    have hlength : permutation.length = 2 * half + 1 := by
      rw [hshape]
      simp only [List.length_cons, List.length_map, tail, List.length_drop, hPlength]
      omega
    have hPnodup := hPperm.nodup_iff.mpr (List.nodup_range' _)
    have htailNodup : tail.Nodup := hPnodup.drop
    have hmissing : half ∉ tail := by
      rw [hPhead] at hPnodup
      exact (List.nodup_cons.mp hPnodup).1
    have htailMem : ∀ entry, entry ∈ tail ↔
        1 ≤ entry ∧ entry ≤ 2 * half ∧ entry ≠ half := by
      intro entry
      constructor
      · intro hentry
        have hh := List.mem_range'_1.mp (hPperm.mem_iff.mp
          (by rw [hPhead]; exact List.mem_cons_of_mem half hentry))
        exact ⟨by omega, by omega, fun heq => hmissing (heq ▸ hentry)⟩
      · rintro ⟨hpositive, hupper, hne⟩
        have hh : entry ∈ P half :=
          hPperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        rw [hPhead] at hh
        exact (List.mem_cons.mp hh).resolve_left hne
    have hshiftInjective : Function.Injective shift := by
      intro first second heq
      dsimp [shift] at heq
      split_ifs at heq <;> omega
    have hnodup : permutation.Nodup := by
      rw [hshape, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, htailNodup.map hshiftInjective⟩
      · simp only [List.mem_cons, List.mem_map, not_or, not_exists]
        refine ⟨by omega, ?_⟩
        rintro entry ⟨hentry, heq⟩
        have hh := (htailMem entry).mp hentry
        dsimp [shift] at heq
        split_ifs at heq <;> omega
      · intro hmem
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
        have hh := (htailMem entry).mp hentry
        dsimp [shift] at heq
        split_ifs at heq <;> omega
    have hperm : permutation.Perm (List.range' 1 (2 * half + 1)) := by
      apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_range' _)).mpr
      intro entry
      rw [hshape]
      simp only [List.mem_cons, List.mem_map, List.mem_range'_1]
      constructor
      · rintro (heq | heq | ⟨old, hold, heq⟩)
        · omega
        · omega
        · have hh := (htailMem old).mp hold
          dsimp [shift] at heq
          split_ifs at heq <;> omega
      · rintro ⟨hpositive, hupper⟩
        by_cases hfirst : entry = half + 1
        · exact Or.inl hfirst
        by_cases hsecond : entry = half
        · exact Or.inr (Or.inl hsecond)
        right; right
        by_cases hhigh : half + 1 < entry
        · refine ⟨entry - 1, (htailMem _).mpr (by omega), ?_⟩
          dsimp [shift]
          rw [if_pos (by omega)]
          omega
        · refine ⟨entry, (htailMem _).mpr (by omega), ?_⟩
          dsimp [shift]
          rw [if_neg (by omega)]
    have hPchain : (P half).Pairwise (fun first second =>
        (first ≤ half ↔ second ≤ half) → second < first) := by
      apply List.pairwise_iff_getElem.mpr
      intro first second hfirst hsecond horder hside
      simp only [P, List.getElem_ofFn] at hside ⊢
      have hfirstBound : first < 2 * half := by omega
      have hsecondBound : second < 2 * half := by omega
      split_ifs at hside ⊢ <;> omega
    have htailChain : (tail.map shift).Pairwise (fun first second =>
        (first ≤ half + 1 ↔ second ≤ half + 1) → second < first) := by
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem (p := hPchain.drop)
      intro first second hfirst hsecond horder hside
      have hf := (htailMem first).mp hfirst
      have hs := (htailMem second).mp hsecond
      have hcut : first ≤ half ↔ second ≤ half := by
        dsimp [shift] at hside
        split_ifs at hside <;> omega
      have hh := horder hcut
      dsimp [shift]
      split_ifs <;> omega
    have hchain : permutation.Pairwise (fun first second =>
        (first ≤ half + 1 ↔ second ≤ half + 1) → second < first) := by
      rw [hshape, List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, ?_, htailChain⟩
      · intro entry hentry hside
        rcases List.mem_cons.mp hentry with heq | hmem
        · omega
        · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
          have hh := (htailMem old).mp hold
          dsimp [shift] at hside ⊢
          split_ifs at hside ⊢ <;> omega
      · intro entry hentry hside
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hentry
        have hh := (htailMem old).mp hold
        dsimp [shift] at hside ⊢
        split_ifs at hside ⊢ <;> omega
    have hlast : permutation.getD (2 * half) 0 = half + 2 := by
      rw [hshape]
      have hi : 2 * half = (2 * half - 2) + 2 := by omega
      rw [hi]
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem _ 0 (by
        simp only [List.length_map, tail, List.length_drop, hPlength]; omega)]
      simp only [List.getElem_map, tail, List.getElem_drop, P, List.getElem_ofFn, shift]
      split_ifs <;> omega
    refine ⟨hperm, (two_decreasing_chains permutation hnodup).1.mpr
      ⟨half + 1, hchain⟩, hlast, ?_⟩
    have hinitial : (permutation.drop 0).take 2 = [half + 1, half] := by
      rw [hshape]
      rfl
    intro start count lower hcount hproper hbound
    constructor
    · intro hinterval
      change ((permutation.drop start).take count).Perm (List.range' lower count) at hinterval
      have hposition : start = 0 ∧ count = 2 := by
        by_cases hlarge : 2 ≤ half
        · have hh := (PopStackPrime.inflation_intervals (P half) [2, 1] 0
            (by simpa only [hPlength] using hPperm) hPsimple (by omega) (by omega)
            (by decide) (by simp)).1 start count lower hcount
              (by change count < permutation.length; omega)
              (by change start + count ≤ permutation.length; omega) hinterval
          simp only [List.length_cons, List.length_nil] at hh
          omega
        · have hhalfOne : half = 1 := by omega
          have hP2 : P 1 = [1, 2] := by decide
          have hQ3 : permutation = [2, 1, 3] := by
            rw [hshape, hhalfOne]
            simp [tail, hhalfOne, hP2, shift]
          have hcountTwo : count = 2 := by omega
          have hstartCases : start = 0 ∨ start = 1 := by omega
          rcases hstartCases with hzero | hone
          · exact ⟨hzero, hcountTwo⟩
          · rw [hQ3, hone, hcountTwo] at hinterval
            have hmin := List.mem_range'_1.mp
              (hinterval.mem_iff.mp (by decide : 1 ∈ [1, 3]))
            have hmax := List.mem_range'_1.mp
              (hinterval.mem_iff.mp (by decide : 3 ∈ [1, 3]))
            omega
      obtain ⟨hzero, hcountTwo⟩ := hposition
      rw [hzero, hcountTwo, hinitial] at hinterval
      have hhalfMem := List.mem_range'_1.mp
        (hinterval.mem_iff.mp (by simp : half ∈ [half + 1, half]))
      have hlowerMem := hinterval.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega : lower ≤ lower ∧ lower < lower + 2))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlowerMem
      exact ⟨hzero, hcountTwo, by omega⟩
    · rintro ⟨hstart, hcount, hlower⟩
      change ((permutation.drop start).take count).Perm (List.range' lower count)
      rw [hstart, hcount, hlower, hinitial]
      simpa only [List.range'_succ, List.range'_zero] using List.Perm.swap half (half + 1) []
  have hA : ∀ length, 2 ≤ length →
      (A length).Perm (List.range' 1 length) ∧ InD (A length) ∧
        (A length).getD (length - 1) 0 ≠ 1 ∧
        (∀ start count lower, 2 ≤ count → count < length → start + count ≤ length →
          (((A length).drop start).take count).Perm (List.range' lower count) →
          start = 0) := by
    intro length hlength
    let half := length / 2
    have hhalf : 1 ≤ half := by dsimp [half]; omega
    by_cases heven : length % 2 = 0
    · have hlengthHalf : length = 2 * half := by dsimp [half]; omega
      have hshape : A length = P half := by simp only [A, if_pos heven, half]
      obtain ⟨hperm, hD, _, hsimple⟩ := parallel_simple half hhalf
      have hPlength : (P half).length = length := by simp [P, hlengthHalf]
      have hlast : (P half).getD (length - 1) 0 = half + 1 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [P, List.getElem_ofFn]
        split_ifs <;> omega
      rw [hshape]
      refine ⟨by simpa only [hlengthHalf] using hperm, hD, by omega, ?_⟩
      intro start count lower hcount hproper hbound hinterval
      exact False.elim (hsimple start count lower hcount (by omega) (by omega) hinterval)
    · have hlengthHalf : length = 2 * half + 1 := by dsimp [half]; omega
      have hshape : A length = inflate (P half) 0 [2, 1] := by
        simp only [A, if_neg heven, half]
      obtain ⟨hperm, hD, hlast, hintervals⟩ := hfirstBond half hhalf
      rw [hshape]
      refine ⟨by simpa only [hlengthHalf] using hperm, hD, ?_, ?_⟩
      · have hi : length - 1 = 2 * half := by omega
        rw [hi, hlast]
        omega
      · intro start count lower hcount hproper hbound hinterval
        exact ((hintervals start count lower hcount (by omega) (by omega)).mp hinterval).1
  have hB : (B size).Perm (List.range' 1 size) ∧ InD (B size) ∧
      (B size).getD (size - 1) 0 = 1 ∧
      (∀ start count lower, 2 ≤ count → count < size → start + count ≤ size →
        (((B size).drop start).take count).Perm (List.range' lower count) → start = 0) := by
    by_cases htwo : size = 2
    · subst size
      have hshape : B 2 = [2, 1] := by simp [B]
      rw [hshape]
      refine ⟨by decide, ?_, rfl, ?_⟩
      · apply (two_decreasing_chains [2, 1] (by decide)).1.mpr
        exact ⟨2, by simp [List.pairwise_cons]⟩
      · intro start count lower hcount hproper
        omega
    · obtain ⟨hperm, hD, hlast, hprefix⟩ := hA (size - 1) (by omega)
      have hlength : (A (size - 1)).length = size - 1 := by
        simpa only [List.length_range'] using hperm.length_eq
      have hh := hskewPrefix (A (size - 1)) (by omega)
        (by simpa only [hlength] using hperm) hD
        (by simpa only [hlength] using hprefix)
      have hshape : B size = (A (size - 1)).map Nat.succ ++ [1] := by
        simp only [B, if_neg htwo]
      rw [hshape]
      refine ⟨by simpa only [hlength, Nat.sub_add_cancel (show 1 ≤ size by omega)] using hh.1,
        hh.2.1, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by
          simp only [List.length_map, hlength]; exact le_rfl)]
        simp only [List.length_map, hlength, Nat.sub_self, List.getElem?_cons_zero,
          Option.getD_some]
      · have hprefix' := hh.2.2.mpr (by simpa only [hlength] using hlast)
        have hwholeLength : ((A (size - 1)).map Nat.succ ++ [1]).length = size := by
          simp only [List.length_append, List.length_map, hlength, List.length_singleton]
          omega
        simpa only [hwholeLength] using hprefix'
  have htwo : ∀ permutation : List ℕ, permutation.Perm (List.range' 1 2) →
      permutation = [1, 2] ∨ permutation = [2, 1] := by
    intro permutation hperm
    have hlength : permutation.length = 2 := by simpa using hperm.length_eq
    obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp hlength
    have hfirst := hperm.mem_iff.mp (by simp : first ∈ [first, second])
    have hsecond := hperm.mem_iff.mp (by simp : second ∈ [first, second])
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' _)
    simp only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hfirst hsecond
    simp only [List.nodup_cons, List.mem_singleton] at hnodup
    rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl
    · exact False.elim (hnodup.1 rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hnodup.1 rfl)
  have hnonterminal : ∀ permutation : List ℕ, ∀ length, 2 ≤ length →
      permutation.Perm (List.range' 1 length) → InD permutation →
      (∀ start count lower, 2 ≤ count → count < length → start + count ≤ length →
        ((permutation.drop start).take count).Perm (List.range' lower count) → start = 0) →
      permutation.getD (length - 1) 0 ≠ 1 → permutation = A length := by
    intro permutation length hlength hperm hD hprefix hlast
    by_cases hlengthTwo : length = 2
    · subst length
      rcases htwo permutation hperm with rfl | rfl
      · have hA2 : A 2 = [1, 2] := by decide
        exact hA2.symm
      · exact False.elim (hlast rfl)
    · obtain ⟨half, hhalf, hshape⟩ :=
        prefix_nonterminal permutation length (by omega) hperm hD hprefix hlast
      rcases hshape with ⟨hsizeHalf, rfl⟩ | ⟨hsizeHalf, rfl⟩
      · have heven : length % 2 = 0 := by omega
        have hhalfEq : length / 2 = half := by omega
        simp only [A, if_pos heven, hhalfEq]
      · have hodd : length % 2 ≠ 0 := by omega
        have hhalfEq : length / 2 = half := by omega
        simp only [A, if_neg hodd, hhalfEq]
  refine ⟨(hA size hsize).2.2.1, hB.2.2.1, ?_⟩
  intro permutation
  constructor
  · rintro ⟨hperm, hD, hprefix⟩
    by_cases hlast : permutation.getD (size - 1) 0 = 1
    swap
    · exact Or.inl (hnonterminal permutation size hsize hperm hD hprefix hlast)
    right
    by_cases hsizeTwo : size = 2
    · subst size
      rcases htwo permutation hperm with rfl | rfl
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at hlast
        omega
      · simp [B]
    have hlength : permutation.length = size := by
      simpa only [List.length_range'] using hperm.length_eq
    let initial := permutation.take (size - 1)
    let old := initial.map Nat.pred
    have hprefixLength : initial.length = size - 1 := by
      simp only [initial, List.length_take, hlength]
      omega
    have hdropLast : permutation.drop (size - 1) = [1] := by
      have hget : permutation[size - 1]? = some 1 := by
        rw [List.getElem?_eq_getElem (by omega),
          ← List.getD_eq_getElem _ 0 (by omega), hlast]
      rw [List.drop_eq_getElem?_toList_append, hget]
      have hdrop : permutation.drop (size - 1 + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      simp only [Option.toList_some, hdrop, List.append_nil]
    have hsplit : permutation = initial ++ [1] := by
      have hh := List.take_append_drop (size - 1) permutation
      rw [hdropLast] at hh
      exact hh.symm
    have hprefixPerm : initial.Perm (List.range' 2 (size - 1)) := by
      have hh := (List.perm_append_singleton 1 initial).symm.trans (hsplit ▸ hperm)
      have hrange : List.range' 1 size = 1 :: List.range' 2 (size - 1) := by
        have heq : size = (size - 1) + 1 := by omega
        conv_lhs => rw [heq, List.range'_succ]
      rw [hrange] at hh
      exact hh.cons_inv
    have hprefixBounds : ∀ entry ∈ initial, 2 ≤ entry ∧ entry ≤ size := by
      intro entry hentry
      have hh := List.mem_range'_1.mp (hprefixPerm.mem_iff.mp hentry)
      omega
    have hpredRange : ∀ count bottom, 1 ≤ bottom →
        (List.range' bottom count).map Nat.pred = List.range' (bottom - 1) count := by
      intro count
      induction count with
      | zero => intro bottom hbottom; simp
      | succ count ih =>
        intro bottom hbottom
        simp only [List.range'_succ, List.map_cons, Nat.pred_eq_sub_one,
          ih (bottom + 1) (by omega)]
        congr 2; omega
    have holdPerm : old.Perm (List.range' 1 (size - 1)) := by
      have hh := hprefixPerm.map Nat.pred
      simpa only [old, hpredRange (size - 1) 2 (by omega), Nat.reduceSub] using hh
    have holdLength : old.length = size - 1 := by simp only [old, List.length_map,
      hprefixLength]
    have hreturn : old.map Nat.succ = initial := by
      dsimp only [old]
      rw [List.map_map]
      calc
        initial.map (Nat.succ ∘ Nat.pred) = initial.map id := by
          apply List.map_congr_left
          intro entry hentry
          have hh := hprefixBounds entry hentry
          simp only [Function.comp_apply, id_eq, Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
          omega
        _ = initial := List.map_id _
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' _)
    have holdNodup := holdPerm.nodup_iff.mpr (List.nodup_range' _)
    obtain ⟨cut, hchains⟩ := (two_decreasing_chains permutation hnodup).1.mp hD
    have holdD : InD old := by
      apply (two_decreasing_chains old holdNodup).1.mpr
      refine ⟨cut - 1, ?_⟩
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem (p := hchains.take)
      intro first second hfirst hsecond horder hside
      have hf := hprefixBounds first hfirst
      have hs := hprefixBounds second hsecond
      have hcut : first ≤ cut ↔ second ≤ cut := by
        simp only [Nat.pred_eq_sub_one] at hside
        omega
      have hh := horder hcut
      simp only [Nat.pred_eq_sub_one]
      omega
    have hsuccRange : ∀ count bottom,
        (List.range' bottom count).map Nat.succ = List.range' (bottom + 1) count := by
      intro count
      induction count with
      | zero => intro bottom; simp
      | succ count ih =>
        intro bottom
        simp only [List.range'_succ, List.map_cons, ih, Nat.succ_eq_add_one]
    have holdPrefix : ∀ start count lower, 2 ≤ count → count < size - 1 →
        start + count ≤ size - 1 →
        ((old.drop start).take count).Perm (List.range' lower count) → start = 0 := by
      intro start count lower hcount hproper hbound hinterval
      have hh := hinterval.map Nat.succ
      rw [List.map_take, List.map_drop, hreturn,
        hsuccRange count lower] at hh
      have hsegment : ((initial.drop start).take count) =
          ((permutation.drop start).take count) := by
        simp only [initial, List.drop_take, List.take_take]
        congr 1
        omega
      rw [hsegment] at hh
      exact hprefix start count (lower + 1) hcount (by omega) (by omega) hh
    have holdLast : old.getD (size - 2) 0 ≠ 1 := by
      intro hlastOld
      have hgetOld : old[size - 2]? = some 1 := by
        rw [List.getElem?_eq_getElem (by omega),
          ← List.getD_eq_getElem _ 0 (by omega), hlastOld]
      have hgetPrefix : initial[size - 2]? = some 2 := by
        rw [← hreturn, List.getElem?_map, hgetOld]
        rfl
      have hget : permutation[size - 2]? = some 2 := by
        rw [List.getElem?_take_of_lt (by omega)] at hgetPrefix
        exact hgetPrefix
      have hdrop : permutation.drop (size - 2) = [2, 1] := by
        rw [List.drop_eq_getElem?_toList_append, hget]
        have heq : size - 2 + 1 = size - 1 := by omega
        rw [heq, hdropLast]
        rfl
      have hinterval : ((permutation.drop (size - 2)).take 2).Perm
          (List.range' 1 2) := by
        rw [hdrop]
        decide
      have hh := hprefix (size - 2) 2 1 (by omega) (by omega) (by omega) hinterval
      omega
    have holdA : old = A (size - 1) :=
      hnonterminal old (size - 1) (by omega) holdPerm holdD holdPrefix
        (by simpa only [show size - 1 - 1 = size - 2 by omega] using holdLast)
    rw [B, if_neg hsizeTwo, ← holdA, hreturn, ← hsplit]
  · rintro (rfl | rfl)
    · exact ⟨(hA size hsize).1, (hA size hsize).2.1, (hA size hsize).2.2.2⟩
    · exact ⟨hB.1, hB.2.1, hB.2.2.2⟩

end D5.S3.Combinatorics.PopStack.PopStackFamilies
