/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci
   mirror-E: none(waiver:fibonacci-circular-class-enumeration)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Minimum-split and skew-block bijections enumerate two linear pattern classes. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCounts
import D5.S3.Combinatorics.ArcherCyclicPadovanBlocks
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncConverse
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci

open D5.S3.Combinatorics
open Nonnesting.NonnestingDefs RotationAvoidanceCounts

theorem fibonacci_count (n : ℕ) (hn : 1 ≤ n) :
    (Fishburn.FishburnClassicalDefs.classicalAvoiders n
      [[2, 1, 3], [4, 1, 3, 2]]).ncard = Nat.fib (2 * n - 1) := by
  classical
  let words := fun size => Fishburn.FishburnClassicalDefs.classicalAvoiders size
    [[2, 1, 3], [4, 1, 3, 2]]
  have membership (size : ℕ) (word : List ℕ) : word ∈ words size ↔
      word.Perm (List.range' 1 size) ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ Occurs [4, 1, 3, 2] word := by
    simp [words, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have finite_words (size : ℕ) : (words size).Finite := by
    apply (List.finite_toSet ((List.range' 1 size).permutations)).subset
    intro word hword
    exact List.mem_permutations.mpr ((membership size word).mp hword).1
  have shift (pattern word : List ℕ) (offset : ℕ)
      (hpattern : pattern ∈ [[2, 1, 3], [4, 1, 3, 2]]) :
      Occurs pattern (word.map (offset + ·)) ↔ Occurs pattern word := by
    have hletters : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hletters]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (offset + ·)
      (by intro low high hlt; dsimp; omega)
  have recurrence (size : ℕ) : (words (size + 1)).ncard =
      (words size).ncard + ∑ index : Fin size, (words (index.val + 1)).ncard := by
    let Domain := (words size) ⊕ (Σ index : Fin size, words (index.val + 1))
    have : Finite (words size) := (finite_words size).to_subtype
    have (index : Fin size) : Finite (words (index.val + 1)) :=
      (finite_words (index.val + 1)).to_subtype
    let front : List ℕ → List ℕ := fun word => 1 :: word.map (1 + ·)
    let block (cut : ℕ) (word : List ℕ) : List ℕ :=
      word.map (size + 1 - cut + ·) ++ 1 :: List.range' 2 (size - cut)
    have frontMember (word : List ℕ) (hword : word ∈ words size) :
        front word ∈ words (size + 1) := by
      obtain ⟨hperm, h213, h4132⟩ := (membership _ _).mp hword
      have hperm' : (front word).Perm (List.range' 1 (size + 1)) := by
        have hmap := hperm.map (1 + ·)
        rw [List.map_add_range'] at hmap
        simpa only [front, List.range'_succ, Nat.reduceAdd, Nat.mul_one] using hmap.cons 1
      have hleast : ∀ value ∈ word.map (1 + ·), 1 < value := by
        intro value hvalue
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hvalue
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hold)
        omega
      apply (membership _ _).mpr
      refine ⟨hperm', ?_⟩
      apply (minimum_split_fibonacci [] (word.map (1 + ·))
        (hperm'.nodup_iff.mpr List.nodup_range') (by simpa using hleast)).mpr
      refine ⟨⟨?_, ?_⟩, by simp, Or.inl ⟨rfl, ?_, ?_⟩⟩
      · rintro ⟨witness, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
      · rintro ⟨witness, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
      · exact fun hocc => h213 ((shift _ word 1 (by simp)).mp hocc)
      · exact fun hocc => h4132 ((shift _ word 1 (by simp)).mp hocc)
    have blockMember (cut : ℕ) (hcutPositive : 1 ≤ cut) (hcut : cut ≤ size)
        (word : List ℕ) (hword : word ∈ words cut) :
        block cut word ∈ words (size + 1) := by
      obtain ⟨hperm, h213, h4132⟩ := (membership _ _).mp hword
      have hlength : word.length = cut := by simpa using hperm.length_eq
      have hleftPerm : (word.map (size + 1 - cut + ·)).Perm
          (List.range' (size + 2 - cut) cut) := by
        have := hperm.map (size + 1 - cut + ·)
        simpa [List.map_add_range', show size + 1 - cut + 1 = size + 2 - cut by omega]
          using this
      have hrange : List.range' 2 (size - cut) ++ List.range' (size + 2 - cut) cut =
          List.range' 2 size := by
        have := List.range'_append_1 (s := 2) (m := size - cut) (n := cut)
        simpa [Nat.sub_add_cancel hcut, show 2 + (size - cut) = size + 2 - cut by omega]
          using this
      have hperm' : (block cut word).Perm (List.range' 1 (size + 1)) := by
        dsimp [block]
        apply (hleftPerm.append (List.Perm.refl (1 :: List.range' 2 (size - cut)))).trans
        have hcomm := List.perm_append_comm
          (l₁ := List.range' (size + 2 - cut) cut)
          (l₂ := 1 :: List.range' 2 (size - cut))
        simpa [hrange, List.range'_succ] using hcomm
      have hseparation : ∀ high ∈ word.map (size + 1 - cut + ·),
          ∀ low ∈ List.range' 2 (size - cut), low < high := by
        intro high hhigh low hlow
        have hh := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hhigh)
        have hl := List.mem_range'_1.mp hlow
        omega
      have hleast : ∀ value ∈ word.map (size + 1 - cut + ·) ++
          List.range' 2 (size - cut), 1 < value := by
        intro value hvalue
        rcases List.mem_append.mp hvalue with hleft | hright
        · have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hleft)
          omega
        · have := List.mem_range'_1.mp hright
          omega
      apply (membership _ _).mpr
      refine ⟨hperm', ?_⟩
      apply (minimum_split_fibonacci _ _ (hperm'.nodup_iff.mpr List.nodup_range') hleast).mpr
      refine ⟨⟨?_, ?_⟩, hseparation, Or.inr ⟨?_, ?_⟩⟩
      · exact fun hocc => h213 ((shift _ word _ (by simp)).mp hocc)
      · exact fun hocc => h4132 ((shift _ word _ (by simp)).mp hocc)
      · have : 0 < (word.map (size + 1 - cut + ·)).length := by simp [hlength]; omega
        exact List.ne_nil_of_length_pos this
      · exact List.pairwise_lt_range' _ (by omega)
    let emit : Domain → words (size + 1) := fun input =>
      match input with
      | Sum.inl parent => ⟨front parent.val, frontMember parent.val parent.property⟩
      | Sum.inr ⟨index, parent⟩ =>
        ⟨block (index.val + 1) parent.val,
          blockMember _ (by omega) (by omega) parent.val parent.property⟩
    have frontCut (word : List ℕ) : (front word).idxOf 1 = 0 := by simp [front]
    have blockCut (cut : ℕ) (hcut : cut ≤ size) (word : List ℕ)
        (hword : word ∈ words cut) : (block cut word).idxOf 1 = cut := by
      have hperm := ((membership _ _).mp hword).1
      have hlength : word.length = cut := by simpa using hperm.length_eq
      have hnot : 1 ∉ word.map (size + 1 - cut + ·) := by
        intro hmem
        obtain ⟨value, hvalue, heq⟩ := List.mem_map.mp hmem
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hvalue)
        omega
      simp [block, List.idxOf_append_of_notMem hnot, hlength]
    have emitInjective : Function.Injective emit := by
      intro first second heq
      have hwords := congrArg Subtype.val heq
      have hcuts := congrArg (fun word : List ℕ => word.idxOf 1) hwords
      cases first with
      | inl parent =>
        cases second with
        | inl other =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have hmaps := List.cons.inj hwords |>.2
          exact (List.map_inj_right (by intro low high heq; omega)).mp hmaps
        | inr other =>
          obtain ⟨index, other⟩ := other
          change (front parent.val).idxOf 1 = (block (index.val + 1) other.val).idxOf 1
            at hcuts
          rw [frontCut, blockCut _ (by omega) _ other.property] at hcuts
          omega
      | inr parent =>
        obtain ⟨index, parent⟩ := parent
        cases second with
        | inl other =>
          change (block (index.val + 1) parent.val).idxOf 1 = (front other.val).idxOf 1
            at hcuts
          rw [blockCut _ (by omega) _ parent.property, frontCut] at hcuts
          omega
        | inr other =>
          obtain ⟨otherIndex, other⟩ := other
          change (block (index.val + 1) parent.val).idxOf 1 =
            (block (otherIndex.val + 1) other.val).idxOf 1 at hcuts
          rw [blockCut _ (by omega) _ parent.property,
            blockCut _ (by omega) _ other.property] at hcuts
          have hi : index = otherIndex := Fin.ext (by omega)
          subst otherIndex
          apply congrArg Sum.inr
          apply congrArg (Sigma.mk index)
          apply Subtype.ext
          have hlength : parent.val.length = index.val + 1 := by
            simpa using ((membership _ _).mp parent.property).1.length_eq
          have hotherLength : other.val.length = index.val + 1 := by
            simpa using ((membership _ _).mp other.property).1.length_eq
          have htake := congrArg (List.take (index.val + 1)) hwords
          change (block (index.val + 1) parent.val).take (index.val + 1) =
            (block (index.val + 1) other.val).take (index.val + 1) at htake
          have hmaps : parent.val.map (size + 1 - (index.val + 1) + ·) =
              other.val.map (size + 1 - (index.val + 1) + ·) := by
            simpa [block, hlength, hotherLength] using htake
          exact (List.map_inj_right (by intro low high heq; omega)).mp hmaps
    have emitSurjective : Function.Surjective emit := by
      intro output
      obtain ⟨hperm, h213, h4132⟩ := (membership _ _).mp output.property
      have hone : 1 ∈ output.val := hperm.mem_iff.mpr (by simp)
      obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hone
      have hlength : left.length + right.length = size := by
        have := hperm.length_eq
        simp [hsplit] at this
        omega
      have hnodup : (left ++ 1 :: right).Nodup := by
        rw [← hsplit]
        exact hperm.nodup_iff.mpr List.nodup_range'
      have hleast : ∀ value ∈ left ++ right, 1 < value := by
        intro value hvalue
        have hnot : value ≠ 1 := by
          have hleft := (List.nodup_append.mp hnodup).2.2
          have hright := (List.nodup_append.mp hnodup).2.1
          rcases List.mem_append.mp hvalue with hvalue | hvalue
          · intro heq
            exact hleft value hvalue 1 (by simp) heq
          · intro heq
            exact (List.nodup_cons.mp hright).1 (heq ▸ hvalue)
        have hmem : value ∈ output.val := by simp [hsplit]; aesop
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
        omega
      obtain ⟨hleftAvoid, hseparation, hright⟩ :=
        (minimum_split_fibonacci left right hnodup hleast).mp
          (by simpa only [← hsplit] using And.intro h213 h4132)
      have hrestPerm : (right ++ left).Perm (List.range' 2 size) := by
        have hcomm := List.perm_append_comm (l₁ := left) (l₂ := 1 :: right)
        have hperm' := hcomm.symm.trans (by simpa [hsplit] using hperm)
        simpa [List.range'_succ] using hperm'.cons_inv
      have hrightPerm : right.Perm (List.range' 2 right.length) := by
        apply ArcherCyclicPadovanBlocks.low_block_perm_initial 2 right left
        · simpa [hlength, Nat.add_comm] using hrestPerm
        · intro low hlow high hhigh
          exact hseparation high hhigh low hlow
      have hleftPerm : left.Perm (List.range' (right.length + 2) left.length) := by
        have hrange := List.range'_append_1 (s := 2) (m := right.length) (n := left.length)
        have hboth : (List.range' 2 right.length ++ left).Perm
            (List.range' 2 right.length ++ List.range' (right.length + 2) left.length) := by
          apply (hrightPerm.symm.append (List.Perm.refl left)).trans
          have hcombined : List.range' 2 right.length ++
              List.range' (right.length + 2) left.length = List.range' 2 size := by
            simpa [Nat.add_comm, hlength] using hrange
          rw [hcombined]
          exact hrestPerm
        exact List.perm_append_left_iff _ |>.mp hboth
      rcases hright with ⟨hleftEmpty, hright213, hright4132⟩ | ⟨hleftNonempty, hincreasing⟩
      · subst left
        have hrightLength : right.length = size := by simpa using hlength
        let parent := right.map (fun value => value - 1)
        have hparentPerm : parent.Perm (List.range' 1 size) := by
          have := hrightPerm.map (fun value => value - 1)
          simpa [parent, hrightLength, List.map_sub_range' (by omega : 1 ≤ 2)] using this
        have hrecover : parent.map (1 + ·) = right := by
          dsimp [parent]
          rw [List.map_map]
          calc
            right.map ((1 + ·) ∘ (fun value => value - 1)) = right.map id := by
              apply List.map_congr_left
              intro value hvalue
              have := hleast value (by simpa using hvalue)
              simp
              omega
            _ = right := List.map_id right
        have hparent : parent ∈ words size := (membership _ _).mpr
          ⟨hparentPerm, fun hocc => hright213 (by
            rw [← hrecover]; exact (shift _ parent 1 (by simp)).mpr hocc),
          fun hocc => hright4132 (by
            rw [← hrecover]; exact (shift _ parent 1 (by simp)).mpr hocc)⟩
        refine ⟨Sum.inl ⟨parent, hparent⟩, Subtype.ext ?_⟩
        change front parent = output.val
        simp [front, hrecover, hsplit]
      · have hleftPositive : 1 ≤ left.length := by
          have := List.length_pos_iff.mpr hleftNonempty
          omega
        let index : Fin size := ⟨left.length - 1, by omega⟩
        have hindex : index.val + 1 = left.length := by dsimp [index]; omega
        let parent := left.map (fun value => value - (right.length + 1))
        have hparentPerm : parent.Perm (List.range' 1 (index.val + 1)) := by
          have := hleftPerm.map (fun value => value - (right.length + 1))
          simpa [parent, hindex,
            List.map_sub_range' (by omega : right.length + 1 ≤ right.length + 2)] using this
        have hrecover : parent.map (right.length + 1 + ·) = left := by
          dsimp [parent]
          rw [List.map_map]
          calc
            left.map ((right.length + 1 + ·) ∘
                (fun value => value - (right.length + 1))) = left.map id := by
              apply List.map_congr_left
              intro value hvalue
              have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hvalue)
              simp
              omega
            _ = left := List.map_id left
        have hparent : parent ∈ words (index.val + 1) := (membership _ _).mpr
          ⟨hparentPerm, fun hocc => hleftAvoid.1 (by
            rw [← hrecover]; exact (shift _ parent _ (by simp)).mpr hocc),
          fun hocc => hleftAvoid.2 (by
            rw [← hrecover]; exact (shift _ parent _ (by simp)).mpr hocc)⟩
        have hrightEq : right = List.range' 2 (size - (index.val + 1)) := by
          have heq := hrightPerm.eq_of_pairwise' hincreasing (List.pairwise_lt_range' _
            (by omega))
          simpa [hindex, show size - left.length = right.length by omega] using heq
        refine ⟨Sum.inr ⟨index, ⟨parent, hparent⟩⟩, Subtype.ext ?_⟩
        change block (index.val + 1) parent = output.val
        have hoffset : size + 1 - (index.val + 1) = right.length + 1 := by
          rw [hindex]
          omega
        simp [block, hoffset, hrecover, ← hrightEq, hsplit]
    have hcard := Nat.card_congr (Equiv.ofBijective emit ⟨emitInjective, emitSurjective⟩)
    rw [Nat.card_sum, Nat.card_sigma, Nat.card_coe_set_eq] at hcard
    simpa only [Nat.card_coe_set_eq] using hcard.symm
  have hzero : words 0 = {[]} := by
    ext word
    rw [membership]
    constructor
    · rintro ⟨hperm, _⟩
      have heq : word = [] := by simpa using hperm
      simp [heq]
    · intro hword
      have heq : word = [] := by simpa using hword
      subst word
      refine ⟨by rfl, ?_, ?_⟩
      all_goals
        rintro ⟨witness, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
  have formula (offset : ℕ) : (words (offset + 1)).ncard = Nat.fib (2 * offset + 1) := by
    have hsum (size : ℕ) : ∑ index : Fin size, Nat.fib (2 * index.val + 1) =
        Nat.fib (2 * size) := by
      induction size with
      | zero => simp
      | succ size ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
        rw [show 2 * (size + 1) = 2 * size + 2 by omega, Nat.fib_add_two]
    induction offset using Nat.strong_induction_on with
    | h offset ih =>
      rw [recurrence offset]
      have hterms : ∑ index : Fin offset, (words (index.val + 1)).ncard =
          Nat.fib (2 * offset) := by
        rw [← hsum offset]
        apply Finset.sum_congr rfl
        intro index _
        exact ih index.val index.isLt
      rw [hterms]
      cases offset with
      | zero => simp [hzero]
      | succ offset =>
        rw [ih offset (by omega)]
        have heq : 2 * (offset + 1) + 1 = (2 * offset + 1) + 2 := by omega
        rw [heq, Nat.fib_add_two]
        have heq' : 2 * (offset + 1) = (2 * offset + 1) + 1 := by omega
        rw [heq']
  have hfinal := formula (n - 1)
  simpa [words, Nat.sub_add_cancel hn, show 2 * (n - 1) + 1 = 2 * n - 1 by omega]
    using hfinal

theorem skew_block_binary_count (n : ℕ) (hn : 1 ≤ n) :
    (Fishburn.FishburnClassicalDefs.classicalAvoiders n
      [[1, 3, 2], [2, 1, 3]]).ncard = 2 ^ (n - 1) := by
  classical
  let words := fun size => Fishburn.FishburnClassicalDefs.classicalAvoiders size
    [[1, 3, 2], [2, 1, 3]]
  have membership (size : ℕ) (word : List ℕ) : word ∈ words size ↔
      word.Perm (List.range' 1 size) ∧
        ¬ Occurs [1, 3, 2] word ∧ ¬ Occurs [2, 1, 3] word := by
    simp [words, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have finite_words (size : ℕ) : (words size).Finite := by
    apply (List.finite_toSet ((List.range' 1 size).permutations)).subset
    intro word hword
    exact List.mem_permutations.mpr ((membership size word).mp hword).1
  have recurrence (size : ℕ) : (words (size + 1)).ncard =
      ∑ index : Fin (size + 1), (words index.val).ncard := by
    let block := fun (cut : ℕ) (word : List ℕ) =>
      List.range' (cut + 1) (size - cut) ++ (size + 1) :: word
    have blockMember (cut : ℕ) (hcut : cut ≤ size) (word : List ℕ)
        (hword : word ∈ words cut) : block cut word ∈ words (size + 1) := by
      obtain ⟨hperm, h132, h213⟩ := (membership _ _).mp hword
      obtain ⟨parts, hpos, hsum, heq⟩ :=
        Nonnesting.NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks cut word hperm h132 h213
      have hblock : block cut word =
          Nonnesting.NonnestingBasicRoyalIncBlocks.incBlocks (size + 1)
            ((size + 1 - cut) :: parts) := by
        simp only [block, Nonnesting.NonnestingBasicRoyalIncBlocks.incBlocks]
        have hremain : size + 1 - (size + 1 - cut) = cut := by omega
        rw [hremain, show size + 1 - cut = (size - cut) + 1 by omega, List.range'_concat]
        simp only [one_mul, show cut + 1 + (size - cut) = size + 1 by omega,
          List.append_assoc, List.singleton_append, ← heq]
      have hav := Nonnesting.NonnestingBasicRoyalIncConverse.incBlocks_avoids (size + 1)
        ((size + 1 - cut) :: parts) (by
          intro part hpart
          rcases List.mem_cons.mp hpart with rfl | hpart
          · omega
          · exact hpos _ hpart) (by simp only [List.sum_cons]; omega)
      apply (membership _ _).mpr
      refine ⟨?_, by simpa only [← hblock] using hav⟩
      have hrange : List.range' 1 cut ++ List.range' (cut + 1) (size - cut) =
          List.range' 1 size := by
        simpa [Nat.add_sub_of_le hcut, Nat.add_comm] using
          (List.range'_append_1 (s := 1) (m := cut) (n := size - cut))
      have hrest : (List.range' (cut + 1) (size - cut) ++ word).Perm
          (List.range' 1 size) := by
        rw [← hrange]
        exact ((List.Perm.refl _).append hperm).trans List.perm_append_comm
      apply List.perm_middle.trans
      apply (hrest.cons (size + 1)).trans
      simpa [List.range'_concat, Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    let Domain := Σ index : Fin (size + 1), words index.val
    have (index : Fin (size + 1)) : Finite (words index.val) :=
      (finite_words _).to_subtype
    let emit : Domain → words (size + 1) := fun input =>
      ⟨block input.1.val input.2.val, blockMember _ (by omega) _ input.2.property⟩
    have blockCut (cut : ℕ) (hcut : cut ≤ size) (word : List ℕ) :
        (block cut word).idxOf (size + 1) = size - cut := by
      have hnot : size + 1 ∉ List.range' (cut + 1) (size - cut) := by
        intro hmem
        have := List.mem_range'.mp hmem
        omega
      simp [block, List.idxOf_append_of_notMem hnot]
    have emitInjective : Function.Injective emit := by
      rintro ⟨index, word⟩ ⟨otherIndex, otherWord⟩ heq
      have hwords := congrArg Subtype.val heq
      have hcuts := congrArg (List.idxOf (size + 1)) hwords
      change (block index.val word.val).idxOf (size + 1) =
        (block otherIndex.val otherWord.val).idxOf (size + 1) at hcuts
      rw [blockCut _ (by omega), blockCut _ (by omega)] at hcuts
      have hindex : index = otherIndex := Fin.ext (by omega)
      subst otherIndex
      apply congrArg (Sigma.mk index)
      apply Subtype.ext
      have hdrop := congrArg (List.drop (size - index.val + 1)) hwords
      have hdropRange : (List.range' (index.val + 1) (size - index.val)).drop
          (size - index.val + 1) = [] := by
        apply List.drop_eq_nil_of_le
        simp
      simpa [emit, block, List.drop_append, hdropRange] using hdrop
    have emitSurjective : Function.Surjective emit := by
      intro output
      obtain ⟨hperm, h132, h213⟩ := (membership _ _).mp output.property
      obtain ⟨parts, hpos, hsum, houtput⟩ :=
        Nonnesting.NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks (size + 1)
          output.val hperm h132 h213
      cases parts with
      | nil => simp at hsum
      | cons first parts =>
        have hfirst : 0 < first := hpos first (by simp)
        have hsize : first ≤ size + 1 := by simp only [List.sum_cons] at hsum; omega
        let cut := size + 1 - first
        have hcut : cut ≤ size := by dsimp [cut]; omega
        have htailSum : parts.sum = cut := by
          simp only [List.sum_cons] at hsum
          dsimp [cut]
          omega
        let tail := Nonnesting.NonnestingBasicRoyalIncBlocks.incBlocks cut parts
        have hsplit : output.val = List.range' (cut + 1) first ++ tail := by
          simpa only [Nonnesting.NonnestingBasicRoyalIncBlocks.incBlocks, cut, tail]
            using houtput
        have hrange : List.range' 1 cut ++ List.range' (cut + 1) first =
            List.range' 1 (size + 1) := by
          have hlen : cut + first = size + 1 := by dsimp [cut]; omega
          simpa [hlen, Nat.add_comm] using
            (List.range'_append_1 (s := 1) (m := cut) (n := first))
        have htailPerm : tail.Perm (List.range' 1 cut) := by
          have hcomm : (List.range' (cut + 1) first ++ tail).Perm
              (List.range' (cut + 1) first ++ List.range' 1 cut) := by
            apply (hsplit ▸ hperm).trans
            rw [← hrange]
            exact List.perm_append_comm
          exact (List.perm_append_left_iff _).mp hcomm
        have htailAvoid := Nonnesting.NonnestingBasicRoyalIncConverse.incBlocks_avoids cut
          parts (by intro part hpart; exact hpos part (by simp [hpart])) htailSum
        have htail : tail ∈ words cut := (membership _ _).mpr ⟨htailPerm, htailAvoid⟩
        refine ⟨⟨⟨cut, by omega⟩, ⟨tail, htail⟩⟩, Subtype.ext ?_⟩
        change block cut tail = output.val
        rw [hsplit]
        have hlen : first = size - cut + 1 := by dsimp [cut]; omega
        rw [hlen, List.range'_concat]
        simp [block, List.append_assoc, show cut + 1 + (size - cut) = size + 1 by omega]
    have hcard := Nat.card_congr (Equiv.ofBijective emit ⟨emitInjective, emitSurjective⟩)
    rw [Nat.card_sigma, Nat.card_coe_set_eq] at hcard
    simpa only [Nat.card_coe_set_eq] using hcard.symm
  have hzero : words 0 = {[]} := by
    ext word
    rw [membership]
    constructor
    · rintro ⟨hperm, _⟩
      have : word = [] := by simpa using hperm
      simp [this]
    · intro hword
      have : word = [] := by simpa using hword
      subst word
      refine ⟨List.Perm.refl _, ?_, ?_⟩
      all_goals
        rintro ⟨witness, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
  have cumulative (size : ℕ) : ∑ index : Fin (size + 1), (words index.val).ncard =
      2 ^ size := by
    induction size with
    | zero => simp [hzero]
    | succ size ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [recurrence size, ih, pow_succ]
      omega
  have hfinal := recurrence (n - 1)
  rw [cumulative] at hfinal
  simpa [words, Nat.sub_add_cancel hn] using hfinal

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
