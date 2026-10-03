/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration
   mirror-E: none(waiver:ascending-minimum-counting-bijections)
   anchors: [mathlib/module/Mathlib.Data.Set.Card.Arithmetic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Minimum-split shuffles enumerate ascending-class words with a nonempty suffix. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEnumeration

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceAscending

theorem ascending_positive_suffix_count (width suffix : ℕ) (hsuffix : 1 ≤ suffix) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + suffix + 1)) ∧
      ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word ∧
      word.idxOf 1 = width ∧ ¬ (word.take width).Pairwise (· > ·)} :
      Set (List ℕ)).ncard = 2 ^ width - width - 1 := by
  classical
  let low := fun cut => (List.range' 2 cut).reverse
  let high := fun cut => (List.range' (cut + suffix + 2) (width - cut)).reverse
  let middle := fun cut => (List.range' (cut + 2) suffix).reverse
  let shuffles := fun cut => {word : List ℕ | word.Perm (low cut ++ high cut) ∧
    word.filter (fun value => decide (value < cut + 2)) = low cut ∧
    word.filter (fun value => !decide (value < cut + 2)) = high cut}
  let slices := fun cut => shuffles cut \ {high cut ++ low cut}
  let words := {word : List ℕ | word.Perm (List.range' 1 (width + suffix + 1)) ∧
    ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word ∧
    word.idxOf 1 = width ∧ ¬ (word.take width).Pairwise (· > ·)}
  have lowValues (cut value : ℕ) (hvalue : value ∈ low cut) :
      2 ≤ value ∧ value < cut + 2 := by
    simpa [Nat.add_comm] using List.mem_range'_1.mp (List.mem_reverse.mp hvalue)
  have highValues (cut value : ℕ) (hvalue : value ∈ high cut) :
      cut + suffix + 2 ≤ value ∧ value < cut + suffix + 2 + (width - cut) := by
    exact List.mem_range'_1.mp (List.mem_reverse.mp hvalue)
  have middleValues (cut value : ℕ) (hvalue : value ∈ middle cut) :
      cut + 2 ≤ value ∧ value < cut + suffix + 2 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      List.mem_range'_1.mp (List.mem_reverse.mp hvalue)
  have lowDesc (cut : ℕ) : (low cut).Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have highDesc (cut : ℕ) : (high cut).Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have middleDesc (cut : ℕ) : (middle cut).Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have canonicalDesc (cut : ℕ) : (high cut ++ low cut).Pairwise (· > ·) := by
    rw [List.pairwise_append]
    refine ⟨highDesc cut, lowDesc cut, ?_⟩
    intro upper hupper lower hlower
    have := highValues cut upper hupper
    have := lowValues cut lower hlower
    omega
  have canonicalMember (cut : ℕ) : high cut ++ low cut ∈ shuffles cut := by
    refine ⟨List.perm_append_comm, ?_, ?_⟩
    · rw [List.filter_append]
      have hlow : (low cut).filter (fun value => decide (value < cut + 2)) = low cut :=
        List.filter_eq_self.mpr (by
          intro value hvalue
          simp [(lowValues cut value hvalue).2])
      have hhigh : (high cut).filter (fun value => decide (value < cut + 2)) = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro value hvalue
          have := highValues cut value hvalue
          simp; omega)
      simp [hhigh, hlow]
    · rw [List.filter_append]
      have hlow : (low cut).filter (fun value => !decide (value < cut + 2)) = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro value hvalue
          simp [(lowValues cut value hvalue).2])
      have hhigh : (high cut).filter (fun value => !decide (value < cut + 2)) = high cut :=
        List.filter_eq_self.mpr (by
          intro value hvalue
          have := highValues cut value hvalue
          simp; omega)
      simp [hhigh, hlow]
  have finite_shuffles (cut : ℕ) : (shuffles cut).Finite := by
    apply (List.finite_toSet (low cut ++ high cut).permutations).subset
    intro word hword
    exact List.mem_permutations.mpr hword.1
  have finite_slices (cut : ℕ) : (slices cut).Finite := (finite_shuffles cut).sdiff
  have sliceCount (cut : ℕ) (hcut : cut ≤ width) :
      (slices cut).ncard + 1 = width.choose cut := by
    have hsubset : {high cut ++ low cut} ⊆ shuffles cut := by
      intro word hword
      have : word = high cut ++ low cut := Set.mem_singleton_iff.mp hword
      subst word
      exact canonicalMember cut
    have hcount := Set.ncard_sdiff_add_ncard_of_subset hsubset (finite_shuffles cut)
    have hshuffle := shuffle_count (fun value => decide (value < cut + 2))
      (low cut) (high cut) (by
        intro value hvalue
        simp [(lowValues cut value hvalue).2]) (by
        intro value hvalue
        have := highValues cut value hvalue
        simp; omega)
    change (shuffles cut).ncard = _ at hshuffle
    have htotal : cut + (width - cut) = width := by omega
    simpa [slices, hshuffle, low, high, htotal] using hcount
  have prefixLength (cut : ℕ) (hcut : cut ≤ width) (word : List ℕ)
      (hword : word ∈ slices cut) : word.length = width := by
    have := hword.1.1.length_eq
    simp only [low, high, List.length_append, List.length_reverse, List.length_range'] at this
    omega
  have notDescending (cut : ℕ) (word : List ℕ) (hword : word ∈ slices cut) :
      ¬ word.Pairwise (· > ·) := by
    intro hdescending
    have heq : word = high cut ++ low cut :=
      (hword.1.1.trans List.perm_append_comm).eq_of_pairwise
        (by intro first last hfirst hlast; omega) hdescending (canonicalDesc cut)
    exact hword.2 (Set.mem_singleton_iff.mpr heq)
  let block := fun cut word => word ++ 1 :: middle cut
  have blockMember (cut : ℕ) (hcut : cut ≤ width) (word : List ℕ)
      (hword : word ∈ slices cut) : block cut word ∈ words := by
    have hlength := prefixLength cut hcut word hword
    have hp := hword.1.1
    have hnotOne : 1 ∉ word := by
      intro hmem
      rcases List.mem_append.mp (hp.mem_iff.mp hmem) with hlo | hhi
      · have := lowValues cut 1 hlo; omega
      · have := highValues cut 1 hhi; omega
    have hcombined : (low cut ++ middle cut ++ high cut).Perm
        (List.range' 2 (width + suffix)) := by
      apply ((List.reverse_perm _).append (List.reverse_perm _) |>.append
        (List.reverse_perm _)).trans
      have hfirst : List.range' 2 cut ++ List.range' (cut + 2) suffix =
          List.range' 2 (cut + suffix) := by
        simpa [Nat.add_comm] using List.range'_append_1 (s := 2) (m := cut) (n := suffix)
      have hsecond : List.range' 2 (cut + suffix) ++
          List.range' (cut + suffix + 2) (width - cut) =
          List.range' 2 (width + suffix) := by
        have hsum : cut + suffix + (width - cut) = width + suffix := by omega
        simpa only [show 2 + (cut + suffix) = cut + suffix + 2 by omega, hsum]
          using List.range'_append_1
          (s := 2) (m := cut + suffix) (n := width - cut)
      rw [hfirst, hsecond]
    have hperm : (block cut word).Perm (List.range' 1 (width + suffix + 1)) := by
      apply (List.perm_middle (a := 1) (l₁ := word) (l₂ := middle cut)).trans
      apply List.Perm.cons
      apply (hp.append_right _).trans
      have hswap : (low cut ++ high cut ++ middle cut).Perm
          (low cut ++ middle cut ++ high cut) := by
        simpa only [List.append_assoc] using
          ((List.Perm.refl (low cut)).append
            (List.perm_append_comm (l₁ := high cut) (l₂ := middle cut)))
      exact hswap.trans hcombined
    have hmiddle : cut + 2 ∈ middle cut := by
      simp only [middle, List.mem_reverse, List.mem_range'_1]
      omega
    have shuffleNormalForm (n : ℕ) (left right : List ℕ) (middle : ℕ)
        (hperm : (left ++ 1 :: right).Perm (List.range' 1 n))
        (hmiddle : middle ∈ right) (hascent : ¬ left.Pairwise (· > ·)) :
        (¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
          ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right)) ↔
        right.Pairwise (· > ·) ∧
          (∀ value ∈ left,
            (∀ other ∈ right, value < other) ∨ (∀ other ∈ right, other < value)) ∧
          (left.filter (fun value => decide (value < middle))).Pairwise (· > ·) ∧
          (left.filter (fun value => decide (middle < value))).Pairwise (· > ·) := by
      classical
      have hnodup := hperm.nodup_iff.mpr List.nodup_range'
      have hdisjoint : ∀ value ∈ left, value ∉ right := by
        intro value hvalue hright
        exact (List.nodup_append.mp hnodup).2.2 _ hvalue _ (by simp [hright]) rfl
      have hleast : ∀ value ∈ left ++ right, 1 < value := by
        intro value hvalue
        have hnot : value ≠ 1 := by
          rcases List.mem_append.mp hvalue with hl | hr
          · exact (List.nodup_append.mp hnodup).2.2 _ hl 1 (by simp)
          · exact fun heq => (List.nodup_cons.mp
              (List.nodup_append.mp hnodup).2.1).1 (heq ▸ hr)
        have hmem : value ∈ left ++ 1 :: right := by
          rcases List.mem_append.mp hvalue with hl | hr
          · exact List.mem_append_left _ hl
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
        omega
      constructor
      · intro havoid
        obtain ⟨_, hdescending, _⟩ := (minimum_split_ascending _ _ hnodup hleast).mp havoid
        obtain ⟨hinterval, hfilters⟩ := ascending_middle_interval n left right hperm
          havoid hascent
        refine ⟨hdescending, ?_, (hfilters middle hmiddle).1, (hfilters middle hmiddle).2⟩
        intro value hvalue
        have hne : value ≠ middle := fun heq => hdisjoint value hvalue (heq ▸ hmiddle)
        by_cases hlow : value < middle
        · left
          intro other hother
          have hneOther : value ≠ other := fun heq => hdisjoint value hvalue (heq ▸ hother)
          by_contra hnot
          have hgap : value ∈ right := hinterval other hother middle hmiddle value
            (by omega) hlow
          exact hdisjoint value hvalue hgap
        · right
          intro other hother
          have hneOther : value ≠ other := fun heq => hdisjoint value hvalue (heq ▸ hother)
          by_contra hnot
          have hgap : value ∈ right := hinterval middle hmiddle other hother value
            (by omega) (by omega)
          exact hdisjoint value hvalue hgap
      · rintro ⟨hdescending, houtside, hlowDescending, hhighDescending⟩
        have crossing (lower upper : ℕ) (hpair : [lower, upper].Sublist left)
            (horder : lower < upper) :
            (∀ other ∈ right, lower < other) ∧ (∀ other ∈ right, other < upper) := by
          have hlower : lower ∈ left := hpair.subset (by simp)
          have hupper : upper ∈ left := hpair.subset (by simp)
          have hneLow : lower ≠ middle := fun heq =>
            hdisjoint lower hlower (heq ▸ hmiddle)
          have hneHigh : upper ≠ middle := fun heq =>
            hdisjoint upper hupper (heq ▸ hmiddle)
          have hlow : lower < middle := by
            by_contra hnot
            have hfiltered : [lower, upper].Sublist
                (left.filter (fun value => decide (middle < value))) := by
              have := hpair.filter (fun value => decide (middle < value))
              simpa [show middle < lower by omega, show middle < upper by omega] using this
            have := List.pairwise_iff_forall_sublist.mp hhighDescending hfiltered
            omega
          have hhigh : middle < upper := by
            by_contra hnot
            have hfiltered : [lower, upper].Sublist
                (left.filter (fun value => decide (value < middle))) := by
              have := hpair.filter (fun value => decide (value < middle))
              simpa [show lower < middle by omega, show upper < middle by omega] using this
            have := List.pairwise_iff_forall_sublist.mp hlowDescending hfiltered
            omega
          constructor
          · rcases houtside lower hlower with hl | hh
            · exact hl
            · have := hh middle hmiddle
              omega
          · rcases houtside upper hupper with hl | hh
            · have := hl middle hmiddle
              omega
            · exact hh
        apply (minimum_split_ascending _ _ hnodup hleast).mpr
        refine ⟨⟨?_, ?_⟩, hdescending, ?_⟩
        · rintro ⟨witness, hincreasing, _, hsub, _⟩
          have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
          have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
          have firstPair := (by decide : [1, 2].Sublist [1, 2, 3]).map witness |>.trans hsub
          have lastPair := (by decide : [2, 3].Sublist [1, 2, 3]).map witness |>.trans hsub
          have hfirst := (crossing _ _ firstPair h12).2 middle hmiddle
          have hlast := (crossing _ _ lastPair h23).1 middle hmiddle
          omega
        · rintro ⟨witness, hincreasing, _, hsub, _⟩
          have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
          have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
          have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
          have firstPair := (by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness
            |>.trans hsub
          have lastPair := (by decide : [1, 2].Sublist [3, 4, 1, 2]).map witness
            |>.trans hsub
          have hfirst := (crossing _ _ firstPair h34).1 middle hmiddle
          have hlast := (crossing _ _ lastPair h12).2 middle hmiddle
          omega
        · intro lower upper hpair horder other hother
          exact ⟨(crossing _ _ hpair horder).1 other hother,
            (crossing _ _ hpair horder).2 other hother⟩
    have havoid : ¬ Occurs [1, 2, 3] (block cut word) ∧
        ¬ Occurs [3, 4, 1, 2] (block cut word) := by
      apply (shuffleNormalForm _ word (middle cut) (cut + 2) hperm
        hmiddle (notDescending cut word hword)).mpr
      refine ⟨middleDesc cut, ?_, ?_, ?_⟩
      · intro value hvalue
        rcases List.mem_append.mp (hp.mem_iff.mp hvalue) with hlo | hhi
        · left
          intro other hother
          have := lowValues cut value hlo
          have := middleValues cut other hother
          omega
        · right
          intro other hother
          have := highValues cut value hhi
          have := middleValues cut other hother
          omega
      · rw [hword.1.2.1]
        exact lowDesc cut
      · have hfilter : word.filter (fun value => decide (cut + 2 < value)) =
            word.filter (fun value => !decide (value < cut + 2)) := by
          apply List.filter_congr
          intro value hvalue
          rcases List.mem_append.mp (hp.mem_iff.mp hvalue) with hlo | hhi
          · have := lowValues cut value hlo
            simp [show ¬ cut + 2 < value by omega, show value < cut + 2 by omega]
          · have := highValues cut value hhi
            simp [show cut + 2 < value by omega, show ¬ value < cut + 2 by omega]
        rw [hfilter, hword.1.2.2]
        exact highDesc cut
    refine ⟨hperm, havoid.1, havoid.2, ?_, ?_⟩
    · simp [block, List.idxOf_append_of_notMem hnotOne, hlength]
    · simpa [block, hlength] using notDescending cut word hword
  let Domain := Σ cut : Fin (width + 1), slices cut.val
  have (cut : Fin (width + 1)) : Finite (slices cut.val) := (finite_slices _).to_subtype
  let emit : Domain → words := fun input =>
    ⟨block input.1.val input.2.val,
      blockMember _ (by omega) _ input.2.property⟩
  have emitInjective : Function.Injective emit := by
    rintro ⟨cut, word⟩ ⟨otherCut, otherWord⟩ heq
    have hwords := congrArg Subtype.val heq
    have hlength := prefixLength _ (by omega) _ word.property
    have hotherLength := prefixLength _ (by omega) _ otherWord.property
    have hright := congrArg (List.drop (width + 1)) hwords
    have hrightEq : middle cut.val = middle otherCut.val := by
      have hdrop : word.val.drop (width + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      have hotherDrop : otherWord.val.drop (width + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      simpa [emit, block, List.drop_append, hlength, hotherLength, hdrop, hotherDrop]
        using hright
    have hstarts := congrArg (fun tail : List ℕ => tail.reverse.head?) hrightEq
    have hcut : cut = otherCut := by
      apply Fin.ext
      have : cut.val + 2 = otherCut.val + 2 := by
        simpa [middle, List.head?_range', show suffix ≠ 0 by omega] using hstarts
      omega
    subst otherCut
    apply congrArg (Sigma.mk cut)
    apply Subtype.ext
    have hleft := congrArg (List.take width) hwords
    simpa [emit, block, hlength, hotherLength] using hleft
  have emitSurjective : Function.Surjective emit := by
    intro output
    obtain ⟨hperm, h123, h3412, hcut, hascent⟩ := output.property
    have hone : 1 ∈ output.val := hperm.mem_iff.mpr (by
      simp only [List.mem_range'_1]; omega)
    obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hone
    have hnodup : (left ++ 1 :: right).Nodup :=
      hsplit ▸ hperm.nodup_iff.mpr List.nodup_range'
    have hnotOne : 1 ∉ left := by
      intro hmem
      exact (List.nodup_append.mp hnodup).2.2 _ hmem 1 (by simp) rfl
    have hleftLength : left.length = width := by
      simpa [hsplit, List.idxOf_append_of_notMem hnotOne] using hcut
    have hrightLength : right.length = suffix := by
      have := hperm.length_eq
      simp only [hsplit, List.length_append, List.length_cons, List.length_range'] at this
      omega
    have hleftAscent : ¬ left.Pairwise (· > ·) := by
      simpa [hsplit, ← hleftLength] using hascent
    have ranks : ∃ low high : ℕ, 1 ≤ low ∧ 1 ≤ high ∧
        low + high + right.length + 1 = width + suffix + 1 ∧
        right = (List.range' (low + 2) right.length).reverse ∧
        left.filter (fun value => decide (value < low + 2)) =
          (List.range' 2 low).reverse ∧
        left.filter (fun value => decide (low + right.length + 1 < value)) =
          (List.range' (low + right.length + 2) high).reverse := by
      let size := width + suffix + 1
      have hperm : (left ++ 1 :: right).Perm (List.range' 1 size) := hsplit ▸ hperm
      have havoid : ¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
          ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right) := by
        simpa only [← hsplit] using And.intro h123 h3412
      have hascent := hleftAscent
      have hnonempty : right ≠ [] := by
        intro hnil
        simp [hnil] at hrightLength
        omega
      have hnodup := hperm.nodup_iff.mpr List.nodup_range'
      have hleftNodup := (List.nodup_append.mp hnodup).1
      have bounds (value : ℕ) (hvalue : value ∈ left ++ right) :
          2 ≤ value ∧ value ≤ size := by
        have hnot : value ≠ 1 := by
          rcases List.mem_append.mp hvalue with hl | hr
          · exact (List.nodup_append.mp hnodup).2.2 _ hl 1 (by simp)
          · exact fun heq => (List.nodup_cons.mp
              (List.nodup_append.mp hnodup).2.1).1 (heq ▸ hr)
        have hmem : value ∈ left ++ 1 :: right := by
          rcases List.mem_append.mp hvalue with hl | hr
          · exact List.mem_append_left _ hl
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
        omega
      obtain ⟨hconvex, hfilters⟩ := ascending_middle_interval size left right hperm havoid hascent
      obtain ⟨_, hdescending, sandwich⟩ := (minimum_split_ascending _ _ hnodup (by
        intro value hvalue
        exact (bounds value hvalue).1)).mp havoid
      have interval (word : List ℕ) (hnonempty : word ≠ [])
          (hdescending : word.Pairwise (· > ·))
          (hconvex : ∀ lower ∈ word, ∀ upper ∈ word, ∀ value,
            lower < value → value < upper → value ∈ word) :
          ∃ first, word = (List.range' first word.length).reverse := by
        classical
        cases word with
        | nil => contradiction
        | cons head tail =>
          have inhabited : ∃ value, value ∈ head :: tail := ⟨head, by simp⟩
          let first := Nat.find inhabited
          have hfirst : first ∈ head :: tail := Nat.find_spec inhabited
          have lower_bound (value : ℕ) (hvalue : value ∈ head :: tail) : first ≤ value :=
            Nat.find_min' inhabited hvalue
          have upper_bound (value : ℕ) (hvalue : value ∈ head :: tail) : value ≤ head := by
            rcases List.mem_cons.mp hvalue with rfl | htail
            · omega
            · have := (List.pairwise_cons.mp hdescending).1 value htail
              omega
          have endpoints : first ≤ head := lower_bound head (by simp)
          have membership (value : ℕ) : value ∈ head :: tail ↔
              value ∈ List.range' first (head + 1 - first) := by
            rw [List.mem_range'_1]
            constructor
            · intro hvalue
              have := lower_bound value hvalue
              have := upper_bound value hvalue
              omega
            · rintro ⟨hlower, hupper⟩
              by_cases heqFirst : value = first
              · exact heqFirst ▸ hfirst
              by_cases heqHead : value = head
              · simp [heqHead]
              exact hconvex first hfirst head (by simp) value (by omega) (by omega)
          have hperm : (head :: tail).Perm (List.range' first (head + 1 - first)).reverse := by
            apply (List.perm_ext_iff_of_nodup hdescending.nodup
              (List.nodup_reverse.mpr List.nodup_range')).mpr
            intro value
            simpa only [List.mem_reverse] using membership value
          have hlength : (head :: tail).length = head + 1 - first := by
            simpa using hperm.length_eq
          refine ⟨first, ?_⟩
          rw [hlength]
          exact hperm.eq_of_pairwise (by intro lower upper hfirst hsecond; omega)
            hdescending (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
      obtain ⟨first, hright⟩ := interval right hnonempty hdescending hconvex
      have hlength : 0 < right.length := List.length_pos_iff.mpr hnonempty
      have hfirst : first ∈ right := by
        rw [hright, List.mem_reverse]
        simp only [List.mem_range'_1]
        omega
      have hlast : first + right.length - 1 ∈ right := by
        rw [hright, List.mem_reverse]
        simp only [List.mem_range'_1, List.length_reverse, List.length_range']
        omega
      have hfirstBound := bounds first (by simp [hfirst])
      have hlastBound := bounds (first + right.length - 1) (by simp [hlast])
      let low := first - 2
      let high := size - low - right.length - 1
      have hfirstEq : first = low + 2 := by dsimp [low]; omega
      have hsum : low + high + right.length + 1 = size := by dsimp [low, high]; omega
      have hlowNodup := hleftNodup.filter (fun value => decide (value < low + 2))
      have hhighNodup := hleftNodup.filter
        (fun value => decide (low + right.length + 1 < value))
      have filter_membership (value : ℕ) :
          value ∈ left.filter (fun value => decide (value < low + 2)) ↔
            value ∈ List.range' 2 low := by
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
        constructor
        · rintro ⟨hvalue, hlt⟩
          have := bounds value (by simp [hvalue])
          omega
        · rintro ⟨hlo, hhi⟩
          have hmem : value ∈ left ++ 1 :: right := hperm.mem_iff.mpr
            (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
          have hnot : value ∉ right := by
            rw [hright, List.mem_reverse]
            intro hvalue
            have := List.mem_range'_1.mp hvalue
            omega
          rcases List.mem_append.mp hmem with hl | hr
          · exact ⟨hl, by omega⟩
          · simp only [List.mem_cons] at hr
            rcases hr with heq | hr
            · omega
            · exact False.elim (hnot hr)
      have high_membership (value : ℕ) :
          value ∈ left.filter (fun value => decide (low + right.length + 1 < value)) ↔
            value ∈ List.range' (low + right.length + 2) high := by
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
        constructor
        · rintro ⟨hvalue, hlt⟩
          have := bounds value (by simp [hvalue])
          omega
        · rintro ⟨hlo, hhi⟩
          have hmem : value ∈ left ++ 1 :: right := hperm.mem_iff.mpr
            (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
          have hnot : value ∉ right := by
            rw [hright, List.mem_reverse]
            intro hvalue
            have := List.mem_range'_1.mp hvalue
            omega
          rcases List.mem_append.mp hmem with hl | hr
          · exact ⟨hl, by omega⟩
          · simp only [List.mem_cons] at hr
            rcases hr with heq | hr
            · omega
            · exact False.elim (hnot hr)
      have hloDesc := (hfilters first hfirst).1
      have hhiDesc := (hfilters (first + right.length - 1) hlast).2
      have low_word : left.filter (fun value => decide (value < low + 2)) =
          (List.range' 2 low).reverse := by
        have hp : (left.filter (fun value => decide (value < low + 2))).Perm
            (List.range' 2 low).reverse := by
          apply (List.perm_ext_iff_of_nodup hlowNodup
            (List.nodup_reverse.mpr List.nodup_range')).mpr
          intro value
          simpa only [List.mem_reverse] using filter_membership value
        exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
          (by simpa [hfirstEq] using hloDesc)
          (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
      have high_word : left.filter (fun value => decide (low + right.length + 1 < value)) =
          (List.range' (low + right.length + 2) high).reverse := by
        have hp : (left.filter (fun value => decide (low + right.length + 1 < value))).Perm
            (List.range' (low + right.length + 2) high).reverse := by
          apply (List.perm_ext_iff_of_nodup hhighNodup
            (List.nodup_reverse.mpr List.nodup_range')).mpr
          intro value
          simpa only [List.mem_reverse] using high_membership value
        exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
          (by simpa [hfirstEq, show low + 2 + right.length - 1 = low + right.length + 1
            by omega] using hhiDesc)
          (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
      have hexists : ∃ lower upper, [lower, upper].Sublist left ∧ lower < upper := by
        rw [List.pairwise_iff_forall_sublist] at hascent
        push Not at hascent
        obtain ⟨lower, upper, hpair, hnot⟩ := hascent
        have hne : lower ≠ upper := by simpa using hleftNodup.sublist hpair
        exact ⟨lower, upper, hpair, by omega⟩
      obtain ⟨lower, upper, hpair, horder⟩ := hexists
      have hlower : lower ∈ left := hpair.subset (by simp)
      have hupper : upper ∈ left := hpair.subset (by simp)
      have hsandLow := (sandwich lower upper hpair horder first hfirst).1
      have hsandHigh := (sandwich lower upper hpair horder _ hlast).2
      have hlowerBound := bounds lower (by simp [hlower])
      have hupperBound := bounds upper (by simp [hupper])
      refine ⟨low, high, ?_, ?_, hsum, ?_, low_word, high_word⟩
      · omega
      · omega
      · simpa [hfirstEq] using hright
    obtain ⟨cut, top, _, _, hsum, hright, hlow, hhigh⟩ := ranks
    have hcutBound : cut ≤ width := by omega
    have htop : top = width - cut := by omega
    have hrightEq : right = middle cut := by simpa [middle, hrightLength] using hright
    have hlowEq : left.filter (fun value => decide (value < cut + 2)) = low cut := hlow
    have hhighEq : left.filter (fun value => !decide (value < cut + 2)) = high cut := by
      have hfilters : left.filter (fun value => !decide (value < cut + 2)) =
          left.filter (fun value => decide (cut + right.length + 1 < value)) := by
        apply List.filter_congr
        intro value hvalue
        have hnot : value ∉ right := by
          intro hr
          exact (List.nodup_append.mp hnodup).2.2 _ hvalue _ (by simp [hr]) rfl
        have hgap : ¬ (cut + 2 ≤ value ∧ value < cut + 2 + right.length) := by
          intro hbounds
          apply hnot
          rw [hright, List.mem_reverse, List.mem_range'_1]
          exact hbounds
        by_cases hlow : value < cut + 2
        · simp [hlow, show ¬ cut + right.length + 1 < value by omega]
        · simp [hlow, show cut + right.length + 1 < value by omega]
      rw [hfilters, hhigh, htop, hrightLength]
    have hleftPerm : left.Perm (low cut ++ high cut) := by
      have := List.filter_append_perm (fun value => decide (value < cut + 2)) left
      simpa only [hlowEq, hhighEq] using this.symm
    have hparent : left ∈ slices cut := by
      refine ⟨⟨hleftPerm, hlowEq, hhighEq⟩, ?_⟩
      intro heq
      have heq' : left = high cut ++ low cut := Set.mem_singleton_iff.mp heq
      exact hleftAscent (heq' ▸ canonicalDesc cut)
    refine ⟨⟨⟨cut, by omega⟩, ⟨left, hparent⟩⟩, Subtype.ext ?_⟩
    change block cut left = output.val
    simp only [block, ← hrightEq, ← hsplit]
  have hcard := Nat.card_congr (Equiv.ofBijective emit ⟨emitInjective, emitSurjective⟩)
  rw [Nat.card_sigma, Nat.card_coe_set_eq] at hcard
  have hsum : words.ncard + (width + 1) =
      ∑ cut : Fin (width + 1), ((slices cut.val).ncard + 1) := by
    rw [Finset.sum_add_distrib]
    simpa only [Nat.card_coe_set_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] using congrArg (· + (width + 1)) hcard.symm
  have htotal : words.ncard + (width + 1) = 2 ^ width := by
    rw [hsum]
    have hsumEq : (∑ cut : Fin (width + 1), ((slices cut.val).ncard + 1)) =
        ∑ cut : Fin (width + 1), width.choose cut.val := by
      apply Finset.sum_congr rfl
      intro cut _
      exact sliceCount cut.val (by omega)
    rw [hsumEq]
    simpa only [Fin.sum_univ_eq_sum_range] using Nat.sum_range_choose width
  change words.ncard = _
  omega

theorem ascending_decreasing_prefix_count (size : ℕ) :
    ({word : List ℕ | word.Perm (List.range' 1 (size + 1)) ∧
      ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word ∧
      (word.take (word.idxOf 1)).Pairwise (· > ·)} : Set (List ℕ)).ncard = 2 ^ size := by
  classical
  let base := (List.range' 2 size).reverse
  let subsets : Set (Finset ℕ) := ↑base.toFinset.powerset
  let words := {word : List ℕ | word.Perm (List.range' 1 (size + 1)) ∧
    ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word ∧
    (word.take (word.idxOf 1)).Pairwise (· > ·)}
  let first := fun selected : Finset ℕ => base.filter (fun value => decide (value ∈ selected))
  let last := fun selected : Finset ℕ => base.filter (fun value => !decide (value ∈ selected))
  let emit := fun selected : Finset ℕ => first selected ++ 1 :: last selected
  have hbaseNodup : base.Nodup := List.nodup_reverse.mpr List.nodup_range'
  have hbaseDescending : base.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have hbaseNotOne : 1 ∉ base := by simp [base, List.mem_range'_1]
  have firstNotOne (selected : Finset ℕ) : 1 ∉ first selected := by
    exact fun hmem => hbaseNotOne (List.filter_sublist.subset hmem)
  have emitCut (selected : Finset ℕ) : (emit selected).idxOf 1 = (first selected).length := by
    simp [emit, List.idxOf_append_of_notMem (firstNotOne selected)]
  have selectedRecovered (selected : Finset ℕ) (hselected : selected ∈ subsets) :
      (first selected).toFinset = selected := by
    have hsubset : selected ⊆ base.toFinset := Finset.mem_powerset.mp hselected
    ext value
    simp only [List.mem_toFinset, first, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hvalue => ⟨List.mem_toFinset.mp (hsubset hvalue), hvalue⟩⟩
  have descendingAvoids (word : List ℕ) (hword : word.Pairwise (· > ·)) :
      ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word := by
    constructor
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hlt : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have hpair := (by decide : [1, 2].Sublist [1, 2, 3]).map witness |>.trans hsub
      have := List.pairwise_iff_forall_sublist.mp hword hpair
      omega
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hlt : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have hpair := (by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness |>.trans hsub
      have := List.pairwise_iff_forall_sublist.mp hword hpair
      omega
  have emitMember (selected : Finset ℕ) : emit selected ∈ words := by
    have hp : (first selected ++ last selected).Perm (List.range' 2 size) :=
      (List.filter_append_perm _ base).trans (List.reverse_perm _)
    have hperm : (emit selected).Perm (List.range' 1 (size + 1)) := by
      exact (List.perm_middle (a := 1) (l₁ := first selected) (l₂ := last selected)).trans
        (hp.cons 1)
    have hleast : ∀ value ∈ first selected ++ last selected, 1 < value := by
      intro value hvalue
      have := List.mem_range'_1.mp (hp.mem_iff.mp hvalue)
      omega
    have hfirst := hbaseDescending.filter (fun value => decide (value ∈ selected))
    have hlast := hbaseDescending.filter (fun value => !decide (value ∈ selected))
    have havoid := (minimum_split_ascending _ _
      (hperm.nodup_iff.mpr List.nodup_range') hleast).mpr
      ⟨descendingAvoids _ hfirst, hlast, by
        intro lower upper hpair hlt
        have := List.pairwise_iff_forall_sublist.mp hfirst hpair
        omega⟩
    exact ⟨hperm, havoid.1, havoid.2, by simpa [emitCut, emit] using hfirst⟩
  have emitInjective (selected other : Finset ℕ) (hselected : selected ∈ subsets)
      (hother : other ∈ subsets) (heq : emit selected = emit other) : selected = other := by
    have hcuts := congrArg (List.idxOf 1) heq
    rw [emitCut, emitCut] at hcuts
    have hfirst := congrArg (List.take (first selected).length) heq
    have hfirstEq : first selected = first other := by
      simpa [emit, hcuts] using hfirst
    have := congrArg List.toFinset hfirstEq
    simpa [selectedRecovered selected hselected, selectedRecovered other hother] using this
  have emitSurjective (word : List ℕ) (hword : word ∈ words) :
      ∃ selected ∈ subsets, emit selected = word := by
    obtain ⟨hperm, h123, h3412, hdesc⟩ := hword
    have hone : 1 ∈ word := hperm.mem_iff.mpr (by simp)
    obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hone
    have hnodup : (left ++ 1 :: right).Nodup := hsplit ▸ hperm.nodup_iff.mpr List.nodup_range'
    have hleftNodup := (List.nodup_append.mp hnodup).1
    have hrightNodup := (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).2
    have hnotOne : 1 ∉ left := by
      intro hmem
      exact (List.nodup_append.mp hnodup).2.2 _ hmem 1 (by simp) rfl
    have hleftDesc : left.Pairwise (· > ·) := by
      simpa [hsplit, List.idxOf_append_of_notMem hnotOne] using hdesc
    have hleftRight : (left ++ right).Perm (List.range' 2 size) := by
      have hp : (1 :: (left ++ right)).Perm (List.range' 1 (size + 1)) :=
        (List.perm_middle (a := 1) (l₁ := left) (l₂ := right)).symm.trans (hsplit ▸ hperm)
      exact List.Perm.cons_inv hp
    have hleast : ∀ value ∈ left ++ right, 1 < value := by
      intro value hvalue
      have := List.mem_range'_1.mp (hleftRight.mem_iff.mp hvalue)
      omega
    have hrightDesc := ((minimum_split_ascending _ _ hnodup hleast).mp
      (by simpa only [← hsplit] using And.intro h123 h3412)).2.1
    have hsubset : left.toFinset ∈ subsets := by
      apply Finset.mem_powerset.mpr
      intro value hvalue
      have hmem := hleftRight.mem_iff.mp (List.mem_append_left _ (List.mem_toFinset.mp hvalue))
      exact List.mem_toFinset.mpr (List.mem_reverse.mpr hmem)
    have hfirstEq : first left.toFinset = left := by
      have hp : (first left.toFinset).Perm left := by
        apply (List.perm_ext_iff_of_nodup (hbaseNodup.filter _) hleftNodup).mpr
        intro value
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_toFinset]
        exact ⟨And.right, fun hvalue => ⟨List.mem_reverse.mpr
          (hleftRight.mem_iff.mp (List.mem_append_left _ hvalue)), hvalue⟩⟩
      exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
        (hbaseDescending.filter _) hleftDesc
    have hlastEq : last left.toFinset = right := by
      have hp : (last left.toFinset).Perm right := by
        apply (List.perm_ext_iff_of_nodup (hbaseNodup.filter _) hrightNodup).mpr
        intro value
        simp only [List.mem_filter, List.mem_toFinset]
        simp only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
        constructor
        · rintro ⟨hvalue, hnot⟩
          have hm := hleftRight.mem_iff.mpr (List.mem_reverse.mp hvalue)
          exact (List.mem_append.mp hm).resolve_left hnot
        · intro hvalue
          refine ⟨List.mem_reverse.mpr (hleftRight.mem_iff.mp
            (List.mem_append_right _ hvalue)), ?_⟩
          intro hl
          exact (List.nodup_append.mp hnodup).2.2 _ hl _ (by simp [hvalue]) rfl
      exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
        (hbaseDescending.filter _) hrightDesc
    exact ⟨left.toFinset, hsubset, by simpa only [emit, hfirstEq, hlastEq] using hsplit.symm⟩
  have hcard := Set.ncard_congr (s := subsets) (t := words) (fun selected _ => emit selected)
    (fun selected _ => emitMember selected) emitInjective (by
      intro word hword
      obtain ⟨selected, hselected, heq⟩ := emitSurjective word hword
      exact ⟨selected, hselected, heq⟩)
  have hsubsets : subsets.ncard = 2 ^ size := by
    simp only [subsets, Set.ncard_coe_finset, Finset.card_powerset,
      List.toFinset_card_of_nodup hbaseNodup, base, List.length_reverse, List.length_range']
  change words.ncard = _
  rw [← hcard, hsubsets]

theorem ascending_count (size : ℕ) :
    (Fishburn.FishburnClassicalDefs.classicalAvoiders size
      [[1, 2, 3], [3, 4, 1, 2]]).ncard =
      2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 := by
  classical
  let words := fun count => Fishburn.FishburnClassicalDefs.classicalAvoiders count
    [[1, 2, 3], [3, 4, 1, 2]]
  have member (count : ℕ) (word : List ℕ) : word ∈ words count ↔
      word.Perm (List.range' 1 count) ∧ ¬ Occurs [1, 2, 3] word ∧
        ¬ Occurs [3, 4, 1, 2] word := by
    simp [words, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have finite_words (count : ℕ) : (words count).Finite := by
    apply (List.finite_toSet (List.range' 1 count).permutations).subset
    intro word hword
    exact List.mem_permutations.mpr ((member _ _).mp hword).1
  have descendingAvoids (word : List ℕ) (hword : word.Pairwise (· > ·)) :
      ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word := by
    constructor
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hlt : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have hpair := (by decide : [1, 2].Sublist [1, 2, 3]).map witness |>.trans hsub
      have := List.pairwise_iff_forall_sublist.mp hword hpair
      omega
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hlt : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have hpair := (by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness |>.trans hsub
      have := List.pairwise_iff_forall_sublist.mp hword hpair
      omega
  have canonical (count : ℕ) : (List.range' 1 count).reverse ∈ words count := by
    exact (member _ _).mpr ⟨List.reverse_perm _, descendingAvoids _
      (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))⟩
  have shift (pattern word : List ℕ) (hpattern : pattern ∈ [[1, 2, 3], [3, 4, 1, 2]]) :
      Occurs pattern (word.map (1 + ·)) ↔ Occurs pattern word := by
    have hletters : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hletters]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (1 + ·)
      (by intro lower upper hlt; dsimp; omega)
  have recurrence (count : ℕ) : (words (count + 1)).ncard + 1 =
      2 ^ count + (words count).ncard +
        ∑ cut : Fin count, (2 ^ cut.val - cut.val - 1) := by
    let decreasing := {word ∈ words (count + 1) |
      (word.take (word.idxOf 1)).Pairwise (· > ·)}
    let terminal := {word ∈ words (count + 1) |
      ¬ (word.take (word.idxOf 1)).Pairwise (· > ·) ∧ word.idxOf 1 = count}
    let positive := fun cut : Fin count => {word ∈ words (count + 1) |
      word.idxOf 1 = cut.val ∧ ¬ (word.take cut.val).Pairwise (· > ·)}
    let parents := words count \ {(List.range' 1 count).reverse}
    have finite_decreasing : decreasing.Finite := (finite_words _).subset (by
      intro word hword; exact hword.1)
    have finite_terminal : terminal.Finite := (finite_words _).subset (by
      intro word hword; exact hword.1)
    have finite_positive (cut : Fin count) : (positive cut).Finite :=
      (finite_words _).subset (by intro word hword; exact hword.1)
    have decreasingCount : decreasing.ncard = 2 ^ count := by
      simpa only [decreasing, member, Set.mem_ofPred_eq, and_assoc] using
        ascending_decreasing_prefix_count count
    let extend := fun word : List ℕ => word.map (1 + ·) ++ [1]
    have extendMember (word : List ℕ) (hword : word ∈ parents) :
        extend word ∈ terminal := by
      obtain ⟨hperm, h123, h3412⟩ := (member _ _).mp hword.1
      have hlength : word.length = count := by simpa using hperm.length_eq
      have hp : (word.map (1 + ·)).Perm (List.range' 2 count) := by
        have hmap := hperm.map (1 + ·)
        rw [List.map_add_range'] at hmap
        exact hmap
      have hnotOne : 1 ∉ word.map (1 + ·) := by
        intro hmem
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hold)
        omega
      have hperm' : (extend word).Perm (List.range' 1 (count + 1)) := by
        have hp' : (word.map (1 + ·) ++ []).Perm (List.range' 2 count) := by
          simpa using hp
        have hc := hp'.cons 1
        change (1 :: (word.map (1 + ·) ++ [])).Perm (List.range' 1 (count + 1)) at hc
        exact (List.perm_middle (a := 1) (l₁ := word.map (1 + ·)) (l₂ := [])).trans hc
      have hleast : ∀ value ∈ word.map (1 + ·) ++ [], 1 < value := by
        intro value hvalue
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp (by simpa using hvalue)
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hold)
        omega
      have havoid := (minimum_split_ascending _ _
        (hperm'.nodup_iff.mpr List.nodup_range') hleast).mpr
        ⟨⟨fun hocc => h123 ((shift _ word (by simp)).mp hocc),
          fun hocc => h3412 ((shift _ word (by simp)).mp hocc)⟩, by simp, by simp⟩
      have hcut : (extend word).idxOf 1 = count := by
        simp [extend, List.idxOf_append_of_notMem hnotOne, hlength]
      refine ⟨(member _ _).mpr ⟨hperm', havoid⟩, ?_, hcut⟩
      intro hdescending
      have hmapDesc : (word.map (1 + ·)).Pairwise (· > ·) := by
        simpa [extend, hcut, hlength] using hdescending
      have hwordDesc : word.Pairwise (· > ·) := by
        exact (List.pairwise_map.mp hmapDesc).imp (by intro first last hlt; omega)
      have heq := (hperm.trans (List.reverse_perm _).symm).eq_of_pairwise
        (by intro first last hfirst hlast; omega) hwordDesc
        (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
      exact hword.2 (Set.mem_singleton_iff.mpr heq)
    have extendInjective (first last : List ℕ) (hfirst : first ∈ parents)
        (hlast : last ∈ parents) (heq : extend first = extend last) : first = last := by
      have hmaps := List.append_cancel_right heq
      exact (List.map_inj_right (by intro lower upper heq; omega)).mp hmaps
    have extendSurjective (word : List ℕ) (hword : word ∈ terminal) :
        ∃ parent, ∃ hparent : parent ∈ parents, extend parent = word := by
      obtain ⟨hmember, hascent, hcut⟩ := hword
      obtain ⟨hperm, h123, h3412⟩ := (member _ _).mp hmember
      have hone : 1 ∈ word := hperm.mem_iff.mpr (by simp)
      obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hone
      have hnodup : (left ++ 1 :: right).Nodup := hsplit ▸ hperm.nodup_iff.mpr List.nodup_range'
      have hnotOne : 1 ∉ left := by
        intro hmem
        exact (List.nodup_append.mp hnodup).2.2 _ hmem 1 (by simp) rfl
      have hleftLength : left.length = count := by
        simpa [hsplit, List.idxOf_append_of_notMem hnotOne] using hcut
      have hrightNil : right = [] := by
        have := hperm.length_eq
        simp only [hsplit, List.length_append, List.length_cons, List.length_range'] at this
        apply List.length_eq_zero_iff.mp
        omega
      subst right
      have hleftPerm : left.Perm (List.range' 2 count) := by
        have hp := (List.perm_middle (a := 1) (l₁ := left) (l₂ := [])).symm.trans
          (hsplit ▸ hperm)
        change (1 :: (left ++ [])).Perm (1 :: List.range' 2 count) at hp
        simpa only [List.append_nil] using List.Perm.cons_inv hp
      let parent := left.map (· - 1)
      have hrestore : parent.map (1 + ·) = left := by
        rw [List.map_map]
        have hmap : left.map ((1 + ·) ∘ (· - 1)) = left.map id := by
          apply List.map_congr_left
          intro value hvalue
          have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hvalue)
          dsimp; omega
        simpa using hmap
      have hparentPerm : parent.Perm (List.range' 1 count) := by
        have hmap := hleftPerm.map (fun value => value - 1)
        simpa only [parent, List.map_sub_range' (by omega : 1 ≤ 2), Nat.reduceSub] using hmap
      have hleftAvoid : ¬ Occurs [1, 2, 3] left ∧ ¬ Occurs [3, 4, 1, 2] left := by
        have hleast : ∀ value ∈ left ++ [], 1 < value := by
          intro value hvalue
          have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp (by simpa using hvalue))
          omega
        exact ((minimum_split_ascending _ _ hnodup hleast).mp
          (by simpa only [← hsplit] using And.intro h123 h3412)).1
      have hparent : parent ∈ parents := by
        refine ⟨(member _ _).mpr ⟨hparentPerm, ?_, ?_⟩, ?_⟩
        · exact fun hocc => hleftAvoid.1 (hrestore ▸ (shift _ parent (by simp)).mpr hocc)
        · exact fun hocc => hleftAvoid.2 (hrestore ▸ (shift _ parent (by simp)).mpr hocc)
        · intro heq
          have heq' : parent = (List.range' 1 count).reverse := Set.mem_singleton_iff.mp heq
          apply hascent
          have hparentDesc : parent.Pairwise (· > ·) := heq' ▸
            List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
          have hleftDesc : left.Pairwise (· > ·) := hrestore ▸ List.pairwise_map.mpr
            (hparentDesc.imp (by intro first last hlt; omega))
          rw [hcut, hsplit]
          simpa [hleftLength] using hleftDesc
      exact ⟨parent, hparent, by simpa only [extend, hrestore] using hsplit.symm⟩
    have hterminal := Set.ncard_congr (s := parents) (t := terminal) (fun word _ => extend word)
      extendMember extendInjective extendSurjective
    have terminalCount : terminal.ncard + 1 = (words count).ncard := by
      have hsubset : {(List.range' 1 count).reverse} ⊆ words count := by
        intro word hword
        exact Set.mem_singleton_iff.mp hword ▸ canonical count
      have := Set.ncard_sdiff_add_ncard_of_subset hsubset (finite_words count)
      simpa only [Set.ncard_singleton, ← hterminal] using this
    have positiveCount (cut : Fin count) : (positive cut).ncard =
        2 ^ cut.val - cut.val - 1 := by
      have hsum : cut.val + (count - cut.val) + 1 = count + 1 := by omega
      simpa only [hsum, positive, member, Set.mem_ofPred_eq, and_assoc] using
        ascending_positive_suffix_count cut.val (count - cut.val) (by omega)
    have hdecomp : words (count + 1) = decreasing ∪ (terminal ∪ ⋃ cut, positive cut) := by
      ext word
      constructor
      · intro hword
        by_cases hdesc : (word.take (word.idxOf 1)).Pairwise (· > ·)
        · exact Or.inl ⟨hword, hdesc⟩
        · right
          by_cases hcut : word.idxOf 1 = count
          · exact Or.inl ⟨hword, hdesc, hcut⟩
          · right
            have hperm := ((member _ _).mp hword).1
            have hone : 1 ∈ word := hperm.mem_iff.mpr (by simp)
            have hbound := List.idxOf_lt_length_of_mem hone
            have hlength : word.length = count + 1 := by simpa using hperm.length_eq
            exact Set.mem_iUnion.mpr ⟨⟨word.idxOf 1, by omega⟩, hword, rfl, hdesc⟩
      · rintro (hword | hword | hword)
        · exact hword.1
        · exact hword.1
        · obtain ⟨cut, hword⟩ := Set.mem_iUnion.mp hword
          exact hword.1
    have hdisjointD : Disjoint decreasing (terminal ∪ ⋃ cut, positive cut) := by
      rw [Set.disjoint_left]
      intro word hd ht
      rcases ht with ht | ht
      · exact ht.2.1 hd.2
      · obtain ⟨cut, ht⟩ := Set.mem_iUnion.mp ht
        exact ht.2.2 (ht.2.1 ▸ hd.2)
    have hdisjointT : Disjoint terminal (⋃ cut, positive cut) := by
      rw [Set.disjoint_left]
      intro word ht hp
      obtain ⟨cut, hp⟩ := Set.mem_iUnion.mp hp
      have := ht.2.2
      have := hp.2.1
      omega
    have hdisjointP : Pairwise (fun first last => Disjoint (positive first) (positive last)) := by
      intro first last hne
      rw [Set.disjoint_left]
      intro word hf hl
      apply hne
      exact Fin.ext (hf.2.1.symm.trans hl.2.1)
    have hpositiveFinite : (⋃ cut, positive cut).Finite :=
      Set.finite_iUnion finite_positive
    rw [hdecomp, Set.ncard_union_eq hdisjointD finite_decreasing
      (finite_terminal.union hpositiveFinite),
      Set.ncard_union_eq hdisjointT finite_terminal hpositiveFinite,
      Set.ncard_iUnion_of_finite finite_positive hdisjointP,
      finsum_eq_sum_of_fintype, decreasingCount]
    simp only [positiveCount]
    omega
  have empty : words 0 = {[]} := by
    ext word
    rw [member]
    constructor
    · rintro ⟨hperm, _⟩
      have : word = [] := by simpa using hperm
      simp [this]
    · intro hword
      have : word = [] := Set.mem_singleton_iff.mp hword
      subst word
      exact ⟨List.Perm.refl _, descendingAvoids [] (by simp)⟩
  have powers (count : ℕ) : count + 1 ≤ 2 ^ count := by
    induction count with
    | zero => simp
    | succ count ih => rw [pow_succ]; omega
  have sum_gaps (count : ℕ) :
      (∑ cut : Fin count, (2 ^ cut.val - cut.val - 1)) + 1 + (count + 1).choose 2 =
        2 ^ count := by
    induction count with
    | zero => simp
    | succ count ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hp := powers count
      have hc := Nat.choose_succ_succ' (count + 1) 1
      norm_num only at hc
      simp only [Nat.choose_one_right] at hc
      rw [hc, pow_succ]
      omega
  have enumeration (count : ℕ) :
      (words count).ncard + 2 * count + 1 + (count + 1).choose 3 = 2 ^ (count + 1) := by
    induction count with
    | zero => simp [empty, show Nat.choose 1 3 = 0 by decide]
    | succ count ih =>
      have hr := recurrence count
      have hs := sum_gaps count
      have hc := Nat.choose_succ_succ' (count + 1) 2
      norm_num only at hc
      rw [hc, pow_succ]
      omega
  have := enumeration size
  change (words size).ncard = _
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEnumeration
