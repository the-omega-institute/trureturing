/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular
   mirror-E: none(waiver:canonical-circle-cut-counting)
   anchors: [mathlib/module/Mathlib.Data.List.Rotate, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Canonical circles and their cuts count full and all-but-one rotation avoidance. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDefs
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular

open D5.S3.Combinatorics
open RotationAvoidanceDefs Nonnesting.NonnestingDefs

def circularAvoiders (n : ℕ) (q : List ℕ) : Set (List ℕ) :=
  {p | p ∈ rotationAvoiders n n q ∧ p.head? = some 1}

def singleBadCircles (n : ℕ) (q : List ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ p.head? = some 1 ∧
    ∃ bad < n, ∀ cut < n, Occurs q (p.rotate cut) ↔ cut = bad}

theorem counting_cuts (n : ℕ) (hn : 0 < n) (q : List ℕ) :
    (rotationAvoiders n n q).ncard = n * (circularAvoiders n q).ncard ∧
      (rotationAvoiders n (n - 1) q).ncard =
        n * (circularAvoiders n q).ncard + (singleBadCircles n q).ncard := by
  classical
  have length_eq (p : List ℕ) (hp : p.Perm (List.range' 1 n)) : p.length = n := by
    simpa using hp.length_eq
  have nodup (p : List ℕ) (hp : p.Perm (List.range' 1 n)) : p.Nodup :=
    hp.nodup_iff.mpr (List.nodup_range' (s := 1) (n := n))
  have rotate_sum (p : List ℕ) (hp : p.Perm (List.range' 1 n)) (start cut : ℕ) :
      (p.rotate start).rotate cut = p.rotate ((start + cut) % n) := by
    rw [List.rotate_rotate, ← List.rotate_mod, length_eq p hp]
  have canonical_zero (p : List ℕ) (hp : p.Perm (List.range' 1 n))
      (hhead : p.head? = some 1) (cut : ℕ) (hcut : cut < n)
      (hrot : (p.rotate cut).head? = some 1) : cut = 0 := by
    have hlength := length_eq p hp
    have hcut' : cut < p.length := by omega
    have hzero : 0 < p.length := by omega
    have hget : p[cut]? = p[0]? := by
      rw [← List.head?_rotate hcut', ← List.head?_eq_getElem?, hhead, hrot]
    rw [List.getElem?_eq_getElem hcut', List.getElem?_eq_getElem hzero,
      Option.some.injEq] at hget
    exact (nodup p hp).getElem_inj_iff.mp hget
  have canonical_unique (first second : List ℕ)
      (hfirst : first.Perm (List.range' 1 n)) (hsecond : second.Perm (List.range' 1 n))
      (hfirstHead : first.head? = some 1) (hsecondHead : second.head? = some 1)
      (left right : ℕ) (hleft : left < n) (hright : right < n)
      (heq : first.rotate left = second.rotate right) : first = second ∧ left = right := by
    have hfirstLength := length_eq first hfirst
    have hsecondLength := length_eq second hsecond
    have hback := congrArg (fun p : List ℕ => p.rotate (n - left)) heq
    rw [List.rotate_rotate, List.rotate_rotate] at hback
    have hsum : left + (n - left) = n := by omega
    have hrotate : first.rotate n = first := by
      rw [← hfirstLength, List.rotate_length]
    rw [hsum, hrotate] at hback
    rw [← List.rotate_mod second, hsecondLength] at hback
    have hhead : (second.rotate ((right + (n - left)) % n)).head? = some 1 := by
      rw [← hback]
      exact hfirstHead
    have hzero := canonical_zero second hsecond hsecondHead
      ((right + (n - left)) % n) (Nat.mod_lt _ hn) hhead
    rw [hzero, List.rotate_zero] at hback
    refine ⟨hback, ?_⟩
    rw [← hback] at heq
    have hnonempty : first ≠ [] := by
      intro hempty
      simp [hempty] at hfirstLength
      omega
    have hcuts := (nodup first hfirst).rotate_congr hnonempty left right heq
    simpa [hfirstLength, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] using hcuts
  have canonical_exists (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
      ∃ (circle : List ℕ) (cut : ℕ), circle.Perm (List.range' 1 n) ∧
        circle.head? = some 1 ∧
        cut < n ∧ circle.rotate cut = p := by
    have hmem : 1 ∈ p := hp.mem_iff.mpr (by
      exact List.mem_range'.mpr ⟨0, hn, by simp⟩)
    have hposition : p.idxOf 1 < p.length := List.idxOf_lt_length_iff.mpr hmem
    have hlength := length_eq p hp
    refine ⟨p.rotate (p.idxOf 1), (n - p.idxOf 1) % n,
      (List.rotate_perm p _).trans hp, ?_, Nat.mod_lt _ hn, ?_⟩
    · rw [List.head?_rotate hposition]
      exact List.getElem?_idxOf hmem
    · rw [← hlength]
      conv_lhs => arg 2; rw [← List.length_rotate p (p.idxOf 1)]
      rw [List.rotate_mod, List.rotate_rotate, List.length_rotate]
      have hsum : p.idxOf 1 + (p.length - p.idxOf 1) = p.length := by omega
      rw [hsum, List.rotate_length]
  have good_rotation (p : List ℕ) (hp : p ∈ rotationAvoiders n n q) (start : ℕ) :
      p.rotate start ∈ rotationAvoiders n n q := by
    refine ⟨(List.rotate_perm p _).trans hp.1, ?_⟩
    intro cut hcut
    rw [rotate_sum p hp.1 start cut]
    exact hp.2 _ (Nat.mod_lt _ hn)
  let allCuts : (circularAvoiders n q) × Fin n → rotationAvoiders n n q :=
    fun pair => ⟨pair.1.val.rotate pair.2.val, good_rotation _ pair.1.property.1 _⟩
  have allCuts_injective : Function.Injective allCuts := by
    rintro ⟨⟨first, hfirst⟩, left⟩ ⟨⟨second, hsecond⟩, right⟩ heq
    have hwords : first.rotate left.val = second.rotate right.val := congrArg Subtype.val heq
    have hpair := canonical_unique first second hfirst.1.1 hsecond.1.1 hfirst.2 hsecond.2
      left.val right.val left.isLt right.isLt hwords
    exact Prod.ext (Subtype.ext hpair.1) (Fin.ext hpair.2)
  have allCuts_surjective : Function.Surjective allCuts := by
    rintro ⟨p, hp⟩
    obtain ⟨circle, cut, hcircle, hhead, hcut, heq⟩ := canonical_exists p hp.1
    have hgood : circle ∈ rotationAvoiders n n q := by
      have hback := good_rotation p hp (n - cut)
      rw [← heq, List.rotate_rotate] at hback
      have hsum : cut + (n - cut) = n := by omega
      have hrotate : circle.rotate n = circle := by
        rw [← length_eq circle hcircle, List.rotate_length]
      rw [hsum, hrotate] at hback
      exact hback
    refine ⟨⟨⟨circle, hgood, hhead⟩, ⟨cut, hcut⟩⟩, ?_⟩
    exact Subtype.ext heq
  have hfull := Nat.card_congr (Equiv.ofBijective allCuts
    ⟨allCuts_injective, allCuts_surjective⟩)
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin, Nat.card_coe_set_eq] at hfull
  have full_count : (rotationAvoiders n n q).ncard =
      n * (circularAvoiders n q).ncard := by
    simpa [Nat.mul_comm] using hfull.symm
  let lastBad : Set (List ℕ) :=
    {p | p ∈ rotationAvoiders n (n - 1) q ∧ Occurs q (p.rotate (n - 1))}
  have last_profile (p : List ℕ) (hp : p ∈ lastBad) :
      ∀ cut < n, Occurs q (p.rotate cut) ↔ cut = n - 1 := by
    intro cut hcut
    constructor
    · intro hbad
      by_contra hne
      exact hp.1.2 cut (by omega) hbad
    · rintro rfl
      exact hp.2
  have shifted_last (start cut : ℕ) (hstart : start < n) (hcut : cut < n) :
      (start + cut) % n = n - 1 ↔ cut = n - 1 - start := by
    by_cases hsmall : start + cut < n
    · rw [Nat.mod_eq_of_lt hsmall]
      omega
    · have hlarge : n ≤ start + cut := by omega
      have hbound : start + cut - n < n := by omega
      rw [Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hbound]
      omega
  have shifted_not_bad (bad cut : ℕ) (hbad : bad < n) (hcut : cut < n - 1) :
      (bad + 1 + cut) % n ≠ bad := by
    by_cases hsmall : bad + 1 + cut < n
    · rw [Nat.mod_eq_of_lt hsmall]
      omega
    · have hlarge : n ≤ bad + 1 + cut := by omega
      have hbound : bad + 1 + cut - n < n := by omega
      rw [Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hbound]
      omega
  let badCut (p : List ℕ) (hp : p ∈ singleBadCircles n q) : ℕ :=
    Classical.choose hp.2.2
  have badCut_spec (p : List ℕ) (hp : p ∈ singleBadCircles n q) :
      badCut p hp < n ∧ ∀ cut < n, Occurs q (p.rotate cut) ↔ cut = badCut p hp :=
    Classical.choose_spec hp.2.2
  have make_lastBad (p : List ℕ) (hp : p ∈ singleBadCircles n q) :
      p.rotate (badCut p hp + 1) ∈ lastBad := by
    have hbad := badCut_spec p hp
    refine ⟨⟨(List.rotate_perm p _).trans hp.1, ?_⟩, ?_⟩
    · intro cut hcut hoccurs
      rw [rotate_sum p hp.1] at hoccurs
      have heq := (hbad.2 _ (Nat.mod_lt _ hn)).mp hoccurs
      exact shifted_not_bad _ cut hbad.1 hcut heq
    · rw [rotate_sum p hp.1]
      have hsum : badCut p hp + 1 + (n - 1) = badCut p hp + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hbad.1]
      exact (hbad.2 _ hbad.1).mpr rfl
  let oneCut : singleBadCircles n q → lastBad := fun p =>
    ⟨p.val.rotate (badCut p.val p.property + 1), make_lastBad p.val p.property⟩
  have oneCut_injective : Function.Injective oneCut := by
    rintro ⟨first, hfirst⟩ ⟨second, hsecond⟩ heq
    have hwords : first.rotate (badCut first hfirst + 1) =
        second.rotate (badCut second hsecond + 1) := congrArg Subtype.val heq
    rw [← List.rotate_mod first, ← List.rotate_mod second,
      length_eq first hfirst.1, length_eq second hsecond.1] at hwords
    have hpair := canonical_unique first second hfirst.1 hsecond.1 hfirst.2.1 hsecond.2.1
      _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hwords
    exact Subtype.ext hpair.1
  have oneCut_surjective : Function.Surjective oneCut := by
    rintro ⟨p, hp⟩
    have hperm := hp.1.1
    have hmem : 1 ∈ p := hperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨0, hn, by simp⟩)
    have hposition : p.idxOf 1 < p.length := List.idxOf_lt_length_iff.mpr hmem
    have hlength := length_eq p hperm
    have hposition' : p.idxOf 1 < n := by omega
    let circle := p.rotate (p.idxOf 1)
    have hcircle : circle ∈ singleBadCircles n q := by
      refine ⟨(List.rotate_perm p _).trans hperm, ?_, n - 1 - p.idxOf 1, by omega, ?_⟩
      · dsimp [circle]
        rw [List.head?_rotate hposition]
        exact List.getElem?_idxOf hmem
      · intro cut hcut
        dsimp [circle]
        rw [rotate_sum p hperm, last_profile p hp _ (Nat.mod_lt _ hn)]
        exact shifted_last (p.idxOf 1) cut hposition' hcut
    have hbad : badCut circle hcircle = n - 1 - p.idxOf 1 := by
      have hknown : Occurs q (circle.rotate (n - 1 - p.idxOf 1)) := by
        dsimp [circle]
        rw [rotate_sum p hperm, last_profile p hp _ (Nat.mod_lt _ hn)]
        exact (shifted_last (p.idxOf 1) _ hposition' (by omega)).mpr rfl
      exact ((badCut_spec circle hcircle).2 _ (by omega)).mp hknown |>.symm
    refine ⟨⟨circle, hcircle⟩, Subtype.ext ?_⟩
    change circle.rotate (badCut circle hcircle + 1) = p
    rw [hbad]
    dsimp [circle]
    rw [List.rotate_rotate]
    have hsum : p.idxOf 1 + (n - 1 - p.idxOf 1 + 1) = n := by omega
    rw [hsum, ← hlength, List.rotate_length]
  have hone := Nat.card_congr (Equiv.ofBijective oneCut
    ⟨oneCut_injective, oneCut_surjective⟩)
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hone
  have finite_words (k : ℕ) : (rotationAvoiders n k q).Finite := by
    apply (List.finite_toSet ((List.range' 1 n).permutations)).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  have hsplit : rotationAvoiders n (n - 1) q = rotationAvoiders n n q ∪ lastBad := by
    ext p
    constructor
    · intro hp
      by_cases hbad : Occurs q (p.rotate (n - 1))
      · exact Or.inr ⟨hp, hbad⟩
      · left
        refine ⟨hp.1, ?_⟩
        intro cut hcut
        by_cases hlast : cut = n - 1
        · simpa [hlast] using hbad
        · exact hp.2 cut (by omega)
    · rintro (hp | hp)
      · exact ⟨hp.1, fun cut hcut => hp.2 cut (by omega)⟩
      · exact hp.1
  have hdisjoint : Disjoint (rotationAvoiders n n q) lastBad := by
    apply Set.disjoint_left.mpr
    intro p hp hbad
    exact hp.2 (n - 1) (by omega) hbad.2
  have hfiniteLast : lastBad.Finite := (finite_words (n - 1)).subset (fun _ hp => hp.1)
  refine ⟨full_count, ?_⟩
  rw [hsplit, Set.ncard_union_eq hdisjoint (finite_words n) hfiniteLast, full_count, ← hone]

theorem unique_bad_cut_iff (n : ℕ) (hn : 4 ≤ n) (q p : List ℕ)
    (hq : q.Perm [1, 2, 3, 4]) (hp : p.Perm (List.range' 1 n)) :
    (∀ cut < n, Occurs q (p.rotate cut) ↔ cut = 0) ↔
      Occurs q p ∧ (∀ shift, 0 < shift → shift < 4 → ¬ Occurs (q.rotate shift) p) ∧
        ¬ Occurs q p.tail ∧ ¬ Occurs q p.dropLast := by
  have hlength : p.length = n := by simpa using hp.length_eq
  have hqLength : q.length = 4 := by simpa using hq.length_eq
  have hnonempty : p ≠ [] := by
    intro hempty
    simp [hempty] at hlength
    omega
  have letters_four (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) : letters r = 4 := by
    simpa [letters] using hr.foldr_eq (f := max) 0
  have rotated_pattern (shift : ℕ) : (q.rotate shift).Perm [1, 2, 3, 4] :=
    (List.rotate_perm q shift).trans hq
  have occurrence_from_sublist (r w : List ℕ) (witness : ℕ → ℕ)
      (hr : r.Perm [1, 2, 3, 4])
      (hincreasing : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1))
      (hsub : (r.map witness).Sublist w) : Occurs r w := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa [letters_four r hr] using hincreasing
    · intro rank hlow hhigh
      rw [letters_four r hr] at hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hr.mem_iff.mpr
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp
  have occurrence_mono (r u v : List ℕ) (hsub : u.Sublist v) :
      Occurs r u → Occurs r v := by
    rintro ⟨witness, hincreasing, hmem, hselected, _⟩
    exact ⟨witness, hincreasing, fun rank hlow hhigh =>
      hsub.subset (hmem rank hlow hhigh), hselected.trans hsub, by simp⟩
  constructor
  · intro hcuts
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using (hcuts 0 (by omega)).mpr rfl
    · intro shift hshift hshiftBound hoccurs
      obtain ⟨witness, hincreasing, _, hselected, _⟩ := hoccurs
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
          witness rank < witness (rank + 1) := by
        simpa [letters_four _ (rotated_pattern shift)] using hincreasing
      let selected := (q.rotate shift).map witness
      have hselectedLength : selected.length = 4 := by simp [selected, hqLength]
      have hselectedSplit :
          (selected.take (4 - shift) ++ selected.drop (4 - shift)).Sublist p := by
        rw [List.take_append_drop]
        exact hselected
      obtain ⟨left, right, hsplit, hleft, hright⟩ :=
        List.append_sublist_iff.mp hselectedSplit
      have hleftLength := hleft.length_le
      have hrightLength := hright.length_le
      have htotal : left.length + right.length = n := by
        simpa [hsplit] using hlength
      have hprefix : (selected.take (4 - shift)).length = 4 - shift := by
        simp [hselectedLength]
      have hsuffix : (selected.drop (4 - shift)).length = shift := by
        simp [hselectedLength]
        omega
      have hcut : 0 < left.length ∧ left.length < n := by
        rw [hprefix] at hleftLength
        rw [hsuffix] at hrightLength
        omega
      have hback : (q.map witness).Sublist (right ++ left) := by
        have hsub := hright.append hleft
        have hrotate : selected.rotate (4 - shift) =
            selected.drop (4 - shift) ++ selected.take (4 - shift) :=
          List.rotate_eq_drop_append_take (by rw [hselectedLength]; omega)
        rw [← hrotate] at hsub
        dsimp [selected] at hsub
        rw [← List.map_rotate, List.rotate_rotate] at hsub
        have hsum : shift + (4 - shift) = 4 := by omega
        rw [hsum, ← hqLength, List.rotate_length] at hsub
        exact hsub
      have hrotation : p.rotate left.length = right ++ left := by
        rw [hsplit, List.rotate_append_length_eq]
      have hbad : Occurs q (p.rotate left.length) := by
        rw [hrotation]
        exact occurrence_from_sublist q _ witness hq hincreasing' hback
      have := (hcuts left.length hcut.2).mp hbad
      omega
    · intro htail
      have hsub : p.tail.Sublist (p.rotate 1) := by
        cases p with
        | nil => simp
        | cons first rest =>
          simpa only [List.tail_cons, List.rotate_cons_succ, List.rotate_zero] using
            List.sublist_append_left rest [first]
      have hbad := occurrence_mono q p.tail (p.rotate 1) hsub htail
      have := (hcuts 1 (by omega)).mp hbad
      omega
    · intro hdropLast
      have hsub : p.dropLast.Sublist (p.rotate (n - 1)) := by
        have hlastLength : p.dropLast.length = n - 1 := by
          rw [List.length_dropLast, hlength]
        have hrotate : p.rotate (n - 1) = [p.getLast hnonempty] ++ p.dropLast := by
          rw [← hlastLength]
          conv_lhs => arg 1; rw [← List.dropLast_concat_getLast hnonempty]
          rw [List.rotate_append_length_eq]
        rw [hrotate]
        exact List.sublist_append_right _ _
      have hbad := occurrence_mono q p.dropLast (p.rotate (n - 1)) hsub hdropLast
      have := (hcuts (n - 1) (by omega)).mp hbad
      omega
  · rintro ⟨hoccurs, hcycles, htail, hdropLast⟩ cut hcut
    constructor
    · intro hbad
      by_contra hcutZero
      obtain ⟨witness, hincreasing, _, hselected, _⟩ := hbad
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
          witness rank < witness (rank + 1) := by
        simpa [letters_four q hq] using hincreasing
      rw [List.rotate_eq_drop_append_take (by omega : cut ≤ p.length)] at hselected
      obtain ⟨left, right, hsplit, hleft, hright⟩ := List.sublist_append_iff.mp hselected
      have htotal : left.length + right.length = 4 := by
        have := congrArg List.length hsplit
        simpa [hqLength] using this.symm
      have hback : ((q.rotate left.length).map witness).Sublist p := by
        rw [List.map_rotate, hsplit, List.rotate_append_length_eq,
          ← List.take_append_drop cut p]
        exact hright.append hleft
      by_cases hleftZero : left.length = 0
      · have hleftNil : left = [] := List.length_eq_zero_iff.mp hleftZero
        have hsub : (q.map witness).Sublist (p.take cut) := by
          rw [hsplit, hleftNil, List.nil_append]
          exact hright
        have htake : (p.take cut).Sublist p.dropLast := by
          rw [List.dropLast_eq_take]
          have hmin : min cut (p.length - 1) = cut := by omega
          have htaken := List.take_sublist cut (p.take (p.length - 1))
          rwa [List.take_take, hmin] at htaken
        exact hdropLast (occurrence_from_sublist q _ witness hq hincreasing'
          (hsub.trans htake))
      · by_cases hleftFour : left.length = 4
        · have hrightNil : right = [] := List.length_eq_zero_iff.mp (by omega)
          have hsub : (q.map witness).Sublist (p.drop cut) := by
            rw [hsplit, hrightNil, List.append_nil]
            exact hleft
          have hdrop : (p.drop cut).Sublist p.tail := by
            have hdropEq : p.tail.drop (cut - 1) = p.drop cut := by
              rw [← List.drop_one, List.drop_drop]
              congr 1
              omega
            exact hdropEq ▸ List.drop_sublist (cut - 1) p.tail
          exact htail (occurrence_from_sublist q _ witness hq hincreasing'
            (hsub.trans hdrop))
        · exact hcycles left.length (by omega) (by omega)
            (occurrence_from_sublist _ p witness (rotated_pattern left.length)
              hincreasing' hback)
    · rintro rfl
      simpa using hoccurs

theorem all_cuts_iff_cycle_avoidance (n : ℕ) (hn : 0 < n) (q p : List ℕ)
    (hq : q.Perm [1, 2, 3, 4]) (hp : p.Perm (List.range' 1 n)) :
    p ∈ rotationAvoiders n n q ↔ ∀ shift < 4, ¬ Occurs (q.rotate shift) p := by
  have hlength : p.length = n := by simpa using hp.length_eq
  have hqLength : q.length = 4 := by simpa using hq.length_eq
  have letters_four (r : List ℕ) (hr : r.Perm [1, 2, 3, 4]) : letters r = 4 := by
    simpa [letters] using hr.foldr_eq (f := max) 0
  have rotated_pattern (shift : ℕ) : (q.rotate shift).Perm [1, 2, 3, 4] :=
    (List.rotate_perm q shift).trans hq
  have occurrence_from_sublist (r w : List ℕ) (witness : ℕ → ℕ)
      (hr : r.Perm [1, 2, 3, 4])
      (hincreasing : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1))
      (hsub : (r.map witness).Sublist w) : Occurs r w := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa [letters_four r hr] using hincreasing
    · intro rank hlow hhigh
      rw [letters_four r hr] at hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hr.mem_iff.mpr
      have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp
  constructor
  · intro hall shift hshift hoccurs
    by_cases hshiftZero : shift = 0
    · rw [hshiftZero, List.rotate_zero] at hoccurs
      exact hall.2 0 hn (by simpa using hoccurs)
    · obtain ⟨witness, hincreasing, _, hselected, _⟩ := hoccurs
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
          witness rank < witness (rank + 1) := by
        simpa [letters_four _ (rotated_pattern shift)] using hincreasing
      let selected := (q.rotate shift).map witness
      have hselectedLength : selected.length = 4 := by simp [selected, hqLength]
      have hselectedSplit :
          (selected.take (4 - shift) ++ selected.drop (4 - shift)).Sublist p := by
        rw [List.take_append_drop]
        exact hselected
      obtain ⟨left, right, hsplit, hleft, hright⟩ :=
        List.append_sublist_iff.mp hselectedSplit
      have hrightLength := hright.length_le
      have htotal : left.length + right.length = n := by
        simpa [hsplit] using hlength
      have hsuffix : (selected.drop (4 - shift)).length = shift := by
        simp [hselectedLength]
        omega
      have hcut : left.length < n := by
        rw [hsuffix] at hrightLength
        omega
      have hback : (q.map witness).Sublist (right ++ left) := by
        have hsub := hright.append hleft
        have hrotate : selected.rotate (4 - shift) =
            selected.drop (4 - shift) ++ selected.take (4 - shift) :=
          List.rotate_eq_drop_append_take (by rw [hselectedLength]; omega)
        rw [← hrotate] at hsub
        dsimp [selected] at hsub
        rw [← List.map_rotate, List.rotate_rotate] at hsub
        have hsum : shift + (4 - shift) = 4 := by omega
        rw [hsum, ← hqLength, List.rotate_length] at hsub
        exact hsub
      apply hall.2 left.length hcut
      have hrotation : p.rotate left.length = right ++ left := by
        rw [hsplit, List.rotate_append_length_eq]
      rw [hrotation]
      exact occurrence_from_sublist q _ witness hq hincreasing' hback
  · intro hcycles
    refine ⟨hp, ?_⟩
    intro cut hcut hbad
    obtain ⟨witness, hincreasing, _, hselected, _⟩ := hbad
    have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
        witness rank < witness (rank + 1) := by
      simpa [letters_four q hq] using hincreasing
    rw [List.rotate_eq_drop_append_take (by omega : cut ≤ p.length)] at hselected
    obtain ⟨left, right, hsplit, hleft, hright⟩ := List.sublist_append_iff.mp hselected
    have htotal : left.length + right.length = 4 := by
      have := congrArg List.length hsplit
      simpa [hqLength] using this.symm
    have hback : ((q.rotate left.length).map witness).Sublist p := by
      rw [List.map_rotate, hsplit, List.rotate_append_length_eq,
        ← List.take_append_drop cut p]
      exact hright.append hleft
    have hoccurs := occurrence_from_sublist _ p witness (rotated_pattern left.length)
      hincreasing' hback
    by_cases hleftFour : left.length = 4
    · have hrotate : q.rotate left.length = q := by
        rw [hleftFour, ← hqLength, List.rotate_length]
      rw [hrotate] at hoccurs
      exact hcycles 0 (by omega) (by simpa using hoccurs)
    · exact hcycles left.length (by omega) hoccurs

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
