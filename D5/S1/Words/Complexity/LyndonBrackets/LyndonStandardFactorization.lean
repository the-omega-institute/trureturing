/- GID: D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The longest Lyndon suffix gives the recursive standard factorization. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

open private list_lt_self_append from
  D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

variable {A : Type*} [LinearOrder A]

/-- The least positive cut whose suffix is Lyndon.  Thus its suffix has maximal length. -/
noncomputable def standardCut (w : List A) (hw : 2 ≤ w.length) : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)

/-- The prefix in the standard longest-Lyndon-suffix factorization. -/
noncomputable def standardLeft (w : List A) (hw : 2 ≤ w.length) : List A :=
  w.take (standardCut w hw)

/-- The longest proper Lyndon suffix in the standard factorization. -/
noncomputable def standardRight (w : List A) (hw : 2 ≤ w.length) : List A :=
  w.drop (standardCut w hw)

private theorem standardRight_longest_suffix (w : List A) (hw : 2 ≤ w.length)
    {v : List A} (hv : IsLyndon v) (hvw : v <:+ w) (hvwne : v ≠ w) :
    v.length ≤ (standardRight w hw).length := by
  rcases hvw with ⟨u, huv⟩
  have hu : u ≠ [] := by
    intro hu
    apply hvwne
    simpa [hu] using huv
  have hj0 : 0 < u.length := List.length_pos_of_ne_nil hu
  have hjl : u.length < w.length := by
    have hlen := congrArg List.length huv
    simp only [List.length_append] at hlen
    have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv.1
    omega
  have hcut : standardCut w hw ≤ u.length :=
    @Nat.find_min' _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)
      u.length ⟨hj0, hjl, by simpa [← huv] using hv⟩
  simp only [standardRight, List.length_drop]
  have hlen := congrArg List.length huv
  simp only [List.length_append] at hlen
  omega

private theorem lyndon_or_standardRight_le (w : List A) (hw : 2 ≤ w.length) :
    IsLyndon w ∨ standardRight w hw ≤ w := by
  let s := standardRight w hw
  have hs : IsLyndon s := by
    simpa [s, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)).2.2
  have hsLeSuffix {v : List A} (hv : v ≠ []) (hvs : v <:+ s) : s ≤ v := by
    rcases eq_or_ne v s with rfl | hvsne
    · exact le_rfl
    · exact ((isLyndon_iff_lt_suffix s).mp hs).2 v hv hvs hvsne |>.le
  have hsw : s <:+ w := ⟨standardLeft w hw, by
    simpa [s, standardLeft, standardRight] using
      List.take_append_drop (standardCut w hw) w⟩
  by_cases hws : w < s
  · left
    apply (isLyndon_iff_lt_suffix w).mpr
    refine ⟨by
      intro h
      simp [h] at hw, ?_⟩
    intro t ht htw htwne
    by_cases hlen : t.length ≤ s.length
    · have hts : t <:+ s :=
        List.suffix_of_suffix_length_le htw hsw hlen
      exact hws.trans_le (hsLeSuffix ht hts)
    · have hslt : s.length < t.length := lt_of_not_ge hlen
      have htltw : t.length < w.length := by
        exact lt_of_le_of_ne htw.length_le (by
          intro heq
          exact htwne (htw.eq_of_length heq))
      have htNot : ¬IsLyndon t := by
        intro htL
        have := standardRight_longest_suffix w hw htL htw htwne
        change t.length ≤ s.length at this
        omega
      have htTwo : 2 ≤ t.length := by
        have hspos : 0 < s.length := List.length_pos_of_ne_nil hs.1
        omega
      have hrec := lyndon_or_standardRight_le t htTwo
      have hrt : standardRight t htTwo ≤ t := hrec.resolve_left htNot
      let r := standardRight t htTwo
      have hrL : IsLyndon r := by
        simpa [r, standardRight, standardCut] using
          (@Nat.find_spec _ (Classical.decPred _)
            (exists_lyndon_suffix_cut t htTwo)).2.2
      have hrtSuffix : r <:+ t := ⟨standardLeft t htTwo, by
        simpa [r, standardLeft, standardRight] using
          List.take_append_drop (standardCut t htTwo) t⟩
      have hrwSuffix : r <:+ w := hrtSuffix.trans htw
      have hrwne : r ≠ w := by
        intro hrw
        have hlenrw := congrArg List.length hrw
        have hrle := hrtSuffix.length_le
        omega
      have hrlen : r.length ≤ s.length :=
        standardRight_longest_suffix w hw hrL hrwSuffix hrwne
      have hrs : r <:+ s :=
        List.suffix_of_suffix_length_le hrwSuffix hsw hrlen
      exact hws.trans_le ((hsLeSuffix hrL.1 hrs).trans hrt)
  · exact Or.inr (le_of_not_gt hws)
termination_by w.length
decreasing_by exact htltw

/-- In the longest-Lyndon-suffix factorization of a Lyndon word, the left
factor is itself Lyndon. -/
theorem isLyndon_standardLeft (w : List A) (hw : 2 ≤ w.length)
    (h : IsLyndon w) : IsLyndon (standardLeft w hw) := by
  let u := standardLeft w hw
  let v := standardRight w hw
  have hu : u ≠ [] := by
    rw [← List.length_pos_iff_ne_nil]
    simp only [u, standardLeft, List.length_take]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut w hw)
    change 0 < standardCut w hw ∧ standardCut w hw < w.length ∧ _ at hc
    omega
  have hv : v ≠ [] := by
    rw [← List.length_pos_iff_ne_nil]
    simp only [v, standardRight, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut w hw)
    change 0 < standardCut w hw ∧ standardCut w hw < w.length ∧ _ at hc
    omega
  have hvL : IsLyndon v := by
    simpa [v, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)).2.2
  have hfactor : u ++ v = w := by
    simpa [u, v, standardLeft, standardRight] using
      List.take_append_drop (standardCut w hw) w
  have hvwne : v ≠ w := by
    intro hvw
    have hlen := congrArg List.length hfactor
    simp only [hvw, List.length_append] at hlen
    have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
    omega
  have hwv : w < v :=
    ((isLyndon_iff_lt_suffix w).mp h).2 v hv
      ⟨u, hfactor⟩ hvwne
  have huv : u < v := by
    have huw : u < w := by
      rw [← hfactor]
      exact list_lt_self_append u hv
    exact huw.trans hwv
  by_contra huL
  change ¬IsLyndon u at huL
  have huTwo : 2 ≤ u.length := by
    have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
    have hone : u.length ≠ 1 := by
      intro hlen
      rcases List.length_eq_one_iff.mp hlen with ⟨a, ha⟩
      apply huL
      rw [ha]
      refine ⟨by simp, ?_⟩
      intro x y hx hy hxy
      have hlength := congrArg List.length hxy
      simp only [List.length_singleton, List.length_append] at hlength
      have hxPos : 0 < x.length := List.length_pos_of_ne_nil hx
      have hyPos : 0 < y.length := List.length_pos_of_ne_nil hy
      omega
    omega
  have hsu : standardRight u huTwo ≤ u :=
    (lyndon_or_standardRight_le u huTwo).resolve_left huL
  let s := standardRight u huTwo
  have hsL : IsLyndon s := by
    simpa [s, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _)
        (exists_lyndon_suffix_cut u huTwo)).2.2
  have hsv : s < v := hsu.trans_lt huv
  have hsvL : IsLyndon (s ++ v) := isLyndon_append hsL hvL hsv
  have hsuffix : s ++ v <:+ w := by
    refine ⟨standardLeft u huTwo, ?_⟩
    calc
      standardLeft u huTwo ++ (s ++ v) =
          (standardLeft u huTwo ++ s) ++ v := (List.append_assoc _ _ _).symm
      _ = u ++ v := by
        simpa [s, standardLeft, standardRight] using
          List.take_append_drop (standardCut u huTwo) u
      _ = w := hfactor
  have hsuffixne : s ++ v ≠ w := by
    intro heq
    have hlen := congrArg List.length heq
    have hleftpos : 0 < (standardLeft u huTwo).length := by
      simp only [standardLeft, List.length_take]
      have hc := @Nat.find_spec _ (Classical.decPred _)
        (exists_lyndon_suffix_cut u huTwo)
      change 0 < standardCut u huTwo ∧
        standardCut u huTwo < u.length ∧ _ at hc
      omega
    have hfactoru := congrArg List.length (show
      standardLeft u huTwo ++ standardRight u huTwo = u by
        simpa [standardLeft, standardRight] using
          List.take_append_drop (standardCut u huTwo) u)
    have hfactorw := congrArg List.length hfactor
    simp only [List.length_append] at hlen hfactoru hfactorw
    change (standardLeft u huTwo).length + s.length = u.length at hfactoru
    omega
  have hlong := standardRight_longest_suffix w hw hsvL hsuffix hsuffixne
  change (s ++ v).length ≤ v.length at hlong
  have hspos : 0 < s.length := List.length_pos_of_ne_nil hsL.1
  simp only [List.length_append] at hlong
  omega


end D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization
