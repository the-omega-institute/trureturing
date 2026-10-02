/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum
   mirror-E: none(waiver:fishburn-sum-boundary-analysis)
   anchors: []
   utility: none
   digest: Fishburn configurations in a direct sum localize to one component. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSum

open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum FishburnDefs

theorem isFishburn_directSum_iff (offset : ℕ) (left right : List ℕ)
    (hleft : ∀ value ∈ left, value ≤ offset)
    (hright : ∀ value ∈ right, 1 ≤ value) :
    IsFishburn (directSum offset left right) ↔ IsFishburn left ∧ IsFishburn right := by
  let word := directSum offset left right
  have hlength : word.length = left.length + right.length := by
    simp [word, directSum, shift]
  have hbefore (index : ℕ) (hindex : index < left.length) :
      word.getD index 0 = left.getD index 0 :=
    List.getD_append _ _ _ _ hindex
  have hafter (index : ℕ) (hlow : left.length ≤ index) (hhigh : index < word.length) :
      word.getD index 0 = right.getD (index - left.length) 0 + offset := by
    change (left ++ shift offset right).getD index 0 = _
    rw [List.getD_append_right _ _ _ _ hlow]
    have hindex : index - left.length < right.length := by omega
    rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hindex),
      List.getD_eq_getElem right 0 hindex]
    simp [shift]
  have hleftbound (index : ℕ) (hindex : index < left.length) :
      left.getD index 0 ≤ offset := by
    rw [List.getD_eq_getElem left 0 hindex]
    exact hleft _ (List.getElem_mem hindex)
  have hrightbound (index : ℕ) (hindex : index < right.length) :
      1 ≤ right.getD index 0 := by
    rw [List.getD_eq_getElem right 0 hindex]
    exact hright _ (List.getElem_mem hindex)
  dsimp only [word] at hlength hbefore hafter
  constructor
  · intro hword
    constructor
    · intro before later hgap hlater hbad
      apply hword before later hgap (by omega)
      simpa only [hbefore before (by omega), hbefore later hlater,
        hbefore (before + 1) (by omega)] using hbad
    · intro before later hgap hlater hbad
      apply hword (left.length + before) (left.length + later) (by omega) (by omega)
      rw [hafter (left.length + before) (by omega) (by omega),
        hafter (left.length + later) (by omega) (by omega),
        hafter (left.length + before + 1) (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left, Nat.add_assoc]
      constructor <;> omega
  · rintro ⟨hfishleft, hfishright⟩ before later hgap hlater hbad
    by_cases hlaterleft : later < left.length
    · apply hfishleft before later hgap hlaterleft
      simpa only [hbefore before (by omega), hbefore later hlaterleft,
        hbefore (before + 1) (by omega)] using hbad
    · by_cases hbeforeleft : before < left.length
      · have hsmall := hleftbound before hbeforeleft
        have hlarge := hrightbound (later - left.length) (by omega)
        rw [hbefore before hbeforeleft, hafter later (by omega) hlater] at hbad
        omega
      · apply hfishright (before - left.length) (later - left.length) (by omega)
          (by omega)
        rw [hafter before (by omega) (by omega), hafter later (by omega) hlater,
          hafter (before + 1) (by omega) (by omega)] at hbad
        have hnext : before + 1 - left.length = before - left.length + 1 := by omega
        rw [hnext] at hbad
        constructor <;> omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSum
