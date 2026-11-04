/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/SourceCertificate
   generality: I
   mirror-B: none(waiver:physical-dependent-source-registration)
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual source strips, exact literal fresh cuts, and physical joint orders. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size sourceMod base oldValue newValue chain_values source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private branch Branch freshCut cut_bounds from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private bankWord inventory stock_good terminal_good genericBanks from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Banks
open private all_windows from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Arithmetic
open private insertAt from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private strip_of_prefix from
  D5.S3.Combinatorics.Circle.PeriodicShortening
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem word_totals (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    ((bankWord a b c d).map (oldValue a b c d)).sum=0 ∧
    ((insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)).map
      (newValue a b c d)).sum=0 := by
  have hp := inventory a b c d hb hba hac hd hda
  have ht := source_totals a b c d (by omega) hb (by omega) hd
  have hins :
      (insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)).Perm
        (bankWord a b c d++[size a b c d]) := by
    unfold insertAt
    have hs := (List.perm_append_singleton (size a b c d)
      ((bankWord a b c d).drop (freshCut a b c d))).symm.append_left
        ((bankWord a b c d).take (freshCut a b c d))
    simpa only [List.append_assoc,List.take_append_drop] using hs
  constructor
  · exact ((hp.map (oldValue a b c d)).sum_eq).trans ht.1
  · rw [(hins.map (newValue a b c d)).sum_eq]
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [(hp.map (newValue a b c d)).sum_eq,ht.2.1,ht.2.2]
    omega

private theorem old_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (bankWord a b c d) := by
  apply strip_of_prefix
  intro n
  have hp := inventory a b c d hb hba hac hd hda
  have ht := word_totals a b c d hb hba hac hd hda
  have hs := source_signs a b c d (by omega) hb (by omega) hd
  have hw := all_windows a b c d hb hba hac hd hda
  simp only [Set.mem_Icc]
  simp [bankWord,genericBanks,Branch,branch] at *
  omega

private theorem new_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)) := by
  apply strip_of_prefix
  intro n
  have hp := inventory a b c d hb hba hac hd hda
  have ht := word_totals a b c d hb hba hac hd hda
  have hs := source_signs a b c d (by omega) hb (by omega) hd
  have hw := all_windows a b c d hb hba hac hd hda
  simp only [Set.mem_Icc]
  simp [insertAt,bankWord,genericBanks,Branch,branch,freshCut] at *
  omega


private theorem physical_order (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    ∃ sigma : List (Fin (size a b c d)), ∃ j : ℕ,
      j=freshCut a b c d ∧ j<size a b c d ∧
      OriginalOrder (size a b c d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (size a b c d+1)
        (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (size a b c d) sigma j) := by
  have hk : 0<size a b c d := by dsimp [size]; omega
  have hp := inventory a b c d hb hba hac hd hda
  have ho : OriginalOrder (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c))
      ((bankWord a b c d).map (label (size a b c d) hk)) := by
    apply lift_order (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c)) hk (bankWord a b c d) hp
    · simpa [sourceMod] using old_strip a b c d hb hba hac hd hda
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [size]; omega)
  have half : modulus (size a b c d+1)/2=sourceMod a b c d := by
    dsimp [modulus,size,sourceMod]
    rw [pow_succ]
    simp only [pow_add]
    omega
  let pre := (bankWord a b c d).take (freshCut a b c d)
  let post := (bankWord a b c d).drop (freshCut a b c d)
  have hpre : pre.length=freshCut a b c d := by
    have hl := hp.length_eq
    simp only [List.length_range] at hl
    dsimp [pre]
    rw [List.length_take]
    exact Nat.min_eq_left (by omega)
  have hperm : (pre++size a b c d::post).Perm (List.range (size a b c d+1)) := by
    have hsplit := List.take_append_drop (freshCut a b c d) (bankWord a b c d)
    have h0 : (pre++size a b c d::post).Perm
        (bankWord a b c d++[size a b c d]) := by
      rw [←hsplit]
      simpa [List.append_assoc] using
        (List.perm_append_singleton (size a b c d) post).symm.append_left pre
    exact h0.trans (by simpa [List.range_succ] using hp.append_right [_])
  have hn : OriginalOrder (size a b c d+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+c)))
      ((pre++size a b c d::post).map
        (label (size a b c d+1) (by omega))) := by
    apply lift_order (size a b c d+1)
      (2*(1+2^a+2^(a+b)+2^(a+b+c))) (by omega)
      (pre++size a b c d::post) hperm
    · have he : insertAt (size a b c d) (bankWord a b c d)
          (freshCut a b c d) = pre++size a b c d::post := by
        simp [insertAt,pre,post,List.take_append_drop]
      simpa only [half,he] using new_strip a b c d hb hba hac hd hda
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [size]; omega)
  refine ⟨(bankWord a b c d).map (label (size a b c d) hk),
    freshCut a b c d,rfl,(cut_bounds a b c d hb hba hac hd hda).2,ho,?_⟩
  dsimp
  rw [←List.take_append_drop (freshCut a b c d) (bankWord a b c d)]
  rw [marked_word (size a b c d) (freshCut a b c d) hk pre post hpre (by simpa [pre,post] using hp)]
  exact hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
