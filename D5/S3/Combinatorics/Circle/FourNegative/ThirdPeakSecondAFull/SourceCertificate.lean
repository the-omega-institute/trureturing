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
open private size sourceMod base oldValue newValue chain_values source_signs source_totals negatives chainLength chainStart from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private x y z t AA BB LL KK SU SV SW full stock complement terminal q h H rho fmask jmask
  mmask Rmask deltaMask branch     
       isFinite
  freshCut cut_bounds cone_powers power_links branch_complete from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private bankWord stock_good terminal_good genericBanks finiteBanks inventory word_totals
  chamber_split labels_band_split labels_three_split from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Banks
open private window first_seams A_second A_seams C_seams B_second A2_B_third all_windows four_packet_strip finite_strips from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Arithmetic
open private packetChecks strip_iff_packetChecks from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private blocksWord from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private insertAt from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private strip_of_prefix from
  D5.S3.Combinatorics.Circle.PeriodicShortening
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem old_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (bankWord a b c d) := by
  by_cases hf : isFinite a b c d
  · exact (finite_strips a b c d hf).1
  apply strip_of_prefix
  intro n
  have hp := inventory a b c d hb hba hac hd hda
  have ht := word_totals a b c d hb hba hac hd hda
  have hs := source_signs a b c d (by omega) hb (by omega) hd
  have hw := all_windows a b c d hb hba hac hd hda
  simp [bankWord,genericBanks,Branch,branch] at *
  omega

private theorem new_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)) := by
  by_cases hf : isFinite a b c d
  · exact (finite_strips a b c d hf).2
  apply strip_of_prefix
  intro n
  have hp := inventory a b c d hb hba hac hd hda
  have ht := word_totals a b c d hb hba hac hd hda
  have hs := source_signs a b c d (by omega) hb (by omega) hd
  have hw := all_windows a b c d hb hba hac hd hda
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
  have hmod : modulus (size a b c d)=sourceMod a b c d := by
    dsimp [modulus,size,sourceMod]; ring
  have hmodnew : modulus (size a b c d+1)=2*sourceMod a b c d+1 := by
    dsimp [modulus,size,sourceMod]; ring
  have hseed : ((1+2^a+2^(a+b)+2^(a+b+c) : ℕ) : ℤ)=base a b c d 0 := by
    push_cast
    dsimp [base]
    ring
  have holdval : (fun i => centered (modulus (size a b c d))
      ((2:ℤ)^i*((1+2^a+2^(a+b)+2^(a+b+c) : ℕ) : ℤ)))=oldValue a b c d := by
    simp only [hmod,hseed,oldValue]
  have hnewval : (fun i => centered (modulus (size a b c d+1))
      ((2:ℤ)^i*((2*(1+2^a+2^(a+b)+2^(a+b+c)) : ℕ) : ℤ)))=newValue a b c d := by
    simp only [Nat.cast_mul,Nat.cast_ofNat,hmodnew,hseed,newValue]
  have ho : OriginalOrder (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c))
      ((bankWord a b c d).map (label (size a b c d) hk)) := by
    apply lift_order (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c)) hk (bankWord a b c d) hp
    · simpa only [holdval,hmod] using old_strip a b c d hb hba hac hd hda
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
    exact Nat.min_eq_left (by have := (cut_bounds a b c d hb hba hac hd hda).2; omega)
  have hperm : (pre++size a b c d::post).Perm (List.range (size a b c d+1)) := by
    have hsplit := List.take_append_drop (freshCut a b c d) (bankWord a b c d)
    have h0 : (pre++size a b c d::post).Perm
        (bankWord a b c d++[size a b c d]) := by
      have hs := (List.perm_append_singleton (size a b c d) post).symm.append_left pre
      have he : pre++post=bankWord a b c d := hsplit
      simpa only [←List.append_assoc,he] using hs
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
      simpa only [hnewval,half,he] using new_strip a b c d hb hba hac hd hda
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [size]; omega)
  refine ⟨(bankWord a b c d).map (label (size a b c d) hk),
    freshCut a b c d,rfl,(cut_bounds a b c d hb hba hac hd hda).2,ho,?_⟩
  rw [←List.take_append_drop (freshCut a b c d) (bankWord a b c d)]
  rw [marked_word (size a b c d) (freshCut a b c d) hk pre post hpre (by simpa [pre,post] using hp)]
  exact hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
