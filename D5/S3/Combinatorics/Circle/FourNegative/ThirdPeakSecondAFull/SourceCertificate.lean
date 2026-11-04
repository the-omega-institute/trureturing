/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/SourceCertificate
   generality: I
   mirror-B: none(waiver:physical-dependent-source-registration)
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual source strips, exact literal fresh cuts, and physical joint orders. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
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
open private stock_mass complement_mass bankWord stock_good terminal_good genericBanks finiteBanks inventory word_totals
  chamber_split labels_band_split labels_three_split from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Banks
open private window first_seams A_second A_seams C_seams B_second A2_B_third all_windows four_packet_strip finite_strips from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Arithmetic
open private packetChecks strip_iff_packetChecks from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private blocksWord blocksWord_flatMap from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private insertAt from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private strip_of_prefix from
  D5.S3.Combinatorics.Circle.PeriodicShortening
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open private native_masses from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private nextBase nextNewBase newBase new_base_bounds from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private bases_identify new_bases_identify from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters

private theorem low_length (len off u : ℕ) (hu : u≤len) :
    (MaxPlusTwo.Chambers.chamberLabels len off (2^u-1)).length=u := by
  have hp : (MaxPlusTwo.Chambers.chamberLabels len off (2^u-1)).Perm
      (List.range' off u) := by
    apply (List.perm_ext_iff_of_nodup
      (MaxPlusTwo.Chambers.chamberLabels_nodup _ _ _) (List.nodup_range')).mpr
    intro i
    rw [MaxPlusTwo.Chambers.chamberLabels_mem,List.mem_range'_1]
    constructor
    · rintro ⟨e,he,hbit,rfl⟩
      have heu : e<u := by simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using hbit
      omega
    · rintro ⟨hlo,hhi⟩
      refine ⟨i-off,by omega,?_,by omega⟩
      simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
      omega
  simpa only [List.length_range'] using hp.length_eq

private theorem power_length (len off u : ℕ) (hu : u<len) :
    (MaxPlusTwo.Chambers.chamberLabels len off (2^u)).length=1 := by
  have hp : (MaxPlusTwo.Chambers.chamberLabels len off (2^u)).Perm [off+u] := by
    apply (List.perm_ext_iff_of_nodup
      (MaxPlusTwo.Chambers.chamberLabels_nodup _ _ _) (List.nodup_singleton _)).mpr
    intro i
    rw [MaxPlusTwo.Chambers.chamberLabels_mem,List.mem_singleton]
    constructor
    · rintro ⟨e,he,hbit,rfl⟩
      have heu : u=e := by simpa only [Nat.testBit_two_pow,decide_eq_true_eq] using hbit
      omega
    · rintro rfl
      exact ⟨u,hu,by simp,rfl⟩
  exact hp.length_eq

private theorem band_length (len off u v δ e : ℕ) (hu : u≤len) (hv : v≤u)
    (hδ : δ<2^v) (he : (MaxPlusTwo.Chambers.chamberLabels len off δ).length=e) :
    (MaxPlusTwo.Chambers.chamberLabels len off (2^u-2^v+δ)).length=u-v+e ∧
    (MaxPlusTwo.Chambers.chamberLabels len off ((2^len-1) ^^^ (2^u-1))).length=len-u := by
  have hcap : 2^u-1<2^len := by
    have hp := Nat.pow_le_pow_right Nat.zero_lt_two hu
    have hz := Nat.two_pow_pos u
    omega
  have houter := (chamber_split len off (2^u-1) hcap).length_eq
  rw [List.length_append,List.length_range',low_length len off u hu] at houter
  have hinner := (MaxPlusTwo.Chambers.chamberLabels_split len off (2^v-1) δ (by
    intro k hk hb
    have hkv : k<v := by
      by_contra hn
      have hbit : δ.testBit k=false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hδ (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      rw [hbit] at hb
      contradiction
    simpa [Nat.testBit_two_pow_sub_one] using hkv)).length_eq
  rw [List.length_append,low_length len off v (by omega),he] at hinner
  have hband := (labels_band_split len off u v δ hv hδ).length_eq
  simp only [List.length_append,MaxPlusTwo.Chambers.chamberLabels_full,List.length_range'] at hband
  constructor <;> omega

private theorem insert_positive (f : ℕ→ℤ) (k n : ℕ) (P : List ℕ)
    (hk : 0≤f k) (hp : ∀ i∈P,0≤f i) :
    (∀ i∈insertAt k P n,0≤f i) ∧
    ((insertAt k P n).map f).sum=(P.map f).sum+f k := by
  constructor
  · intro i hi
    simp only [insertAt,List.mem_append,List.mem_cons] at hi
    rcases hi with hi|rfl|hi
    · exact hp i (List.mem_of_mem_take hi)
    · exact hk
    · exact hp i (List.mem_of_mem_drop hi)
  · have hs := (List.perm_append_singleton k (P.drop n)).symm.append_left (P.take n)
    have he : (P.take n++k::P.drop n).Perm (P++[k]) := by
      simpa only [←List.append_assoc,List.take_append_drop] using hs
    simpa only [insertAt,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] using
      (he.map f).sum_eq

private theorem old_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (bankWord a b c d) := by
  by_cases hf : isFinite a b c d
  · exact (finite_strips a b c d hf).1
  have hn1 : (a,b,c,d)≠(4,2,5,2) := fun he => hf (Or.inl he)
  have hn2 : (a,b,c,d)≠(4,2,6,2) := fun he => hf (Or.inr (Or.inl he))
  have hn3 : (a,b,c,d)≠(5,2,6,2) := fun he => hf (Or.inr (Or.inr he))
  have hv := chain_values a b c d (by omega) hb (by omega) hd
  have hz := (word_totals a b c d hb hba hac hd hda).1
  have hw := all_windows a b c d hb hba hac hd hda
  have hN : 0≤sourceMod a b c d := by have := hv.1 0; omega
  have hs (r : Fin 4) (m i : ℕ) (hi : i∈stock a b c d r m) :
      0≤oldValue a b c d i := by
    obtain ⟨hi',hni⟩ := stock_good a b c d hb hba hac hd hda r m i hi
    have hsign := source_signs a b c d (by omega) hb (by omega) hd i hi'
    rw [if_neg hni] at hsign
    exact hsign.1.le
  have hsc (r : Fin 4) (m i : ℕ) (hi : i∈complement a b c d r m) :
      0≤oldValue a b c d i := hs r _ i hi
  have ht (r : Fin 4) : oldValue a b c d (terminal a b c d r)≤0 := by
    obtain ⟨hi,hn⟩ := terminal_good a b c d hb hba hac hd hda r
    have hsign := source_signs a b c d (by omega) hb (by omega) hd _ hi
    rw [if_pos hn] at hsign
    exact hsign.1.le
  have hval (r : Fin 4) (e : ℕ) (he : e<chainLength a b c d r-1) :
      oldValue a b c d (chainStart b c d r+e)=2^e*base a b c d r := by
    rw [hv.2.1 r e (by omega),if_pos (by omega)]
  have sm (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :=
    stock_mass a b c d r m hm (oldValue a b c d) (base a b c d) hval
  have cm (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :=
    complement_mass a b c d r m hm (oldValue a b c d) (base a b c d) hval
  have ti (r : Fin 4) : chainStart b c d r+(chainLength a b c d r-1)=
      terminal a b c d r := by fin_cases r <;> simp [chainStart,chainLength,terminal] <;> omega
  have nm (r : Fin 4) := native_masses a b c d (by omega) hb (by omega) hd r
  dsimp only at nm
  simp only [ti] at nm
  have row (r : Fin 4) :
      (full a b c d r : ℤ)*base a b c d r+oldValue a b c d (terminal a b c d r)=
        nextBase a b c d r-base a b c d r := (nm r).1
  have term (r : Fin 4) : 2*oldValue a b c d (terminal a b c d r)=
      nextBase a b c d r-sourceMod a b c d := (nm r).2.2.1
  have bi := bases_identify a b c d
  have r0 := row 0
  have r1 := row 1
  have r2 := row 2
  have r3 := row 3
  have t0 := term 0
  have t1 := term 1
  have t2 := term 2
  have t3 := term 3
  simp only [nextBase] at r0 r1 r2 r3 t0 t1 t2 t3
  simp only [bi.1,bi.2.1,bi.2.2.1,bi.2.2.2] at r0 r1 r2 r3 t0 t1 t2 t3
  change _=BB d a b-AA a b c at r0
  change _=LL a c d-BB d a b at r1
  change _=KK b c d-LL a c d at r2
  change _=AA a b c-KK b c d at r3
  change _=BB d a b-sourceMod a b c d at t0
  change _=LL a c d-sourceMod a b c d at t1
  change _=KK b c d-sourceMod a b c d at t2
  change _=AA a b c-sourceMod a b c d at t3
  have fp (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have s0 := sm 0 _ (fp 0)
  have s2 := sm 2 _ (fp 2)
  simp only [bi.1,bi.2.2.1] at s0 s2
  have powle {u v : ℕ} (h : u≤v) : 2^u≤(2:ℕ)^v := Nat.pow_le_pow_right Nat.zero_lt_two h
  have powlt {u v : ℕ} (h : u<v) : 2^u<(2:ℕ)^v := pow_lt_pow_right₀ (by decide) h
  have hh : 0<h b c := by dsimp [h]; positivity
  have hH : 0<H a c := by dsimp [H]; positivity
  have hHh : H a c≤h b c := by exact powle (by omega)
  have hhcap : h b c<2^(c-1) := by exact powlt (by omega)
  have hfpos : 0<fmask a d := by dsimp [fmask]; positivity
  have hfcap : fmask a d<2^(a-1) := by
    have pp : 0<(2:ℕ)^(a-d-2) := by positivity
    have pe : 4*(2:ℕ)^(a-d-2)≤2^(a-1) := by
      calc
        _ = 2^(a-d-2+2) := by rw [pow_add]; ring
        _ ≤ _ := powle (by omega)
    dsimp [fmask]; omega
  have m0 := cm 1 (h b c-1) (by simpa [chainLength] using (show h b c-1<2^(c-1) by omega))
  simp only [bi.2.1] at m0
  by_cases hbd : b≤d
  · have m1 := sm 1 (h b c-H a c) (by simpa [chainLength] using (show h b c-H a c<2^(c-1) by omega))
    have mH := sm 1 (H a c-1) (by simpa [chainLength] using (show H a c-1<2^(c-1) by omega))
    simp only [bi.2.1] at m1 mH
    have castH : ((h b c-H a c : ℕ):ℤ)=(h b c:ℤ)-(H a c:ℤ) := by omega
    have casth : ((h b c-1 : ℕ):ℤ)=(h b c:ℤ)-1 := by omega
    have castH1 : ((H a c-1 : ℕ):ℤ)=(H a c:ℤ)-1 := by omega
    rw [castH] at m1
    rw [casth] at m0
    rw [castH1] at mH
    by_cases ha1 : a=d+1
    · have hbr : branch a b c d=.a1 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_pos ha1]
      have mX := sm 3 1 (by change 1<(2:ℕ)^(a-1); simpa using powlt (show 0<a-1 by omega))
      simp only [bi.2.2.2,Nat.cast_one] at mX
      have z := hz
      simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at z
      simp only [bankWord,hbr]
      rw [←blocksWord_flatMap]
      dsimp only [genericBanks] 
      apply four_packet_strip _ _ (sourceMod a b c d) _ _ _ _ _ _ _ _ (LL a c d) (KK b c d) (AA a b c) (BB d a b)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
        · exact hsc 3 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 0 _ _ hi
            · exact hs 1 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (hv.1 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.1 using 1 <;> linear_combination m0+r1
      · convert (hw.2.1 hbd).1 using 1 <;> simp only [List.map_append,List.sum_append] <;> linear_combination m0+r1+m1+s2+r2
      · have he : (AA a b c-KK b c d-(H a c:ℤ)*BB d a b)=
            ((complement a b c d 1 (h b c-1)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 1)+
              ((stock a b c d 2 (full a b c d 2)++stock a b c d 1 (h b c-H a c)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 2)+
              ((complement a b c d 3 1).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 3) := by
          simp only [List.map_append,List.sum_append] at z ⊢
          linear_combination -(z)+s0+mH+mX+r0
        rw [←he]
        exact (hw.2.2.1 hbd ha1).1
      · simpa only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil,blocksWord,List.append_assoc,List.singleton_append] using hz
    · have hbr : branch a b c d=.a2 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_neg ha1]
      have mX := sm 3 (fmask a d) (by simpa [chainLength] using hfcap)
      simp only [bi.2.2.2] at mX
      have z := hz
      simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at z
      simp only [bankWord,hbr]
      rw [←blocksWord_flatMap]
      dsimp only [genericBanks]
      apply four_packet_strip _ _ (sourceMod a b c d) _ _ _ _ _ _ _ _ (LL a c d) (KK b c d) (AA a b c) (BB d a b)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hsc 3 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 0 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (hv.1 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.1 using 1 <;> linear_combination m0+r1
      · convert (hw.2.1 hbd).1 using 1 <;> simp only [List.map_append,List.sum_append] <;> linear_combination m0+r1+m1+s2+r2
      · have he : (AA a b c-(fmask a d:ℤ)*KK b c d-BB d a b)=
            ((complement a b c d 1 (h b c-1)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 1)+
              ((stock a b c d 2 (full a b c d 2)++stock a b c d 1 (h b c-H a c)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 2)+
              ((complement a b c d 3 (fmask a d)++stock a b c d 1 (H a c-1)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 3) := by
          simp only [List.map_append,List.sum_append] at z ⊢
          linear_combination -(z)+s0+mX+r0
        rw [←he]
        exact (hw.2.2.2.1 (by omega) (Or.inl ⟨hbd,hf⟩)).1
      · simpa only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil,blocksWord,List.append_assoc,List.singleton_append] using hz
  · by_cases hB : d+2≤b ∨ a+2≤c
    · have hB' : d+2≤b ∨ b=d+1 ∧ a+2≤c := by omega
      let δ := if d+2≤b then 0 else deltaMask a b c d
      let v3 := if d+2≤b then Rmask a b c d-1 else
        (Rmask a b c d-1) ^^^ deltaMask a b c d
      let J := min (a-b-1) (d-2)
      have hJ : jmask a b d=2^J := by
        dsimp [jmask,J]
        by_cases hle : a-b-1≤d-2
        · rw [Nat.min_eq_left hle,Nat.min_eq_left (powle hle)]
        · have hle' : d-2≤a-b-1 := by omega
          rw [Nat.min_eq_right hle',Nat.min_eq_right (powle hle')]
      have hR : Rmask a b c d=2^(c-a+J) := by
        dsimp [Rmask,q]; rw [hJ,←pow_add]
      have hRh : Rmask a b c d≤h b c := by
        rw [hR]; exact powle (by have := Nat.min_le_left (a-b-1) (d-2); dsimp [J] at *; omega)
      have hRpos : 0<Rmask a b c d := by rw [hR]; positivity
      have hδ : δ≤Rmask a b c d := by
        dsimp [δ,deltaMask]
        split_ifs
        · omega
        · omega
        · exact Nat.div_le_self _ _
      have hjpos : 0<jmask a b d := by rw [hJ]; positivity
      have hjcap : jmask a b d≤2^(a-1) := by
        rw [hJ]; exact powle (by have := Nat.min_le_left (a-b-1) (d-2); dsimp [J] at *; omega)
      have mV := sm 1 (h b c-Rmask a b c d+δ) (by change _<2^(c-1); omega)
      have mM := sm 3 (mmask a b d) (by change _<2^(a-1); dsimp [mmask]; omega)
      have mX := sm 3 (fmask a d) (by simpa [chainLength] using hfcap)
      simp only [bi.2.1] at mV
      simp only [bi.2.2.2] at mM mX
      have casth : ((h b c-1:ℕ):ℤ)=(h b c:ℤ)-1 := by omega
      have castV : ((h b c-Rmask a b c d+δ:ℕ):ℤ)=
          (h b c:ℤ)-(Rmask a b c d:ℤ)+(δ:ℤ) := by omega
      have castM : (mmask a b d:ℤ)=(jmask a b d:ℤ)-1 := by dsimp [mmask]; omega
      have castR : (Rmask a b c d:ℤ)=(q a c:ℤ)*(jmask a b d:ℤ) := by simp [Rmask]
      rw [casth] at m0
      rw [castV,castR] at mV
      rw [castM] at mM
      have heword : bankWord a b c d=blocksWord
          [(complement a b c d 1 (h b c-1),terminal a b c d 1),
           (stock a b c d 2 (full a b c d 2)++stock a b c d 3 (mmask a b d)++
             stock a b c d 1 (h b c-Rmask a b c d+δ),terminal a b c d 2),
           (complement a b c d 3 (mmask a b d ||| fmask a d)++stock a b c d 1 v3,
             terminal a b c d 3),
           (stock a b c d 0 (full a b c d 0)++stock a b c d 3 (fmask a d),terminal a b c d 0)] := by
        simp only [bankWord,branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd]
        by_cases hb0 : d+2≤b
        · simp [hb0,genericBanks,blocksWord,δ,v3,List.append_assoc]
        · have hc2 : a+2≤c := by omega
          simp only [if_neg hb0,if_pos hc2]
          split_ifs <;> simp [genericBanks,blocksWord,δ,v3,hb0,List.append_assoc]
      rw [heword] at hz ⊢
      have z := hz
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil] at z
      apply four_packet_strip _ _ (sourceMod a b c d) _ _ _ _ _ _ _ _
        (LL a c d) (KK b c d) (AA a b c) (BB d a b)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 2 _ _ hi
            · exact hs 3 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hsc 3 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 0 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (hv.1 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.1 using 1 <;> linear_combination m0+r1
      · have ww : window ((jmask a b d:ℤ)*(KK b c d-(q a c:ℤ)*BB d a b)+(δ:ℤ)*BB d a b) (KK b c d) := by
          by_cases hb0 : d+2≤b <;> simpa [δ,hb0] using (hw.2.2.2.2.1 hB').1
        convert ww using 1 <;> simp only [List.map_append,List.sum_append] <;>
          linear_combination m0+r1+s2+mM+mV+r2
      · have he : (AA a b c-(fmask a d:ℤ)*KK b c d-BB d a b)=
            ((complement a b c d 1 (h b c-1)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 1)+
              ((stock a b c d 2 (full a b c d 2)++stock a b c d 3 (mmask a b d)++
                stock a b c d 1 (h b c-Rmask a b c d+δ)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 2)+
              ((complement a b c d 3 (mmask a b d ||| fmask a d)++stock a b c d 1 v3).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 3) := by
          simp only [List.map_append,List.sum_append]
          linear_combination -z+s0+mX+r0
        rw [←he]
        exact (hw.2.2.2.1 (by omega) (Or.inr hB')).1
      · exact hz
    · have hbdC : b=d+1 := by omega
      have hca : c=a+1 := by omega
      have hbr : branch a b c d=.c := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,
          if_neg (show ¬d+2≤b by omega),if_neg (show ¬a+2≤c by omega)]
      have hrho : rho a d=4*2^(a-d-2) := by
        conv_lhs =>
          dsimp [rho]
          rw [show a-d=(a-d-2)+2 by omega,pow_add]
        ring
      have hM : 3*rho a d/4=fmask a d := by rw [hrho]; dsimp [fmask]; omega
      have hnu : rho a d/2=2^(a-d-1) := by
        conv_lhs =>
          dsimp [rho]
          rw [show a-d=(a-d-1)+1 by omega,pow_succ]
        omega
      have hnucap : rho a d/2<2^(c-1) := by rw [hnu]; exact powlt (by omega)
      have oneV : 1<2^(c-1) := by simpa using powlt (show 0<c-1 by omega)
      have oneW : 1<2^(b-1) := by simpa using powlt (show 0<b-1 by omega)
      have mC := cm 3 (3*rho a d/4-1) (by change _<2^(a-1); rw [hM]; omega)
      have mC' := sm 3 (3*rho a d/4-1) (by change _<2^(a-1); rw [hM]; omega)
      have mW := cm 2 1 (by simpa [chainLength] using oneW)
      have mW' := sm 2 1 (by simpa [chainLength] using oneW)
      have mV := sm 1 1 (by simpa [chainLength] using oneV)
      have mnu := sm 1 (rho a d/2) (by simpa [chainLength] using hnucap)
      simp only [bi.2.2.2] at mC mC'
      simp only [bi.2.2.1,Nat.cast_one,one_mul] at mW mW'
      simp only [bi.2.1,Nat.cast_one,one_mul] at mV mnu
      have castM : ((3*rho a d/4-1:ℕ):ℤ)=(fmask a d:ℤ)-1 := by rw [hM]; omega
      rw [castM] at mC mC'
      simp only [bankWord,hbr] at hz ⊢
      rw [←blocksWord_flatMap] at hz ⊢
      dsimp only [genericBanks] at hz ⊢
      have z := hz
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil] at z
      apply four_packet_strip _ _ (sourceMod a b c d) _ _ _ _ _ _ _ _
        (AA a b c) (KK b c d) (LL a c d) (BB d a b)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 3 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 3 _ _ hi
            · exact hsc 2 _ _ hi
          · exact hs 1 _ _ hi
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 0 _ _ hi
            · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 3
        · exact ht 2
        · exact ht 1
        · exact ht 0
      · exact t3
      · exact t2
      · exact t1
      · exact t0
      · have := (hv.1 1).1; rw [bi.2.1] at this; omega
      · convert (hw.2.2.2.2.2 hbdC hca).1 using 1 <;> linear_combination mC+r3
      · convert (hw.2.2.2.2.2 hbdC hca).2.2.1 using 1 <;>
          simp only [List.map_append,List.sum_append] <;> linear_combination mC+r3+mC'+mW+mV+r2
      · have he : (AA a b c-LL a c d-((rho a d/2:ℕ):ℤ)*BB d a b-BB d a b)=
            ((complement a b c d 3 (3*rho a d/4-1)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 3)+
              ((stock a b c d 3 (3*rho a d/4-1)++complement a b c d 2 1++stock a b c d 1 1).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 2)+
              ((complement a b c d 1 (1 ||| rho a d/2)).map (oldValue a b c d)).sum+
              oldValue a b c d (terminal a b c d 1) := by
          simp only [List.map_append,List.sum_append]
          linear_combination -z+s0+mW'+mnu+r0
        rw [←he]
        convert (hw.2.2.2.2.2 hbdC hca).2.2.2.2.1 using 1 <;> ring
      · exact hz


private def markedBanks (a b c d : ℕ) (br : Branch) : List (List ℕ × ℕ) :=
  match genericBanks a b c d br with
  | [(P0,n0),(P1,n1),(P2,n2),(P3,n3)] =>
      if br=.c then
        [(insertAt (size a b c d) P0 1,n0),(P1,n1),(P2,n2),(P3,n3)]
      else [(P0,n0),(P1,n1),(size a b c d::P2,n2),(P3,n3)]
  | bs => bs

private theorem insert_after_two (k : ℕ) (P0 P1 P2 P3 : List ℕ)
    (n0 n1 n2 n3 : ℕ) :
    insertAt k (blocksWord [(P0,n0),(P1,n1),(P2,n2),(P3,n3)])
      (P0.length+1+P1.length+1)=
    blocksWord [(P0,n0),(P1,n1),(k::P2,n2),(P3,n3)] := by
  let pre := P0++[n0]++P1++[n1]
  let post := blocksWord [(P2,n2),(P3,n3)]
  have he : blocksWord [(P0,n0),(P1,n1),(P2,n2),(P3,n3)]=pre++post := by
    simp [pre,post,blocksWord,List.append_assoc]
  have hl : pre.length=P0.length+1+P1.length+1 := by simp only [pre,List.length_append,List.length_singleton]
  rw [he,←hl,insertAt,List.take_left,List.drop_left]
  simp [pre,post,blocksWord,List.append_assoc]

private theorem literal_cut (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hf : ¬isFinite a b c d) :
    insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)=
      blocksWord (markedBanks a b c d (branch a b c d)) := by
  have hn1 : (a,b,c,d)≠(4,2,5,2) := fun he => hf (Or.inl he)
  have hn2 : (a,b,c,d)≠(4,2,6,2) := fun he => hf (Or.inr (Or.inl he))
  have hn3 : (a,b,c,d)≠(5,2,6,2) := fun he => hf (Or.inr (Or.inr he))
  have hword : bankWord a b c d=blocksWord (genericBanks a b c d (branch a b c d)) := by
    exact (blocksWord_flatMap _).symm
  have zero (len off : ℕ) : (MaxPlusTwo.Chambers.chamberLabels len off 0).length=0 := by
    simpa using low_length len off 0 (Nat.zero_le _)
  have p0 : (complement a b c d 1 (h b c-1)).length=b := by
    have hh := (band_length (c-1) d (c-b-1) (c-b-1) 0 0 (by omega) (by omega)
      (by positivity) (zero _ _)).2
    simpa [complement,stock,full,chainLength,chainStart,h,show c-1-(c-b-1)=b by omega] using hh
  have w : (stock a b c d 2 (full a b c d 2)).length=b-1 := by
    simp [stock,full,chainLength,MaxPlusTwo.Chambers.chamberLabels_full]
  rw [hword]
  by_cases hbd : b≤d
  · have v : (stock a b c d 1 (h b c-H a c)).length=a-b := by
      have hh := (band_length (c-1) d (c-b-1) (c-a-1) 0 0 (by omega) (by omega)
        (by positivity) (zero _ _)).1
      simpa [stock,chainLength,chainStart,h,H,show c-b-1-(c-a-1)=a-b by omega] using hh
    have hcut : freshCut a b c d=(complement a b c d 1 (h b c-1)).length+1+
        (stock a b c d 2 (full a b c d 2)++stock a b c d 1 (h b c-H a c)).length+1 := by
      simp only [freshCut,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,List.length_append,p0,w,v]
      omega
    rw [hcut]
    by_cases ha1 : a=d+1
    · have hbr : branch a b c d=.a1 := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_pos ha1]
      rw [hbr]
      simpa [markedBanks,genericBanks] using insert_after_two (size a b c d)
        (complement a b c d 1 (h b c-1))
        (stock a b c d 2 (full a b c d 2)++stock a b c d 1 (h b c-H a c))
        (complement a b c d 3 1)
        (stock a b c d 0 (full a b c d 0)++stock a b c d 1 (H a c-1)++stock a b c d 3 1)
        (terminal a b c d 1) (terminal a b c d 2) (terminal a b c d 3) (terminal a b c d 0)
    · have hbr : branch a b c d=.a2 := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_neg ha1]
      rw [hbr]
      simpa [markedBanks,genericBanks] using insert_after_two (size a b c d)
        (complement a b c d 1 (h b c-1))
        (stock a b c d 2 (full a b c d 2)++stock a b c d 1 (h b c-H a c))
        (complement a b c d 3 (fmask a d)++stock a b c d 1 (H a c-1))
        (stock a b c d 0 (full a b c d 0)++stock a b c d 3 (fmask a d))
        (terminal a b c d 1) (terminal a b c d 2) (terminal a b c d 3) (terminal a b c d 0)
  · let J := min (a-b-1) (d-2)
    have hj : jmask a b d=2^J := by
      dsimp [jmask,J]
      by_cases hle : a-b-1≤d-2
      · rw [Nat.min_eq_left hle,Nat.min_eq_left (Nat.pow_le_pow_right Nat.zero_lt_two hle)]
      · have hle' : d-2≤a-b-1 := by omega
        rw [Nat.min_eq_right hle',Nat.min_eq_right (Nat.pow_le_pow_right Nat.zero_lt_two hle')]
    have hr : Rmask a b c d=2^(c-a+J) := by dsimp [Rmask,q]; rw [hj,←pow_add]
    have hJ : J≤a-b-1 := Nat.min_le_left _ _
    have hu : c-a+J≤c-b-1 := by omega
    have xm : (stock a b c d 3 (mmask a b d)).length=J := by
      simpa [stock,chainLength,chainStart,mmask,hj] using
        low_length (a-1) (d+c+b) J (by omega)
    by_cases hb0 : d+2≤b
    · have v : (stock a b c d 1 (h b c-Rmask a b c d)).length=a-b-1-J := by
        have hh := (band_length (c-1) d (c-b-1) (c-a+J) 0 0 (by omega) hu
          (by positivity) (zero _ _)).1
        simpa [stock,chainLength,chainStart,h,hr,show c-b-1-(c-a+J)=a-b-1-J by omega] using hh
      have hbr : branch a b c d=.b0 := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_pos hb0]
      have hcut : freshCut a b c d=(complement a b c d 1 (h b c-1)).length+1+
          (stock a b c d 2 (full a b c d 2)++stock a b c d 3 (mmask a b d)++
            stock a b c d 1 (h b c-Rmask a b c d)).length+1 := by
        simp only [freshCut,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_pos hb0,
          List.length_append,p0,w,xm,v]
        omega
      rw [hbr,hcut]
      exact insert_after_two _ _ _ _ _ _ _ _ _
    · by_cases hc2 : a+2≤c
      · have hδ : ∃ D, deltaMask a b c d=2^D ∧ D<c-a+J := by
          by_cases hsmall : Rmask a b c d<2^a*2^b
          · exact ⟨0,by simp [deltaMask,hsmall],by omega⟩
          · have hle : a+b≤c-a+J := by
              apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
              simpa only [←pow_add,hr] using (Nat.le_of_not_gt hsmall)
            let D := c-a+J-(a+b)
            have hm : (2^a*2^b)*2^D=Rmask a b c d := by
              rw [hr,←pow_add,←pow_add,show a+b+D=c-a+J by dsimp [D]; omega]
            refine ⟨D,?_,by dsimp [D]; omega⟩
            rw [deltaMask,if_neg hsmall,←hm,Nat.mul_div_cancel_left _ (by positivity)]
        obtain ⟨D,hδ,hD⟩ := hδ
        have v : (stock a b c d 1 (h b c-Rmask a b c d+deltaMask a b c d)).length=a-b-J := by
          have hh := (band_length (c-1) d (c-b-1) (c-a+J) (deltaMask a b c d) 1
            (by omega) hu (by rw [hδ]; exact pow_lt_pow_right₀ (by decide) hD)
            (by rw [hδ]; exact power_length _ _ _ (by omega))).1
          simpa [stock,chainLength,chainStart,h,hr,show c-b-1-(c-a+J)+1=a-b-J by omega] using hh
        have hcut : freshCut a b c d=(complement a b c d 1 (h b c-1)).length+1+
            (stock a b c d 2 (full a b c d 2)++stock a b c d 3 (mmask a b d)++
              stock a b c d 1 (h b c-Rmask a b c d+deltaMask a b c d)).length+1 := by
          simp only [freshCut,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_neg hb0,if_pos hc2,
            List.length_append,p0,w,xm,v]
          omega
        have hbranches : branch a b c d=.b1one ∨ branch a b c d=.b1quot := by
          simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_neg hb0,if_pos hc2]
          split_ifs <;> simp
        rw [hcut]
        rcases hbranches with hbr|hbr
        all_goals
          rw [hbr]
          exact insert_after_two _ _ _ _ _ _ _ _ _
      · have hbr : branch a b c d=.c := by
          simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_neg hb0,if_neg hc2]
        have hcut : freshCut a b c d=1 := by
          simp only [freshCut,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_neg hb0,if_neg hc2]
        have hM : 3*rho a d/4=fmask a d := by
          have hrho : rho a d=4*2^(a-d-2) := by
            conv_lhs =>
              dsimp [rho]
              rw [show a-d=(a-d-2)+2 by omega,pow_add]
            ring
          rw [hrho]; dsimp [fmask]; omega
        have hsmall : 3*rho a d/4-1<2^(a-2) := by
          have hp : 0<(2:ℕ)^(a-d-2) := by positivity
          have hle : 4*(2:ℕ)^(a-d-2)≤2^(a-2) := by
            calc
              _ = 2^(a-d-2+2) := by rw [pow_add]; ring
              _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
          rw [hM]; dsimp [fmask]; omega
        have hmem : chainStart b c d 3+(a-2)∈complement a b c d 3 (3*rho a d/4-1) := by
          apply MaxPlusTwo.Chambers.chamberLabels_mem _ _ _ _ |>.mpr
          refine ⟨a-2,by dsimp [chainLength]; omega,?_,rfl⟩
          have hfalse := Nat.testBit_lt_two_pow hsmall
          dsimp [full,chainLength]
          simp only [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hfalse]
          simp [show a-2<a-1 by omega]
        have hlen : 1≤(complement a b c d 3 (3*rho a d/4-1)).length := by
          exact List.length_pos_of_mem hmem
        rw [hbr,hcut]
        dsimp only [genericBanks,markedBanks]
        simp only [reduceIte,blocksWord]
        rw [insertAt,List.take_append_of_le_length hlen,List.drop_append_of_le_length hlen]
        simp [insertAt,List.append_assoc]

private theorem new_strip (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)) := by
  by_cases hf : isFinite a b c d
  · exact (finite_strips a b c d hf).2
  have hn1 : (a,b,c,d)≠(4,2,5,2) := fun he => hf (Or.inl he)
  have hn2 : (a,b,c,d)≠(4,2,6,2) := fun he => hf (Or.inr (Or.inl he))
  have hn3 : (a,b,c,d)≠(5,2,6,2) := fun he => hf (Or.inr (Or.inr he))
  have hv := chain_values a b c d (by omega) hb (by omega) hd
  have hz := (word_totals a b c d hb hba hac hd hda).2
  rw [literal_cut a b c d hb hba hac hd hda hf] at hz ⊢
  have hw := all_windows a b c d hb hba hac hd hda
  have hN : 0≤sourceMod a b c d := by have := hv.1 0; omega
  have hs (r : Fin 4) (m i : ℕ) (hi : i∈stock a b c d r m) :
      0≤newValue a b c d i := by
    obtain ⟨hi',hni⟩ := stock_good a b c d hb hba hac hd hda r m i hi
    have hsign := source_signs a b c d (by omega) hb (by omega) hd i hi'
    rw [if_neg hni] at hsign
    exact hsign.2.le
  have hsc (r : Fin 4) (m i : ℕ) (hi : i∈complement a b c d r m) :
      0≤newValue a b c d i := hs r _ i hi
  have ht (r : Fin 4) : newValue a b c d (terminal a b c d r)≤0 := by
    obtain ⟨hi,hn⟩ := terminal_good a b c d hb hba hac hd hda r
    have hsign := source_signs a b c d (by omega) hb (by omega) hd _ hi
    rw [if_pos hn] at hsign
    exact hsign.2.le
  have hval (r : Fin 4) (e : ℕ) (he : e<chainLength a b c d r-1) :
      newValue a b c d (chainStart b c d r+e)=2^e*newBase a b c d r := by
    rw [hv.2.2.1 r e (by omega),if_pos (by omega)]
  have sm (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :=
    stock_mass a b c d r m hm (newValue a b c d) (newBase a b c d) hval
  have cm (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :=
    complement_mass a b c d r m hm (newValue a b c d) (newBase a b c d) hval
  have ti (r : Fin 4) : chainStart b c d r+(chainLength a b c d r-1)=
      terminal a b c d r := by fin_cases r <;> simp [chainStart,chainLength,terminal] <;> omega
  have nm (r : Fin 4) := native_masses a b c d (by omega) hb (by omega) hd r
  dsimp only at nm
  simp only [ti] at nm
  have row (r : Fin 4) :
      (full a b c d r : ℤ)*newBase a b c d r+newValue a b c d (terminal a b c d r)=
        nextNewBase a b c d r-newBase a b c d r := (nm r).2.1
  have term (r : Fin 4) : 2*newValue a b c d (terminal a b c d r)=
      nextNewBase a b c d r-(2*sourceMod a b c d+1) := (nm r).2.2.2
  have bi := new_bases_identify a b c d
  have newpos := new_base_bounds a b c d (by omega) hb (by omega) hd
  have hA : 0≤AA a b c := by
    have hp := (hv.1 0).1
    rw [(bases_identify a b c d).1] at hp
    omega
  have hear : newValue a b c d (size a b c d)=AA a b c :=
    hv.2.2.2.trans (bases_identify a b c d).1
  have r0 := row 0
  have r1 := row 1
  have r2 := row 2
  have r3 := row 3
  have t0 := term 0
  have t1 := term 1
  have t2 := term 2
  have t3 := term 3
  simp only [nextNewBase] at r0 r1 r2 r3 t0 t1 t2 t3
  simp only [bi.1,bi.2.1,bi.2.2.1,bi.2.2.2,(bases_identify a b c d).1] at r0 r1 r2 r3 t0 t1 t2 t3
  change _=SU a b d-2*AA a b c at r0
  change _=SV a c d-SU a b d at r1
  change _=SW b c d-SV a c d at r2
  change _=AA a b c-SW b c d at r3
  change _=SU a b d-(2*sourceMod a b c d+1) at t0
  change _=SV a c d-(2*sourceMod a b c d+1) at t1
  change _=SW b c d-(2*sourceMod a b c d+1) at t2
  change _=AA a b c-(2*sourceMod a b c d+1) at t3
  have fp (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have s0 := sm 0 _ (fp 0)
  have s2 := sm 2 _ (fp 2)
  simp only [bi.1,bi.2.2.1] at s0 s2
  have powle {u v : ℕ} (h : u≤v) : 2^u≤(2:ℕ)^v := Nat.pow_le_pow_right Nat.zero_lt_two h
  have powlt {u v : ℕ} (h : u<v) : 2^u<(2:ℕ)^v := pow_lt_pow_right₀ (by decide) h
  have hh : 0<h b c := by dsimp [h]; positivity
  have hH : 0<H a c := by dsimp [H]; positivity
  have hHh : H a c≤h b c := by exact powle (by omega)
  have hhcap : h b c<2^(c-1) := by exact powlt (by omega)
  have hfpos : 0<fmask a d := by dsimp [fmask]; positivity
  have hfcap : fmask a d<2^(a-1) := by
    have pp : 0<(2:ℕ)^(a-d-2) := by positivity
    have pe : 4*(2:ℕ)^(a-d-2)≤2^(a-1) := by
      calc
        _ = 2^(a-d-2+2) := by rw [pow_add]; ring
        _ ≤ _ := powle (by omega)
    dsimp [fmask]; omega
  have m0 := cm 1 (h b c-1) (by simpa [chainLength] using (show h b c-1<2^(c-1) by omega))
  simp only [bi.2.1] at m0
  by_cases hbd : b≤d
  · have m1 := sm 1 (h b c-H a c) (by simpa [chainLength] using (show h b c-H a c<2^(c-1) by omega))
    have mH := sm 1 (H a c-1) (by simpa [chainLength] using (show H a c-1<2^(c-1) by omega))
    simp only [bi.2.1] at m1 mH
    have castH : ((h b c-H a c : ℕ):ℤ)=(h b c:ℤ)-(H a c:ℤ) := by omega
    have casth : ((h b c-1 : ℕ):ℤ)=(h b c:ℤ)-1 := by omega
    have castH1 : ((H a c-1 : ℕ):ℤ)=(H a c:ℤ)-1 := by omega
    rw [castH] at m1
    rw [casth] at m0
    rw [castH1] at mH
    by_cases ha1 : a=d+1
    · have hbr : branch a b c d=.a1 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_pos ha1]
      have mX := sm 3 1 (by change 1<(2:ℕ)^(a-1); simpa using powlt (show 0<a-1 by omega))
      simp only [bi.2.2.2,Nat.cast_one] at mX
      have z := hz
      simp only [hbr] at z
      dsimp only [markedBanks,genericBanks] at z
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,hear] at z
      rw [hbr]
      dsimp only [markedBanks,genericBanks]
      apply four_packet_strip _ _ (2*sourceMod a b c d+1) _ _ _ _ _ _ _ _ (SV a c d) (SW b c d) (AA a b c) (SU a b d)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_cons.mp hi with rfl|hi
          · exact hear.symm ▸ hA
          · exact hsc 3 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 0 _ _ hi
            · exact hs 1 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (newpos 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.2 using 1 <;> linear_combination m0+r1
      · convert (hw.2.1 hbd).2 using 1 <;> simp only [List.map_append,List.sum_append] <;> linear_combination m0+r1+m1+s2+r2
      · convert (hw.2.2.1 hbd ha1).2 using 1 <;>
          simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,hear] <;>
          linear_combination z-s0-mH-mX-r0
      · simpa [hbr,markedBanks,genericBanks] using hz
    · have hbr : branch a b c d=.a2 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_neg ha1]
      have mX := sm 3 (fmask a d) (by simpa [chainLength] using hfcap)
      simp only [bi.2.2.2] at mX
      have z := hz
      simp only [hbr] at z
      dsimp only [markedBanks,genericBanks] at z
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,hear] at z
      rw [hbr]
      dsimp only [markedBanks,genericBanks]
      apply four_packet_strip _ _ (2*sourceMod a b c d+1) _ _ _ _ _ _ _ _ (SV a c d) (SW b c d) (AA a b c) (SU a b d)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_cons.mp hi with rfl|hi
          · exact hear.symm ▸ hA
          · rcases List.mem_append.mp hi with hi|hi
            · exact hsc 3 _ _ hi
            · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 0 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (newpos 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.2 using 1 <;> linear_combination m0+r1
      · convert (hw.2.1 hbd).2 using 1 <;> simp only [List.map_append,List.sum_append] <;> linear_combination m0+r1+m1+s2+r2
      · convert (hw.2.2.2.1 (by omega) (Or.inl ⟨hbd,hf⟩)).2 using 1 <;>
          simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,hear] <;>
          linear_combination z-s0-mX-r0
      · simpa [hbr,markedBanks,genericBanks] using hz
  · by_cases hB : d+2≤b ∨ a+2≤c
    · have hB' : d+2≤b ∨ b=d+1 ∧ a+2≤c := by omega
      let δ := if d+2≤b then 0 else deltaMask a b c d
      let v3 := if d+2≤b then Rmask a b c d-1 else
        (Rmask a b c d-1) ^^^ deltaMask a b c d
      let J := min (a-b-1) (d-2)
      have hJ : jmask a b d=2^J := by
        dsimp [jmask,J]
        by_cases hle : a-b-1≤d-2
        · rw [Nat.min_eq_left hle,Nat.min_eq_left (powle hle)]
        · have hle' : d-2≤a-b-1 := by omega
          rw [Nat.min_eq_right hle',Nat.min_eq_right (powle hle')]
      have hR : Rmask a b c d=2^(c-a+J) := by
        dsimp [Rmask,q]; rw [hJ,←pow_add]
      have hRh : Rmask a b c d≤h b c := by
        rw [hR]; exact powle (by have := Nat.min_le_left (a-b-1) (d-2); dsimp [J] at *; omega)
      have hRpos : 0<Rmask a b c d := by rw [hR]; positivity
      have hδ : δ≤Rmask a b c d := by
        dsimp [δ,deltaMask]
        split_ifs
        · omega
        · omega
        · exact Nat.div_le_self _ _
      have hjpos : 0<jmask a b d := by rw [hJ]; positivity
      have hjcap : jmask a b d≤2^(a-1) := by
        rw [hJ]; exact powle (by have := Nat.min_le_left (a-b-1) (d-2); dsimp [J] at *; omega)
      have mV := sm 1 (h b c-Rmask a b c d+δ) (by change _<2^(c-1); omega)
      have mM := sm 3 (mmask a b d) (by change _<2^(a-1); dsimp [mmask]; omega)
      have mX := sm 3 (fmask a d) (by simpa [chainLength] using hfcap)
      simp only [bi.2.1] at mV
      simp only [bi.2.2.2] at mM mX
      have casth : ((h b c-1:ℕ):ℤ)=(h b c:ℤ)-1 := by omega
      have castV : ((h b c-Rmask a b c d+δ:ℕ):ℤ)=
          (h b c:ℤ)-(Rmask a b c d:ℤ)+(δ:ℤ) := by omega
      have castM : (mmask a b d:ℤ)=(jmask a b d:ℤ)-1 := by dsimp [mmask]; omega
      have castR : (Rmask a b c d:ℤ)=(q a c:ℤ)*(jmask a b d:ℤ) := by simp [Rmask]
      rw [casth] at m0
      rw [castV,castR] at mV
      rw [castM] at mM
      have heword : blocksWord (markedBanks a b c d (branch a b c d))=blocksWord
          [(complement a b c d 1 (h b c-1),terminal a b c d 1),
           (stock a b c d 2 (full a b c d 2)++stock a b c d 3 (mmask a b d)++
             stock a b c d 1 (h b c-Rmask a b c d+δ),terminal a b c d 2),
           (size a b c d::(complement a b c d 3 (mmask a b d ||| fmask a d)++stock a b c d 1 v3),
             terminal a b c d 3),
           (stock a b c d 0 (full a b c d 0)++stock a b c d 3 (fmask a d),terminal a b c d 0)] := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd]
        by_cases hb0 : d+2≤b
        · simp [hb0,markedBanks,genericBanks,blocksWord,δ,v3,List.append_assoc]
        · have hc2 : a+2≤c := by omega
          simp only [if_neg hb0,if_pos hc2]
          split_ifs <;> simp [markedBanks,genericBanks,blocksWord,δ,v3,hb0,List.append_assoc]
      rw [heword] at hz ⊢
      have z := hz
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,hear] at z
      apply four_packet_strip _ _ (2*sourceMod a b c d+1) _ _ _ _ _ _ _ _
        (SV a c d) (SW b c d) (AA a b c) (SU a b d)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 2 _ _ hi
            · exact hs 3 _ _ hi
          · exact hs 1 _ _ hi
        · rcases List.mem_cons.mp hi with rfl|hi
          · exact hear.symm ▸ hA
          · rcases List.mem_append.mp hi with hi|hi
            · exact hsc 3 _ _ hi
            · exact hs 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact hs 0 _ _ hi
          · exact hs 3 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 1
        · exact ht 2
        · exact ht 3
        · exact ht 0
      · exact t1
      · exact t2
      · exact t3
      · exact t0
      · have := (newpos 1).1; rw [bi.2.1] at this; omega
      · convert hw.1.2 using 1 <;> linear_combination m0+r1
      · have ww : window ((jmask a b d:ℤ)*(SW b c d-(q a c:ℤ)*SU a b d)+(δ:ℤ)*SU a b d) (SW b c d) := by
          by_cases hb0 : d+2≤b <;> simpa [δ,hb0] using (hw.2.2.2.2.1 hB').2
        convert ww using 1 <;> simp only [List.map_append,List.sum_append] <;>
          linear_combination m0+r1+s2+mM+mV+r2
      · convert (hw.2.2.2.1 (by omega) (Or.inr hB')).2 using 1 <;>
          simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,hear] <;>
          linear_combination z-s0-mX-r0
      · exact hz
    · have hbdC : b=d+1 := by omega
      have hca : c=a+1 := by omega
      have hbr : branch a b c d=.c := by
        simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,
          if_neg (show ¬d+2≤b by omega),if_neg (show ¬a+2≤c by omega)]
      have hrho : rho a d=4*2^(a-d-2) := by
        conv_lhs =>
          dsimp [rho]
          rw [show a-d=(a-d-2)+2 by omega,pow_add]
        ring
      have hM : 3*rho a d/4=fmask a d := by rw [hrho]; dsimp [fmask]; omega
      have hnu : rho a d/2=2^(a-d-1) := by
        conv_lhs =>
          dsimp [rho]
          rw [show a-d=(a-d-1)+1 by omega,pow_succ]
        omega
      have hnucap : rho a d/2<2^(c-1) := by rw [hnu]; exact powlt (by omega)
      have oneV : 1<2^(c-1) := by simpa using powlt (show 0<c-1 by omega)
      have oneW : 1<2^(b-1) := by simpa using powlt (show 0<b-1 by omega)
      have mC := cm 3 (3*rho a d/4-1) (by change _<2^(a-1); rw [hM]; omega)
      have mC' := sm 3 (3*rho a d/4-1) (by change _<2^(a-1); rw [hM]; omega)
      have mW := cm 2 1 (by simpa [chainLength] using oneW)
      have mW' := sm 2 1 (by simpa [chainLength] using oneW)
      have mV := sm 1 1 (by simpa [chainLength] using oneV)
      have mnu := sm 1 (rho a d/2) (by simpa [chainLength] using hnucap)
      simp only [bi.2.2.2] at mC mC'
      simp only [bi.2.2.1,Nat.cast_one,one_mul] at mW mW'
      simp only [bi.2.1,Nat.cast_one,one_mul] at mV mnu
      have castM : ((3*rho a d/4-1:ℕ):ℤ)=(fmask a d:ℤ)-1 := by rw [hM]; omega
      rw [castM] at mC mC'
      have marked := insert_positive (newValue a b c d) (size a b c d) 1
        (complement a b c d 3 (3*rho a d/4-1)) (by rw [hear]; exact hA)
        (hsc 3 _)
      simp only [hear] at marked
      simp only [hbr,markedBanks,genericBanks,reduceIte] at hz ⊢
      have z := hz
      simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,marked.2,hear] at z
      apply four_packet_strip _ _ (2*sourceMod a b c d+1) _ _ _ _ _ _ _ _
        (AA a b c) (SW b c d) (SV a c d) (SU a b d)
      · omega
      · omega
      · intro p hp i hi
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact marked.1 i hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 3 _ _ hi
            · exact hsc 2 _ _ hi
          · exact hs 1 _ _ hi
        · exact hsc 1 _ _ hi
        · rcases List.mem_append.mp hi with hi|hi
          · rcases List.mem_append.mp hi with hi|hi
            · exact hs 0 _ _ hi
            · exact hs 2 _ _ hi
          · exact hs 1 _ _ hi
      · intro p hp
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl
        · exact ht 3
        · exact ht 2
        · exact ht 1
        · exact ht 0
      · exact t3
      · exact t2
      · exact t1
      · exact t0
      · have := (newpos 1).1; rw [bi.2.1] at this; omega
      · convert (hw.2.2.2.2.2 hbdC hca).2.1 using 1 <;> simp only [marked.2] <;> linear_combination mC+r3
      · convert (hw.2.2.2.2.2 hbdC hca).2.2.2.1 using 1 <;>
          simp only [List.map_append,List.sum_append,marked.2] <;> linear_combination mC+r3+mC'+mW+mV+r2
      · convert (hw.2.2.2.2.2 hbdC hca).2.2.2.2.2 using 1 <;>
          simp only [List.map_append,List.sum_append,marked.2] <;>
          linear_combination z-s0-mW'-mnu-r0
      · exact hz



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
    funext i
    simp only [hmod,hseed,oldValue]
  have hnewval : (fun i => centered (modulus (size a b c d+1))
      ((2:ℤ)^i*((2*(1+2^a+2^(a+b)+2^(a+b+c)) : ℕ) : ℤ)))=newValue a b c d := by
    funext i
    simp only [Nat.cast_mul,Nat.cast_ofNat,hmodnew,hseed,newValue]
  have ho : OriginalOrder (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c))
      ((bankWord a b c d).map (label (size a b c d) hk)) := by
    apply lift_order (size a b c d)
      (1+2^a+2^(a+b)+2^(a+b+c)) hk (bankWord a b c d) hp
    · rw [holdval,hmod]
      exact old_strip a b c d hb hba hac hd hda
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
      rw [hnewval,half]
      simpa only [he] using new_strip a b c d hb hba hac hd hda
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [size]; omega)
  refine ⟨(bankWord a b c d).map (label (size a b c d) hk),
    freshCut a b c d,rfl,(cut_bounds a b c d hb hba hac hd hda).2,ho,?_⟩
  rw [←List.take_append_drop (freshCut a b c d) (bankWord a b c d)]
  rw [marked_word (size a b c d) (freshCut a b c d) hk pre post hpre (by simpa [pre,post] using hp)]
  exact hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
