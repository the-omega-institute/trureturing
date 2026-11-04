/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks
   generality: I
   mirror-B: none(waiver:physical-dependent-source-family)
   mirror-E: none(waiver:physical-dependent-source-family)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Native mask partitions and the five literal bank inventories. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private full stock complement terminal q h H fmask jmask mmask Rmask deltaMask rho branch      
      isFinite branch_complete from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private oldValue newValue source_totals size negatives chainLength chainStart from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

open private freshCut from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private insertAt from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def finiteBanks (a b c d : ℕ) : List (List ℕ × ℕ) :=
  if (a,b,c,d)=(4,2,5,2) then
    [([0,2,3],6),([4,5],1),([9,11],12),([7,10],8)]
  else if (a,b,c,d)=(4,2,6,2) then
    [([0,2,3,4],7),([5,8],13),([10,12],9),([6,11],1)]
  else
    [([0,2,3,4],7),([5,6],1),([8,10,11],14),([12,13],9)]

private def genericBanks (a b c d : ℕ) (br : Branch) : List (List ℕ × ℕ) :=
  let U := stock a b c d 0 (full a b c d 0)
  let V (m : ℕ) := stock a b c d 1 m
  let W := stock a b c d 2 (full a b c d 2)
  let X (m : ℕ) := stock a b c d 3 m
  let Vc (m : ℕ) := complement a b c d 1 m
  let Xc (m : ℕ) := complement a b c d 3 m
  let n0 := terminal a b c d 0
  let n1 := terminal a b c d 1
  let n2 := terminal a b c d 2
  let n3 := terminal a b c d 3
  match br with
  | .a1 =>
      [(Vc (h b c-1),n1),(W++V (h b c-H a c),n2),
       (Xc 1,n3),(U++V (H a c-1)++X 1,n0)]
  | .a2 =>
      [(Vc (h b c-1),n1),(W++V (h b c-H a c),n2),
       (Xc (fmask a d)++V (H a c-1),n3),(U++X (fmask a d),n0)]
  | .b0 =>
      [(Vc (h b c-1),n1),(W++X (mmask a b d)++V (h b c-Rmask a b c d),n2),
       (Xc (mmask a b d ||| fmask a d)++V (Rmask a b c d-1),n3),
       (U++X (fmask a d),n0)]
  | .b1one | .b1quot =>
      [(Vc (h b c-1),n1),
       (W++X (mmask a b d)++V (h b c-Rmask a b c d+deltaMask a b c d),n2),
       (Xc (mmask a b d ||| fmask a d)++
          V ((Rmask a b c d-1) ^^^ deltaMask a b c d),n3),
       (U++X (fmask a d),n0)]
  | .c =>
      let M := 3*rho a d/4
      let nu := rho a d/2
      [(Xc (M-1),n3),(X (M-1)++complement a b c d 2 1++V 1,n2),
       (complement a b c d 1 (1 ||| nu),n1),
       (U++stock a b c d 2 1++V nu,n0)]
  | .finite1 | .finite2 | .finite3 => finiteBanks a b c d

private def bankWord (a b c d : ℕ) : List ℕ :=
  (genericBanks a b c d (branch a b c d)).flatMap (fun p => p.1 ++ [p.2])

private theorem chamber_split (len off mask : ℕ) (hm : mask < 2^len) :
    (chamberLabels len off (2^len-1 ^^^ mask) ++ chamberLabels len off mask).Perm
      (List.range' off len) := by
  simpa only [chamberLabels_full] using
    (chamberLabels_split len off (2^len-1) mask
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he]))

private theorem bit_band (u v e : ℕ) (hvu : v≤u) :
    (2^u-2^v).testBit e = (decide (e<u) && !decide (e<v)) := by
  have hv : 0<2^v := Nat.two_pow_pos v
  have huv : 2^v≤2^u := Nat.pow_le_pow_right Nat.zero_lt_two hvu
  have he : 2^u-2^v=2^u-((2^v-1)+1) := by omega
  rw [he,Nat.testBit_two_pow_sub_succ (by omega),Nat.testBit_two_pow_sub_one]

private theorem band_toggle (u v δ : ℕ) (hvu : v≤u) (hδ : δ<2^v) :
    (2^u-1) ^^^ ((2^v-1) ^^^ δ) = 2^u-2^v+δ := by
  have factor : 2^u-2^v=2^v*(2^(u-v)-1) := by
    rw [Nat.mul_sub,Nat.mul_one,←pow_add]
    rw [show v+(u-v)=u by omega]
  have hor : 2^u-2^v+δ=(2^u-2^v) ||| δ := by
    rw [factor]
    exact Nat.two_pow_add_eq_or_of_lt hδ _
  rw [hor]
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_xor,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one,Nat.testBit_or,bit_band u v e hvu]
  by_cases hev : e<v
  · have heu : e<u := by omega
    simp [hev,heu]
  · have hbit : δ.testBit e=false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hδ (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    simp [hev,hbit]

private theorem labels_band_split (len off u v δ : ℕ)
    (hvu : v≤u) (hδ : δ<2^v) :
    (chamberLabels len off ((2^len-1) ^^^ (2^u-1)) ++
      chamberLabels len off (2^u-2^v+δ) ++
      chamberLabels len off ((2^v-1) ^^^ δ)).Perm
        (chamberLabels len off (2^len-1)) := by
  have hsub : ∀ e<len, ((2^v-1) ^^^ δ).testBit e=true →
      (2^u-1).testBit e=true := by
    intro e he hb
    by_cases heu : e<u
    · simp [Nat.testBit_two_pow_sub_one,heu]
    · have hev : ¬e<v := by omega
      have hbit : δ.testBit e=false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hδ (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      simp [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hev,hbit] at hb
  have hi := chamberLabels_split len off (2^u-1) ((2^v-1) ^^^ δ) hsub
  rw [band_toggle u v δ hvu hδ] at hi
  have ho := chamberLabels_split len off (2^len-1) (2^u-1)
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
  simpa only [List.append_assoc] using
    (hi.append_left (chamberLabels len off ((2^len-1) ^^^ (2^u-1)))).trans ho

private theorem labels_union (len off m n : ℕ)
    (hd : ∀ e<len, m.testBit e=true → n.testBit e=false) :
    (chamberLabels len off m ++ chamberLabels len off n).Perm
      (chamberLabels len off (m ||| n)) := by
  have hnd : (chamberLabels len off m ++ chamberLabels len off n).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨chamberLabels_nodup _ _ _,chamberLabels_nodup _ _ _,?_⟩
    intro i hi j hj hij
    obtain ⟨e,he,hm,hie⟩ := (chamberLabels_mem _ _ _ _).mp hi
    obtain ⟨f,hf,hn,hjf⟩ := (chamberLabels_mem _ _ _ _).mp hj
    have hef : e=f := by omega
    subst f
    rw [hd e he hm] at hn
    contradiction
  apply (List.perm_ext_iff_of_nodup hnd (chamberLabels_nodup _ _ _)).mpr
  intro i
  simp only [List.mem_append,chamberLabels_mem,Nat.testBit_or,Bool.or_eq_true]
  constructor
  · rintro (⟨e,he,hm,hi⟩|⟨e,he,hn,hi⟩)
    · exact ⟨e,he,Or.inl hm,hi⟩
    · exact ⟨e,he,Or.inr hn,hi⟩
  · rintro ⟨e,he,hm|hn,hi⟩
    · exact Or.inl ⟨e,he,hm,hi⟩
    · exact Or.inr ⟨e,he,hn,hi⟩

private theorem labels_three_split (len off m n : ℕ)
    (hd : ∀ e<len, m.testBit e=true → n.testBit e=false) :
    (chamberLabels len off ((2^len-1) ^^^ (m ||| n)) ++
      chamberLabels len off m ++ chamberLabels len off n).Perm
        (chamberLabels len off (2^len-1)) := by
  have hu := labels_union len off m n hd
  have hs := chamberLabels_split len off (2^len-1) (m ||| n)
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
  simpa only [List.append_assoc] using
    (hu.append_left (chamberLabels len off ((2^len-1) ^^^ (m ||| n)))).trans hs

private theorem stock_good (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (r : Fin 4) (mask i : ℕ) (hi : i ∈ stock a b c d r mask) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  obtain ⟨e,he,_,hval⟩ := (chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;>
    dsimp [chainLength,chainStart] at he hval <;>
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false] <;> omega

private theorem terminal_good (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (r : Fin 4) :
    terminal a b c d r < size a b c d ∧
      terminal a b c d r ∈ negatives a b c d := by
  fin_cases r <;> simp [terminal,negatives,size] <;> omega

private theorem stock_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((stock a b c d r mask).map f).sum=(mask : ℤ)*F r := by
  exact chamberLabels_sum _ _ _ hm f (F r) (hf r)

private theorem complement_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((complement a b c d r mask).map f).sum=
      ((full a b c d r : ℤ)-(mask : ℤ))*F r := by
  have hs := chamberLabels_split (chainLength a b c d r-1) (chainStart b c d r)
    (full a b c d r) mask
    (by intro e he _; simp [full,Nat.testBit_two_pow_sub_one,he])
  have hsum := (hs.map f).sum_eq
  have hfull := stock_mass a b c d r (full a b c d r)
    (by dsimp [full]; exact Nat.sub_lt (by positivity) (by decide)) f F hf
  have hmask := stock_mass a b c d r mask hm f F hf
  change (((complement a b c d r mask)++stock a b c d r mask).map f).sum=
    ((stock a b c d r (full a b c d r)).map f).sum at hsum
  rw [List.map_append,List.sum_append,hfull,hmask] at hsum
  linear_combination hsum

private theorem full_inventory (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    (stock a b c d 0 (full a b c d 0) ++ [terminal a b c d 0] ++
      stock a b c d 1 (full a b c d 1) ++ [terminal a b c d 1] ++
      stock a b c d 2 (full a b c d 2) ++ [terminal a b c d 2] ++
      stock a b c d 3 (full a b c d 3) ++ [terminal a b c d 3]).Perm
        (List.range (size a b c d)) := by
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,
      show len-1+1=len by omega] using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0 := merge 0 d (by omega)
  have h1 := merge d c (by omega)
  have h2 := merge (d+c) b (by omega)
  have h3 := merge (d+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have hr :
      (List.range' 0 (d-1) ++ [d-1]) ++
      (List.range' d (c-1) ++ [d+c-1]) ++
      (List.range' (d+c) (b-1) ++ [d+c+b-1]) ++
      (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1]) = List.range (size a b c d) := by
    rw [h0,h1,h2,show a+b+c+d-1=d+c+b+a-1 by omega,h3]
    have j0 : List.range' 0 d ++ List.range' d c=List.range' 0 (d+c) := by
      simpa using (List.range'_append_1 (s:=0) (m:=d) (n:=c))
    have j1 : List.range' 0 (d+c) ++ List.range' (d+c) b=List.range' 0 (d+c+b) := by
      simpa using (List.range'_append_1 (s:=0) (m:=d+c) (n:=b))
    have j2 : List.range' 0 (d+c+b) ++ List.range' (d+c+b) a=List.range' 0 (size a b c d) := by
      simpa [size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a))
    rw [j0,j1,j2]
    simp only [←List.range_eq_range']
  simpa [stock,full,terminal,chainLength,chainStart,
    MaxPlusTwo.Chambers.chamberLabels_full,List.append_assoc] using List.Perm.of_eq hr

private theorem inventory (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    (bankWord a b c d).Perm (List.range (size a b c d)) := by
  classical
  by_cases hf : isFinite a b c d
  · rcases hf with hf|hf|hf
    all_goals
      simp only [Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl,rfl,rfl⟩
      decide
  have hn1 : (a,b,c,d)≠(4,2,5,2) := fun he => hf (Or.inl he)
  have hn2 : (a,b,c,d)≠(4,2,6,2) := fun he => hf (Or.inr (Or.inl he))
  have hn3 : (a,b,c,d)≠(5,2,6,2) := fun he => hf (Or.inr (Or.inr he))
  have hfull := full_inventory a b c d hb hba hac hd hda
  have split (r : Fin 4) (m : ℕ) :
      (complement a b c d r m ++ stock a b c d r m).Perm
        (stock a b c d r (full a b c d r)) := by
    exact MaxPlusTwo.Chambers.chamberLabels_split _ _ _ _
      (by intro e he _; simp [full,Nat.testBit_two_pow_sub_one,he])
  by_cases hbd : b≤d
  · have hV :
        (complement a b c d 1 (h b c-1) ++ stock a b c d 1 (h b c-H a c) ++
          stock a b c d 1 (H a c-1)).Perm (stock a b c d 1 (full a b c d 1)) := by
      simpa [stock,complement,full,chainLength,chainStart,h,H] using
        labels_band_split (c-1) d (c-b-1) (c-a-1) 0 (by omega) (by positivity)
    have hVM := Multiset.coe_eq_coe.mpr hV
    by_cases ha1 : a=d+1
    · have hbr : branch a b c d=.a1 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_pos ha1]
      have hXM := Multiset.coe_eq_coe.mpr (split 3 1)
      apply List.Perm.trans ?_ hfull
      apply Multiset.coe_eq_coe.mp
      simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      simp only [←Multiset.coe_add,Multiset.coe_singleton] at hVM hXM ⊢
      rw [←hVM,←hXM]
      ac_rfl
    · have hbr : branch a b c d=.a2 := by simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_pos hbd,if_neg ha1]
      have hXM := Multiset.coe_eq_coe.mpr (split 3 (fmask a d))
      apply List.Perm.trans ?_ hfull
      apply Multiset.coe_eq_coe.mp
      simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      simp only [←Multiset.coe_add,Multiset.coe_singleton] at hVM hXM ⊢
      rw [←hVM,←hXM]
      ac_rfl
  · let J := min (a-b-1) (d-2)
    have hJ : jmask a b d=2^J := by
      dsimp [jmask,J]
      by_cases hp : a-b-1≤d-2
      · rw [Nat.min_eq_left hp,Nat.min_eq_left (Nat.pow_le_pow_right Nat.zero_lt_two hp)]
      · have hp' : d-2≤a-b-1 := by omega
        rw [Nat.min_eq_right hp',Nat.min_eq_right (Nat.pow_le_pow_right Nat.zero_lt_two hp')]
    have hJα : J≤a-d-2 := by dsimp [J]; have := Nat.min_le_left (a-b-1) (d-2); omega
    have hR : Rmask a b c d=2^(c-a+J) := by dsimp [Rmask,q]; rw [hJ,←pow_add]
    have hRV : c-a+J≤c-b-1 := by
      have := Nat.min_le_left (a-b-1) (d-2)
      dsimp [J] at *
      omega
    have hX :
        (complement a b c d 3 (mmask a b d ||| fmask a d) ++
          stock a b c d 3 (mmask a b d) ++ stock a b c d 3 (fmask a d)).Perm
            (stock a b c d 3 (full a b c d 3)) := by
      apply labels_three_split
      intro e he hm
      have heJ : e<J := by simpa [mmask,hJ,Nat.testBit_two_pow_sub_one] using hm
      simp [fmask,Nat.testBit_mul_two_pow,show ¬a-d-2≤e by omega]
    have hXM := Multiset.coe_eq_coe.mpr hX
    by_cases hb0 : d+2≤b
    · have hbr : branch a b c d=.b0 := by simp [branch,hn1,hn2,hn3,hbd,hb0]
      have hV :
          (complement a b c d 1 (h b c-1) ++
            stock a b c d 1 (h b c-Rmask a b c d) ++
            stock a b c d 1 (Rmask a b c d-1)).Perm
              (stock a b c d 1 (full a b c d 1)) := by
        simpa [stock,complement,full,chainLength,chainStart,h,hR] using
          labels_band_split (c-1) d (c-b-1) (c-a+J) 0 hRV (by positivity)
      have hVM := Multiset.coe_eq_coe.mpr hV
      apply List.Perm.trans ?_ hfull
      apply Multiset.coe_eq_coe.mp
      simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      simp only [←Multiset.coe_add,Multiset.coe_singleton] at hVM hXM ⊢
      rw [←hVM,←hXM]
      ac_rfl
    · by_cases hc1 : a+2≤c
      · have hRpos : 4≤Rmask a b c d := by
          rw [hR]
          exact Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤c-a+J by omega)
        have hδ : deltaMask a b c d<2^(c-a+J) := by
          rw [←hR]
          unfold deltaMask
          split_ifs
          · omega
          · apply Nat.div_lt_self (by omega)
            have hpa : 4≤2^a := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤a by omega)
            have hpb : 4≤2^b := Nat.pow_le_pow_right Nat.zero_lt_two hb
            nlinarith
        have hV :
            (complement a b c d 1 (h b c-1) ++
              stock a b c d 1 (h b c-Rmask a b c d+deltaMask a b c d) ++
              stock a b c d 1 ((Rmask a b c d-1) ^^^ deltaMask a b c d)).Perm
                (stock a b c d 1 (full a b c d 1)) := by
          simpa [stock,complement,full,chainLength,chainStart,h,hR] using
            labels_band_split (c-1) d (c-b-1) (c-a+J) (deltaMask a b c d) hRV hδ
        have hVM := Multiset.coe_eq_coe.mpr hV
        have hbranches : branch a b c d=.b1one ∨ branch a b c d=.b1quot := by
          simp only [branch,if_neg hn1,if_neg hn2,if_neg hn3,if_neg hbd,if_neg hb0,if_pos hc1]
          split_ifs <;> simp
        rcases hbranches with hbr|hbr
        all_goals
          apply List.Perm.trans ?_ hfull
          apply Multiset.coe_eq_coe.mp
          simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
          simp only [←Multiset.coe_add,Multiset.coe_singleton] at hVM hXM ⊢
          rw [←hVM,←hXM]
          ac_rfl
      · have ha2 : d+2≤a := by omega
        have hbr : branch a b c d=.c := by simp [branch,hn1,hn2,hn3,hbd,hb0,hc1]
        have hnu : rho a d/2=2^(a-d-1) := by
          conv_lhs =>
            dsimp [rho]
            rw [show a-d=(a-d-1)+1 by omega,pow_succ]
          omega
        have hV :
            (complement a b c d 1 (1 ||| rho a d/2) ++ stock a b c d 1 1 ++
              stock a b c d 1 (rho a d/2)).Perm (stock a b c d 1 (full a b c d 1)) := by
          apply labels_three_split
          intro e he hm
          have he0 : e=0 := by
            have hp : (2^0 : ℕ).testBit e=true := hm
            rw [Nat.testBit_two_pow] at hp
            exact (of_decide_eq_true hp).symm
          subst e
          rw [hnu,Nat.testBit_two_pow]
          simp only [decide_eq_false_iff_not]
          omega
        have hVM := Multiset.coe_eq_coe.mpr hV
        have hWM := Multiset.coe_eq_coe.mpr (split 2 1)
        have hXM := Multiset.coe_eq_coe.mpr (split 3 (3*rho a d/4-1))
        apply List.Perm.trans ?_ hfull
        apply Multiset.coe_eq_coe.mp
        simp only [bankWord,hbr,genericBanks,List.flatMap_cons,List.flatMap_nil,List.append_nil]
        simp only [←Multiset.coe_add,Multiset.coe_singleton] at hVM hWM hXM ⊢
        rw [←hVM,←hWM,←hXM]
        ac_rfl

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
    simpa only [←List.append_assoc,List.take_append_drop] using hs
  constructor
  · exact ((hp.map (oldValue a b c d)).sum_eq).trans ht.1
  · rw [(hins.map (newValue a b c d)).sum_eq]
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [(hp.map (newValue a b c d)).sum_eq,ht.2.1,ht.2.2]
    omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
