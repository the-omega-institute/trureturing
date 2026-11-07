/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Schedule
   generality: I
   mirror-B: none(waiver:private-consumed-moderate-third-gap-construction)
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: exact physical banks and the two literal cuts after W- and X-. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B C D E K L N x y z t lam sAt FAt ZAt Selected
  selector_arithmetic outside_seams power_data PowerData
  Selected.u Selected.H Selected.early Selected.u_le Selected.Hhi
  Selected.slo Selected.shi Selected.second_lo Selected.second_hi PowerData.y_eq
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Arithmetic
open private bank terminal word bank_inventory bank_good bank_masses bank_double_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
  (size base newBase oldValue newValue negatives chainLength chainStart blocksWord insertAt)
open private seed sourceMod charge nextBase nextNewBase
  source_signs source_totals chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

private theorem source_terminal_table (a b c d : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b) (i : Fin 4) :
    let len := chainLength a b c d i
    let j := chainStart b c d i+(len-1)
    (((2^(len-1)-1:ℕ):ℤ)*base a b c d i+oldValue a b c d j=
      nextBase a b c d i-base a b c d i) ∧
    (((2^(len-1)-1:ℕ):ℤ)*newBase a b c d i+newValue a b c d j=
      nextNewBase a b c d i-newBase a b c d i) ∧
    2*oldValue a b c d j=nextBase a b c d i-sourceMod a b c d ∧
    2*newValue a b c d j=nextNewBase a b c d i-(2*sourceMod a b c d+1) :=
  native_masses a b c d ha (by omega) (by omega) (by omega) i

set_option maxHeartbeats 1600000 in
private theorem joint_construction (a b c d : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b) (hmoder : c≤a+d) :
    ∃ l : List ℕ, l.Perm (List.range (size a b c d)) ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 l ∧
      ∃ j : ℕ, j≤size a b c d ∧
        InStrip (newValue a b c d) (sourceMod a b c d) 0
          (insertAt (size a b c d) l j) := by
  classical
  obtain ⟨q⟩ := selector_arithmetic a b c d ha had hdc hcb hmoder
  let u := (Selected.u q); let H := (Selected.H q)
  let P := bank a b c d u H
  let T := terminal a b c d
  let l := word a b c d u H
  let f := oldValue a b c d; let g := newValue a b c d
  let k := size a b c d; let NN := sourceMod a b c d
  let AA := A (x a) (y b) (z c); let BB := B (x a) (y b) (t d)
  let LL := L (x a) (z c) (t d); let KK := K (y b) (z c) (t d)
  let DD := D (y b) (z c); let CC := C (x a) (z c) (t d) (lam b c)
  let SU := 2*BB-1; let SV := 2*LL-z c-1; let SW := 2*KK-DD
  let S1 := BB+KK-2*((u:ℤ)+1)*AA
  let S2 := sAt (E (x a) (y b) (z c) (t d)) AA CC u H
  let S3 := 2*BB-CC
  let T1 := 2*S1-DD-1
  let T2 := 2*FAt (E (x a) (y b) (z c) (t d)) AA CC (z c) (lam b c) u H+
    (if (Selected.early q) then AA else -AA)-1
  let T3 := 2*(SU-lam b c*SV)
  have hu : u=0 ∨ u=1 ∨ u=2 := by have := (Selected.u_le q); dsimp [u]; omega
  have hH : H<2^c := by
    have hp := Nat.two_pow_pos c
    have := (Selected.Hhi q)
    dsimp [H]
    omega
  have hp : l.Perm (List.range k) := bank_inventory a b c d u H ha had hdc hcb hu hH
  have p := power_data a b c d ha had hdc hcb hmoder
  have b0 : base a b c d 0=AA := by dsimp [base,AA,A,x,y,z]; ring
  have b1 : base a b c d 1=BB := by dsimp [base,BB,B,x,y,t]; ring
  have b2 : base a b c d 2=LL := by dsimp [base,LL,L,x,z,t]; ring
  have b3 : base a b c d 3=KK := by dsimp [base,KK,K,y,z,t]; ring
  have n0 : newBase a b c d 0=2*AA := by simp [newBase,charge,b0]
  have n1 : newBase a b c d 1=SU := by simp [newBase,charge,b1,SU]
  have n2 : newBase a b c d 2=SV := by simp [newBase,charge,b2,SV,z] <;> ring
  have n3 : newBase a b c d 3=SW := by simp [newBase,charge,b3,SW,DD,D,y,z]
  have hNN : NN=N (x a) (y b) (z c) (t d) := by dsimp [NN,sourceMod,N,x,y,z,t]
  have hb := (chain_values a b c d ha (by omega) (by omega) (by omega)).1
  have hAA : 1≤AA := by simpa only [b0] using (hb 0).1
  have hLL : 1≤LL := by simpa only [b2] using (hb 2).1
  have hSV : 1≤SV := by
    simpa only [n2] using (new_base_bounds a b c d ha (by omega) (by omega) (by omega) 2).1
  have hNNpos : 0<NN := by have hh := hb 0; dsimp [NN]; omega
  have hfresh : g k=AA := by
    exact (source_totals a b c d ha (by omega) (by omega) (by omega)).2.2.trans b0
  have good (j : Fin 4) (i : ℕ) (hi : i∈P j) : i<k ∧ i∉negatives a b c d :=
    bank_good a b c d u H ha had hdc hcb j i hi
  have posold (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0≤f i := by
    have hs := source_signs a b c d ha (by omega) (by omega) (by omega) i (good j i hi).1
    rw [if_neg (good j i hi).2] at hs
    exact hs.1.le
  have posnew (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0≤g i := by
    have hs := source_signs a b c d ha (by omega) (by omega) (by omega) i (good j i hi).1
    rw [if_neg (good j i hi).2] at hs
    exact hs.2.le
  have negold (j : Fin 4) : f (T j)≤0 := by
    have hs := source_signs a b c d ha (by omega) (by omega) (by omega) (T j)
      (by fin_cases j <;> dsimp [T,terminal,k,size] <;> omega)
    rw [if_pos (by fin_cases j <;> simp [T,terminal,negatives,size])] at hs
    exact hs.1.le
  have negnew (j : Fin 4) : g (T j)≤0 := by
    have hs := source_signs a b c d ha (by omega) (by omega) (by omega) (T j)
      (by fin_cases j <;> dsimp [T,terminal,k,size] <;> omega)
    rw [if_pos (by fin_cases j <;> simp [T,terminal,negatives,size])] at hs
    exact hs.2.le
  have mo := bank_double_masses a b c d u H ha had hdc hcb hu hH false
  have mn := bank_double_masses a b c d u H ha had hdc hcb hu hH true
  simp only [Bool.false_eq_true,ite_false,ite_true] at mo mn
  rw [b0,b1,b2,b3] at mo
  rw [n0,n1,n2,n3] at mn
  change 2*((P 0).map f).sum=(t d-2-2*(u:ℤ))*AA ∧
    2*((P 1).map f).sum=2*lam b c*(H:ℤ)*LL ∧
    2*((P 2).map f).sum=2*lam b c*(z c-1-(H:ℤ))*LL+
      (x a-2)*KK+2*(u:ℤ)*AA ∧
    2*((P 3).map f).sum=(z c-2)*BB+2*(lam b c-1)*LL at mo
  change 2*((P 0).map g).sum=(t d-2-2*(u:ℤ))*(2*AA) ∧
    2*((P 1).map g).sum=2*lam b c*(H:ℤ)*SV ∧
    2*((P 2).map g).sum=2*lam b c*(z c-1-(H:ℤ))*SV+
      (x a-2)*SW+2*(u:ℤ)*(2*AA) ∧
    2*((P 3).map g).sum=(z c-2)*SU+2*(lam b c-1)*SV at mn
  have term0 := source_terminal_table a b c d ha had hdc hcb 2
  have term1 := source_terminal_table a b c d ha had hdc hcb 3
  have term2 := source_terminal_table a b c d ha had hdc hcb 0
  have term3 := source_terminal_table a b c d ha had hdc hcb 1
  have negs :
      (2*f (T 0)=KK-NN ∧ 2*g (T 0)=SW-(2*NN+1)) ∧
      (2*f (T 1)=AA-NN ∧ 2*g (T 1)=AA-(2*NN+1)) ∧
      (2*f (T 2)=BB-NN ∧ 2*g (T 2)=SU-(2*NN+1)) ∧
      (2*f (T 3)=LL-NN ∧ 2*g (T 3)=SV-(2*NN+1)) := by
    have ht0 : d+c+(b-1)=d+c+b-1 := by omega
    have ht1 : d+c+b+(a-1)=a+b+c+d-1 := by omega
    have ht2 : 0+(d-1)=d-1 := by omega
    have ht3 : d+(c-1)=d+c-1 := by omega
    dsimp [chainStart,chainLength,nextBase,nextNewBase] at term0 term1 term2 term3
    dsimp [f,g,T,terminal,NN]
    simpa only [ht0,ht1,ht2,ht3,
      b0,b1,b2,b3,n0,n1,n2,n3] using
      (show (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _) from
        ⟨term0.2.2,term1.2.2,term2.2.2,term3.2.2⟩)
  have so1 : 2*(((P 0).map f).sum+f (T 0))=S1 := by
    calc
      _=((t d)-2-2*(u:ℤ))*AA+(KK-NN) := by linarith only [mo.1,negs.1.1]
      _=S1 := by dsimp [S1,AA,BB,KK,A,B,K,NN,sourceMod,x,y,z,t]; ring
  have so2 : 2*(((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1))=S2 := by
    calc
      _=S1+2*lam b c*(H:ℤ)*LL+AA-NN := by linarith only [so1,mo.2.1,negs.2.1.1]
      _=S2 := by dsimp [S1,S2,AA,BB,KK,CC,LL,sAt,C,E,N,A,B,K,L,NN,sourceMod,lam,x,y,z,t]; ring
  have so3 : 2*(((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2))=S3 := by
    calc
      _=S1+2*lam b c*(H:ℤ)*LL+AA-NN+
          2*lam b c*(z c-1-(H:ℤ))*LL+(x a-2)*KK+2*(u:ℤ)*AA+BB-NN := by
        linarith only [so1,mo.2.1,mo.2.2.1,negs.2.1.1,negs.2.2.1.1]
      _=S3 := by
        simp only [hNN]
        dsimp [S1,S3,AA,BB,KK,CC,LL,C,A,B,K,L,N]
        simp only [(PowerData.y_eq p)]
        ring
  have totals := source_totals a b c d ha (by omega) (by omega) (by omega)
  have oldzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have sharedzero : (l.map g).sum=-AA := by
    rw [(hp.map g).sum_eq]
    simpa only [b0] using totals.2.1
  have so4 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)+((P 3).map f).sum+f (T 3)=0 := by
    simpa [l,word,P,T,List.map_append,List.sum_append,add_assoc] using oldzero
  have seams := outside_seams a b c d ha had hdc hcb hmoder q
  have s1range : 0<S1 ∧ S1≤KK-1 := seams.1
  have t1range : 0<T1 ∧ T1≤SW-1 := seams.2.1
  have s3range : 0<S3 ∧ S3≤BB-1 := seams.2.2.1
  have t3range : 0<T3 ∧ T3≤SU-1 := by
    simpa [T3,SU,BB,SV,LL,sub_sub] using seams.2.2.2
  have s2range : 0<S2 ∧ S2≤AA-1 := ⟨(Selected.slo q),(Selected.shi q)⟩
  have t2range : 0<T2 ∧ T2≤AA-1 := ⟨(Selected.second_lo q),(Selected.second_hi q)⟩
  have oldChecks : packetChecks f (NN/2) 0
      [(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)] := by
    simp only [packetChecks,zero_add]
    repeat' constructor
    all_goals first
      | trivial
      | (apply (Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ)<2)).mpr
         linarith only [so1,so2,so3,so4,negs.1.1,negs.2.1.1,negs.2.2.1.1,
           negs.2.2.2.1,s1range.2,s2range.2,s3range.2,hLL])
      | linarith only [so1,so2,so3,so4,s1range.1,s2range.1,s3range.1]
  have oldstrip : InStrip f (NN/2) 0 l := by
    have wordblocks : l=blocksWord [(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)] := by
      simp [l,word,P,T,blocksWord,List.append_assoc]
    rw [wordblocks]
    apply (strip_iff_packetChecks f (NN/2) 0
      [(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)]
      ⟨by omega,Int.ediv_nonneg (by omega) (by norm_num)⟩ ?_ ?_).mpr oldChecks
    · intro b hb i hi
      simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact posold 0 i hi
      · exact posold 1 i hi
      · exact posold 2 i hi
      · exact posold 3 i hi
    · intro b hb
      simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact negold 0
      · exact negold 1
      · exact negold 2
      · exact negold 3
  /- The new label starts bank 1 or bank 2.  This is the literal timing,
     rather than the right-normalized withEar timing at a bank's end. -/
  let Pe : Fin 4 → List ℕ := fun j =>
    if ((Selected.early q)=true ∧ j=1) ∨ ((Selected.early q)=false ∧ j=2) then k::P j else P j
  let delta : ℤ := if (Selected.early q) then 1 else 0
  have pe0 : ((Pe 0).map g).sum=((P 0).map g).sum := by
    cases he : (Selected.early q) <;> simp [Pe,he]
  have pe1 : ((Pe 1).map g).sum=((P 1).map g).sum+delta*AA := by
    cases he : (Selected.early q) <;> simp [Pe,he,delta,hfresh,add_comm]
  have pe2 : ((Pe 2).map g).sum=((P 2).map g).sum+(1-delta)*AA := by
    cases he : (Selected.early q) <;> simp [Pe,he,delta,hfresh,add_comm]
  have pe3 : ((Pe 3).map g).sum=((P 3).map g).sum := by
    cases he : (Selected.early q) <;> simp [Pe,he]
  have sn1 : 2*(((Pe 0).map g).sum+g (T 0))=T1 := by
    rw [pe0]
    calc
      _=(t d-2-2*(u:ℤ))*(2*AA)+SW-(2*NN+1) := by
        linarith only [mn.1,negs.1.2]
      _=T1 := by
        dsimp [T1,S1,SW,AA,BB,KK,DD,A,B,K,D,NN,sourceMod,x,y,z,t]
        ring
  have sn2 : 2*(((Pe 0).map g).sum+g (T 0)+((Pe 1).map g).sum+g (T 1))=T2 := by
    rw [pe1]
    calc
      _=T1+2*lam b c*(H:ℤ)*SV+2*delta*AA+AA-(2*NN+1) := by
        linarith only [sn1,mn.2.1,negs.2.1.2]
      _=T2 := by
        simp only [hNN]
        dsimp [T1,S1,T2,AA,BB,KK,DD,CC,SV,LL,FAt,sAt,ZAt,A,B,C,D,E,N,K,L]
        simp only [(PowerData.y_eq p)]
        cases he : (Selected.early q) <;>
          simp only [delta,he,Bool.false_eq_true,ite_true,ite_false] <;> ring
  have sn3 : 2*(((Pe 0).map g).sum+g (T 0)+((Pe 1).map g).sum+g (T 1)+
      ((Pe 2).map g).sum+g (T 2))=T3 := by
    rw [pe1,pe2]
    calc
      _=T1+2*lam b c*(H:ℤ)*SV+2*delta*AA+AA-(2*NN+1)+
          2*lam b c*(z c-1-(H:ℤ))*SV+(x a-2)*SW+2*(u:ℤ)*(2*AA)+
          2*(1-delta)*AA+SU-(2*NN+1) := by
        linarith only [sn1,mn.2.1,mn.2.2.1,negs.2.1.2,negs.2.2.1.2]
      _=T3 := by
        simp only [hNN]
        dsimp [T1,S1,T3,AA,BB,KK,DD,SV,SW,SU,LL,N,A,B,K,D,L]
        simp only [(PowerData.y_eq p)]
        ring
  have sn4 : ((Pe 0).map g).sum+g (T 0)+((Pe 1).map g).sum+g (T 1)+
      ((Pe 2).map g).sum+g (T 2)+((Pe 3).map g).sum+g (T 3)=0 := by
    have hs : ((P 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1)+
        ((P 2).map g).sum+g (T 2)+((P 3).map g).sum+g (T 3)=-AA := by
      simpa [l,word,P,T,List.map_append,List.sum_append,add_assoc] using sharedzero
    rw [pe0,pe1,pe2,pe3]
    linarith only [hs]
  have newChecks : packetChecks g NN 0
      [(Pe 0,T 0),(Pe 1,T 1),(Pe 2,T 2),(Pe 3,T 3)] := by
    simp only [packetChecks,zero_add]
    repeat' constructor
    all_goals first
      | trivial
      | linarith only [sn1,sn2,sn3,sn4,negs.1.2,negs.2.1.2,negs.2.2.1.2,
          negs.2.2.2.2,t1range.1,t1range.2,t2range.1,t2range.2,t3range.1,t3range.2,
          hSV]
  have pePositive (j : Fin 4) (i : ℕ) (hi : i∈Pe j) : 0≤g i := by
    dsimp [Pe] at hi
    split_ifs at hi
    · rcases List.mem_cons.mp hi with rfl|hi
      · rw [hfresh]; omega
      · exact posnew j i hi
    · exact posnew j i hi
  have markedstrip : InStrip g NN 0
      (blocksWord [(Pe 0,T 0),(Pe 1,T 1),(Pe 2,T 2),(Pe 3,T 3)]) := by
    apply (strip_iff_packetChecks g NN 0
      [(Pe 0,T 0),(Pe 1,T 1),(Pe 2,T 2),(Pe 3,T 3)] ⟨by omega,by omega⟩ ?_ ?_).mpr newChecks
    · intro b hb i hi
      simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact pePositive 0 i hi
      · exact pePositive 1 i hi
      · exact pePositive 2 i hi
      · exact pePositive 3 i hi
    · intro b hb
      simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      · exact negnew 0
      · exact negnew 1
      · exact negnew 2
      · exact negnew 3
  let pre := if (Selected.early q) then P 0 ++ [T 0]
    else P 0 ++ [T 0] ++ P 1 ++ [T 1]
  let post := if (Selected.early q) then P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]
    else P 2 ++ T 2 :: P 3 ++ [T 3]
  have split : l=pre++post := by
    cases he : (Selected.early q) <;> simp [pre,post,he,l,word,P,T,List.append_assoc]
  have marked : blocksWord [(Pe 0,T 0),(Pe 1,T 1),(Pe 2,T 2),(Pe 3,T 3)]=
      pre++k::post := by
    cases he : (Selected.early q) <;> simp [Pe,pre,post,he,blocksWord,List.append_assoc]
  have hj : pre.length≤k := by
    have hh := hp.length_eq
    rw [split] at hh
    simp only [List.length_append,List.length_range] at hh
    omega
  have literal : insertAt k l pre.length=
      blocksWord [(Pe 0,T 0),(Pe 1,T 1),(Pe 2,T 2),(Pe 3,T 3)] := by
    rw [split,marked]
    simp [insertAt]
  exact ⟨l,hp,oldstrip,pre.length,hj,by rw [literal]; exact markedstrip⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
