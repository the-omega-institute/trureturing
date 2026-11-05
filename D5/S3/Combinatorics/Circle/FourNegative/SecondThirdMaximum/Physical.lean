/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-by-endpoint)
   mirror-E: none(waiver:private-consumed-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Literal U,V,W,X banks and the original-source four-terminal lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private A B L K SU SV SW old2 new2 middle universal discrepancy selector_exists pow_split
  from D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum.Arithmetic
open private sourceMod base newBase charge nextBase nextNewBase oldValue newValue chain_values source_signs source_totals new_base_bounds from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size chainLength chainStart negatives)
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private actual_nat_joint_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private canonical_inventory stock full
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks

private def heads (len off : ℕ) : List ℕ := chamberLabels len off (2^len-1)
private def bank (a s d H p w : ℕ) (e : ℤ) : Fin 4→List ℕ :=
  let V := chamberLabels a d
  let WH := chamberLabels (s-a-1) (d+s+a)
  let X := chamberLabels (a-1) (d+s+s)
  ![heads (d-1) 0,
    V p ++ ((if e=1 then [d+s] else []) ++ WH H) ++ X w,
    V ((2^a-1) ^^^ p) ++
      ((if e=1 then [] else [d+s]) ++ WH ((2^(s-a-1)-1) ^^^ H)) ++
      X ((2^(a-1)-1) ^^^ w),
    heads (s-a-1) (d+a) ++ heads (a-1) (d+s+1)]
private def terminal (a s d : ℕ) : Fin 4→ℕ :=
  ![d+s+s-1,a+s+s+d-1,d-1,d+s-1]
private def word (a s d H p w : ℕ) (e : ℤ) : List ℕ :=
  let P:=bank a s d H p w e
  let T:=terminal a s d
  P 0++T 0::P 1++T 1::P 2++T 2::P 3++[T 3]

private theorem split (len off mask : ℕ) :
    (chamberLabels len off mask++chamberLabels len off ((2^len-1) ^^^ mask)).Perm
      (heads len off) := by
  exact List.perm_append_comm.trans (chamberLabels_split len off (2^len-1) mask
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he]))

private theorem v_partition (a s d p : ℕ) (has : a<s) :
    (chamberLabels a d p++chamberLabels a d ((2^a-1) ^^^ p)++
      heads (s-a-1) (d+a)).Perm (heads (s-1) d) := by
  have hp := (split a d p).append_right (heads (s-a-1) (d+a))
  have he : heads a d++heads (s-a-1) (d+a)=heads (s-1) d := by
    simp only [heads,chamberLabels_full]
    simpa only [show a+(s-a-1)=s-1 by omega] using
      (List.range'_append_1 (s:=d) (m:=a) (n:=s-a-1))
  exact hp.trans (List.Perm.of_eq he)

private theorem w_partition (a s d H : ℕ) (e : ℤ) (ha : 1≤a) (has : a<s) :
    (((if e=1 then [d+s] else [])++chamberLabels (s-a-1) (d+s+a) H)++
      ((if e=1 then [] else [d+s])++
        chamberLabels (s-a-1) (d+s+a) ((2^(s-a-1)-1) ^^^ H))++
      heads (a-1) (d+s+1)).Perm (heads (s-1) (d+s)) := by
  have hs := Multiset.coe_eq_coe.mpr (split (s-a-1) (d+s+a) H)
  simp only [←Multiset.coe_add] at hs
  have join : [d+s]++heads (a-1) (d+s+1)++heads (s-a-1) (d+s+a)=
      heads (s-1) (d+s) := by
    simp only [heads,chamberLabels_full]
    have h0 : [d+s]++List.range' (d+s+1) (a-1)=List.range' (d+s) a := by
      simpa [show 1+(a-1)=a by omega] using
        (List.range'_append_1 (s:=d+s) (m:=1) (n:=a-1))
    rw [h0]
    simpa only [show a+(s-a-1)=s-1 by omega] using
      (List.range'_append_1 (s:=d+s) (m:=a) (n:=s-a-1))
  apply Multiset.coe_eq_coe.mp
  rw [←join]
  simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
  by_cases he : e=1 <;> simp only [he,ite_true,ite_false,List.nil_append,List.append_nil]
  all_goals simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton,Multiset.coe_nil]
  all_goals rw [←hs]
  all_goals ac_rfl

private theorem inventory (a s d H p w : ℕ) (e : ℤ)
    (ha : 2≤a) (had : a<d) (hds : d<s) :
    (word a s d H p w e).Perm (List.range (a+s+s+d)) := by
  have hv := Multiset.coe_eq_coe.mpr (v_partition a s d p (by omega))
  have hw := Multiset.coe_eq_coe.mpr (w_partition a s d H e (by omega) (by omega))
  have hx := Multiset.coe_eq_coe.mpr (split (a-1) (d+s+s) w)
  simp only [←Multiset.coe_add] at hv hw hx
  have hc := canonical_inventory a s s d ha (by omega) (by omega) (by omega)
  change heads (d-1) 0++[d-1]++heads (s-1) d++[d+s-1]++
    heads (s-1) (d+s)++[d+s+s-1]++heads (a-1) (d+s+s)++[a+s+s+d-1]=
      List.range (a+s+s+d) at hc
  apply Multiset.coe_eq_coe.mp
  rw [←hc]
  simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
  rw [←hv,←hw,←hx]
  dsimp [word,bank,terminal]
  simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
  ac_rfl

private theorem good (a s d H p w : ℕ) (e : ℤ)
    (ha : 2≤a) (had : a<d) (hds : d<s)
    (r : Fin 4) (i : ℕ) (hi : i∈bank a s d H p w e r) :
    i<size a s s d ∧ i∉negatives a s s d := by
  have lab (len off mask : ℕ)
      (hgood : ∀ j<len, off+j<size a s s d ∧ off+j∉negatives a s s d)
      (hi : i∈chamberLabels len off mask) :
      i<size a s s d ∧ i∉negatives a s s d := by
    obtain ⟨j,hj,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
    exact hgood j hj
  have gu (mask : ℕ) (hi : i∈chamberLabels (d-1) 0 mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have gv (mask : ℕ) (hi : i∈chamberLabels a d mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have gwh (mask : ℕ) (hi : i∈chamberLabels (s-a-1) (d+s+a) mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have gx (mask : ℕ) (hi : i∈chamberLabels (a-1) (d+s+s) mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have gvh (mask : ℕ) (hi : i∈chamberLabels (s-a-1) (d+a) mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have gwl (mask : ℕ) (hi : i∈chamberLabels (a-1) (d+s+1) mask) :
      i<size a s s d ∧ i∉negatives a s s d :=
    lab _ _ _ (by intro j hj; simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]; omega) hi
  have bit (hi : i=d+s) : i<size a s s d ∧ i∉negatives a s s d := by
    subst i
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  fin_cases r
  · exact gu _ hi
  · dsimp [bank] at hi
    simp only [List.mem_append] at hi
    rcases hi with (hi|(hi|hi))|hi
    · exact gv _ hi
    · split_ifs at hi <;> simp only [List.mem_singleton,List.not_mem_nil] at hi
      exact bit hi
    · exact gwh _ hi
    · exact gx _ hi
  · dsimp [bank] at hi
    simp only [List.mem_append] at hi
    rcases hi with (hi|(hi|hi))|hi
    · exact gv _ hi
    · split_ifs at hi <;> simp only [List.mem_singleton,List.not_mem_nil] at hi
      exact bit hi
    · exact gwh _ hi
    · exact gx _ hi
  · dsimp [bank] at hi
    simp only [heads,List.mem_append] at hi
    rcases hi with hi|hi
    · exact gvh _ hi
    · exact gwl _ hi

/-- Only the first, second and last bank masses are needed: the intervening
bank endpoint is recovered from the exact total and the actual final suffix. -/
private theorem masses (a s d H p w : ℕ) (e : ℤ)
    (ha : 2≤a) (had : a<d) (hds : d<s)
    (hH : H<2^(s-a-1)) (hp : p<2^a) (hw : w<2^(a-1))
    (he : e=0 ∨ e=1) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ j<chainLength a s s d r-1,
      f (chainStart s s d r+j)=2^j*F r) :
    (((bank a s d H p w e 0).map f).sum)=((2:ℤ)^(d-1)-1)*F 0 ∧
    (((bank a s d H p w e 1).map f).sum)=
      (p:ℤ)*F 1+((2:ℤ)^a*H+e)*F 2+(w:ℤ)*F 3 ∧
    (((bank a s d H p w e 3).map f).sum)=
      ((2:ℤ)^(s-1)-(2:ℤ)^a)*F 1+((2:ℤ)^a-2)*F 2 := by
  have fullcap (len : ℕ) : 2^len-1<2^len := by have := Nat.two_pow_pos len; omega
  have castfull (len : ℕ) : ((2^len-1:ℕ):ℤ)=(2:ℤ)^len-1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow (n:=len))]
    push_cast; rfl
  have u := chamberLabels_sum (d-1) 0 (2^(d-1)-1) (fullcap _) f (F 0)
    (by intro j hj; simpa [chainStart] using hf 0 j (by simpa [chainLength] using hj))
  have vp := chamberLabels_sum a d p hp f (F 1)
    (by intro j hj; simpa [chainStart] using hf 1 j (by simp [chainLength]; omega))
  have wh := chamberLabels_sum (s-a-1) (d+s+a) H hH f ((2:ℤ)^a*F 2)
    (by
      intro j hj
      have h := hf 2 (a+j) (by simp [chainLength]; omega)
      simpa [chainStart,pow_add,Nat.add_assoc,mul_assoc,mul_comm,mul_left_comm] using h)
  have xw := chamberLabels_sum (a-1) (d+s+s) w hw f (F 3)
    (by intro j hj; simpa [chainStart] using hf 3 j (by simpa [chainLength] using hj))
  have vh := chamberLabels_sum (s-a-1) (d+a) (2^(s-a-1)-1) (fullcap _) f ((2:ℤ)^a*F 1)
    (by
      intro j hj
      have h := hf 1 (a+j) (by simp [chainLength]; omega)
      simpa [chainStart,pow_add,Nat.add_assoc,mul_assoc,mul_comm,mul_left_comm] using h)
  have wl := chamberLabels_sum (a-1) (d+s+1) (2^(a-1)-1) (fullcap _) f (2*F 2)
    (by
      intro j hj
      have h := hf 2 (1+j) (by simp [chainLength]; omega)
      simpa [chainStart,pow_add,Nat.add_assoc,mul_assoc,mul_comm,mul_left_comm] using h)
  have f0 : f (d+s)=F 2 := by
    simpa [chainStart] using hf 2 0 (by simp [chainLength]; omega)
  have hpow : (2:ℤ)^a*2^(s-a-1)=2^(s-1) := by rw [←pow_add]; congr 1; omega
  have hhalf : 2*(2:ℤ)^(a-1)=2^a := by
    simpa only [show a-(a-1)=1 by omega,pow_one,mul_comm] using
      (pow_split a (a-1) (by omega)).symm
  rw [castfull] at u vh wl
  refine ⟨by simpa [bank,heads] using u,?_,?_⟩
  · rcases he with rfl|rfl
    all_goals dsimp [bank]
    all_goals simp only [List.map_append,List.sum_append,List.map_cons,
      List.sum_cons,List.map_nil,List.sum_nil,zero_add,add_zero]
    all_goals rw [vp,wh,xw]
    all_goals try rw [f0]
    all_goals ring
  · dsimp [bank,heads]
    simp only [List.map_append,List.sum_append]
    rw [vh,wl]
    nlinarith only [congrArg (fun q : ℤ => q*F 1) hpow,
      congrArg (fun q : ℤ => q*F 2) hhalf]

private theorem physical_joint (a s d : ℕ) (ha : 2≤a) (had : a<d) (hds : d<s) :
    ∃ sigma : List (Fin (a+s+s+d)), ∃ j : ℕ, j≤a+s+s+d ∧
      OriginalOrder (a+s+s+d) (1+2^a+2^(a+s)+2^(a+s+s)) sigma ∧
      OriginalOrder (a+s+s+d+1) (2*(1+2^a+2^(a+s)+2^(a+s+s)))
        (earWord (a+s+s+d) sigma j) := by
  obtain ⟨n,H,e,p,w,hn,hnx,hH,hHJ,he,hp,hpx,hw,hnw,hm⟩ := selector_exists a s d ha had hds
  let x : ℤ:=2^a
  let t : ℤ:=2^d
  let z : ℤ:=2^s
  let k:=a+s+s+d
  let NN:=sourceMod a s s d
  let AA:=base a s s d 0
  let BB:=base a s s d 1
  let LL:=base a s s d 2
  let KK:=base a s s d 3
  let UU:=newBase a s s d 1
  let VV:=newBase a s s d 2
  let WW:=newBase a s s d 3
  let P:=bank a s d H.toNat p.toNat w.toNat e
  let T:=terminal a s d
  let l:=word a s d H.toNat p.toNat w.toNat e
  let f:=oldValue a s s d
  let g:=newValue a s s d
  let C:=fun q : ℕ => (2:ℤ)^(q-1)-1
  have Hcast : (H.toNat:ℤ)=H := Int.toNat_of_nonneg hH
  have pcast : (p.toNat:ℤ)=p := Int.toNat_of_nonneg hp
  have wcast : (w.toNat:ℤ)=w := Int.toNat_of_nonneg hw
  have Hcap : H.toNat<2^(s-a-1) := by exact_mod_cast (show (H.toNat:ℤ)<(2:ℤ)^(s-a-1) by simpa only [Hcast] using hHJ)
  have pcap : p.toNat<2^a := by exact_mod_cast (show (p.toNat:ℤ)<(2:ℤ)^a by simpa only [pcast] using hpx)
  have xhalf : 2*(2:ℤ)^(a-1)=x := by
    dsimp only [x]
    simpa only [show a-(a-1)=1 by omega,pow_one,mul_comm] using
      (pow_split a (a-1) (by omega)).symm
  have wcap : w.toNat<2^(a-1) := by
    exact_mod_cast (show (w.toNat:ℤ)<(2:ℤ)^(a-1) by rw [wcast]; nlinarith only [hnw,hn,xhalf])
  have hx : 4≤x := by dsimp [x]; have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha; norm_num at this; exact this
  have ht : 2*x≤t := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show a+1≤d by omega)
    simpa [x,t,pow_succ,mul_comm] using this
  have hz : 2*t≤z := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show d+1≤s by omega)
    simpa [z,t,pow_succ,mul_comm] using this
  have aa : AA=A x z := by dsimp [AA,base,A,x,z]; ring
  have bb : BB=B x t z := by dsimp [BB,base,B,x,t,z]; ring
  have ll : LL=L x t z := by dsimp [LL,base,L,x,t,z]; ring
  have kk : KK=K t z := by dsimp [KK,base,K,t,z]; ring
  have uu : UU=SU x t z := by dsimp [UU,newBase,charge,base,SU,B,x,t,z]; ring
  have vv : VV=SV x t z := by dsimp [VV,newBase,charge,base,SV,L,x,t,z]; ring
  have ww : WW=SW t z := by dsimp [WW,newBase,charge,base,SW,K,t,z]; ring
  have nn : NN=x*t*z^2-1 := by dsimp [NN,sourceMod,x,t,z]; ring
  have cu : 2*C d=t-2 := by
    have he : (2:ℤ)^d=2*2^(d-1) := by
      simpa only [show d-(d-1)=1 by omega,pow_one,mul_comm] using
        pow_split d (d-1) (by omega)
    dsimp [C,t]; omega
  have cv : 2*C s=z-2 := by
    have he : (2:ℤ)^s=2*2^(s-1) := by
      simpa only [show s-(s-1)=1 by omega,pow_one,mul_comm] using
        pow_split s (s-1) (by omega)
    dsimp [C,z]; omega
  have recU : t*AA=NN+BB := by dsimp [t,AA,NN,BB,base,sourceMod]; ring
  have recX : x*KK=NN+AA := by dsimp [x,KK,NN,AA,base,sourceMod]; ring
  have recUn : t*(2*AA)=2*NN+1+UU := by dsimp [t,AA,NN,UU,newBase,charge,base,sourceMod]; ring
  have recXn : x*WW=2*NN+1+AA := by dsimp [x,WW,NN,AA,newBase,charge,base,sourceMod]; ring
  have hpword : l.Perm (List.range k) := inventory a s d H.toNat p.toNat w.toNat e ha had hds
  have tab:=chain_values a s s d ha (by omega) (by omega) (by omega)
  have row (side : Bool) :
      (((P 0).map (if side then g else f)).sum)=C d*(if side then 2*AA else AA) ∧
      (((P 1).map (if side then g else f)).sum)=
        p*(if side then UU else BB)+(x*H+e)*(if side then VV else LL)+w*(if side then WW else KK) ∧
      (((P 3).map (if side then g else f)).sum)=
        (C s-x+1)*(if side then UU else BB)+(x-2)*(if side then VV else LL) := by
    let F:=if side then newBase a s s d else base a s s d
    have hf (r : Fin 4) (j : ℕ) (hj : j<chainLength a s s d r-1) :
        (if side then g else f) (chainStart s s d r+j)=2^j*F r := by
      cases side
      · exact (tab.2.1 r j (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r j (by omega)).trans (if_pos (by omega))
    have hmass:=masses a s d H.toNat p.toNat w.toNat e ha had hds Hcap pcap wcap he
      (if side then g else f) F hf
    have new0 : newBase a s s d 0=2*AA := by dsimp [newBase,charge,AA]; ring
    cases side
    all_goals
      simp only [F,ite_true,ite_false,Bool.false_eq_true,C,Hcast,pcast,wcast,new0] at hmass ⊢
      refine ⟨hmass.1,hmass.2.1,?_⟩
      calc
        _ = _ := hmass.2.2
        _ = _ := by dsimp only [x,BB,LL,UU,VV]; ring
  have mo:=row false
  have mn:=row true
  simp at mo mn
  have native (r : Fin 4) :
      C ((![d,s,s,a] : Fin 4→ℕ) r) * (base a s s d r)+
        f ((![d-1,d+s-1,d+s+s-1,k-1] : Fin 4→ℕ) r)=
          nextBase a s s d r-base a s s d r ∧
      C ((![d,s,s,a] : Fin 4→ℕ) r) * (newBase a s s d r)+
        g ((![d-1,d+s-1,d+s+s-1,k-1] : Fin 4→ℕ) r)=
          nextNewBase a s s d r-newBase a s s d r ∧
      2*f ((![d-1,d+s-1,d+s+s-1,k-1] : Fin 4→ℕ) r)=nextBase a s s d r-NN ∧
      2*g ((![d-1,d+s-1,d+s+s-1,k-1] : Fin 4→ℕ) r)=nextNewBase a s s d r-(2*NN+1) := by
    have hh:=native_masses a s s d ha (by omega) (by omega) (by omega) r
    have cast (len : ℕ) : ((2^(len-1)-1:ℕ):ℤ)=C len := by
      rw [Nat.cast_sub (Nat.one_le_two_pow (n:=len-1))]
      push_cast; rfl
    have idx : chainStart s s d r+(chainLength a s s d r-1)=
        (![d-1,d+s-1,d+s+s-1,k-1] : Fin 4→ℕ) r := by
      fin_cases r <;> dsimp [chainStart,chainLength,k] <;> omega
    dsimp only at hh
    simp only [cast,idx] at hh
    simpa only [chainLength] using hh
  have ntU:=native 0
  have ntV:=native 1
  have ntW:=native 2
  have ntX:=native 3
  change C d*AA+f (T 2)=BB-AA ∧ C d*(2*AA)+g (T 2)=UU-2*AA ∧
    2*f (T 2)=BB-NN ∧ 2*g (T 2)=UU-(2*NN+1) at ntU
  change C s*BB+f (T 3)=LL-BB ∧ C s*UU+g (T 3)=VV-UU ∧
    2*f (T 3)=LL-NN ∧ 2*g (T 3)=VV-(2*NN+1) at ntV
  change C s*LL+f (T 0)=KK-LL ∧ C s*VV+g (T 0)=WW-VV ∧
    2*f (T 0)=KK-NN ∧ 2*g (T 0)=WW-(2*NN+1) at ntW
  change C a*KK+f (T 1)=AA-KK ∧ C a*WW+g (T 1)=AA-WW ∧
    2*f (T 1)=AA-NN ∧ 2*g (T 1)=AA-(2*NN+1) at ntX
  have totals:=source_totals a s s d ha (by omega) (by omega) (by omega)
  have fzero : (l.map f).sum=0 := (hpword.map f).sum_eq.trans totals.1
  have gzero : AA+(l.map g).sum=0 := by
    have hh:=(hpword.map g).sum_eq.trans totals.2.1
    change (l.map g).sum= -AA at hh
    omega
  have gear : g k=AA := totals.2.2
  let Pn : Fin 4→List ℕ := ![k::P 0,P 1,P 2,P 3]
  let ln:=Pn 0++T 0::Pn 1++T 1::Pn 2++T 2::Pn 3++[T 3]
  have pn0 : ((Pn 0).map g).sum=AA+((P 0).map g).sum := by simp [Pn,gear]
  have lnzero : (ln.map g).sum=0 := by simpa [ln,Pn,l,word,gear] using gzero
  have o0 : 2*(((P 0).map f).sum+f (T 0))=BB+KK-2*AA := by
    nlinarith only [mo.1,ntW.2.2.1,congrArg (fun q : ℤ => q*AA) cu,recU]
  have n0 : 2*(((Pn 0).map g).sum+g (T 0))=UU+WW-2*AA := by
    nlinarith only [pn0,mn.1,ntW.2.2.2,congrArg (fun q : ℤ => q*(2*AA)) cu,recUn]
  have o1 : 2*(((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1))=
      old2 x t z n (x*H+e) p := by
    have rel:=congrArg (fun q : ℤ => q*KK) hnw
    dsimp [old2]
    rw [←bb,←ll,←kk]
    nlinarith only [o0,mo.2.1,ntX.2.2.1,rel,recX]
  have n1 : 2*(((Pn 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1))=
      new2 x t z n (x*H+e) p := by
    have rel:=congrArg (fun q : ℤ => q*WW) hnw
    dsimp [new2]
    rw [←uu,←vv,←ww]
    nlinarith only [n0,mn.2.1,ntX.2.2.2,rel,recXn]
  have o3 : ((P 3).map f).sum+f (T 3)= -(x*BB-(x-1)*LL) := by
    nlinarith only [mo.2.2,ntV.1]
  have n3 : ((P 3).map g).sum+g (T 3)= -(x*UU-(x-1)*VV) := by
    nlinarith only [mn.2.2,ntV.2.1]
  have o2 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)=x*BB-(x-1)*LL := by
    dsimp [l,word] at fzero
    simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_singleton,List.sum_singleton,List.map_nil,List.sum_nil,add_zero] at fzero
    linarith only [fzero,o3]
  have n2 : ((Pn 0).map g).sum+g (T 0)+((P 1).map g).sum+g (T 1)+
      ((P 2).map g).sum+g (T 2)=x*UU-(x-1)*VV := by
    dsimp [ln] at lnzero
    simp only [Pn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',
      List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.map_singleton,List.sum_singleton,List.map_nil,List.sum_nil,add_zero,gear] at lnzero
    rw [←pn0] at lnzero
    linarith only [lnzero,n3]
  have pos (r : Fin 4) (i : ℕ) (hi : i∈P r) : 0≤f i ∧ 0≤g i := by
    have gg:=good a s d H.toNat p.toNat w.toNat e ha had hds r i hi
    have hs:=source_signs a s s d ha (by omega) (by omega) (by omega) i gg.1
    rw [if_neg gg.2] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have un:=universal x t z hx ht hz
  rw [←aa,←bb,←ll,←kk,←uu,←vv,←ww,←nn] at un
  have Jz : 2*x*(2:ℤ)^(s-a-1)=z := by
    dsimp [x,z]
    calc
      2*(2:ℤ)^a*2^(s-a-1)=2^(a+(s-a-1)+1) := by rw [pow_succ,pow_add]; ring
      _=2^s := by congr 1; omega
  have dis:=discrepancy x t z n H e p (2^(s-a-1)) hx (by omega) hn hHJ he hpx Jz
  have midO : 0≤old2 x t z n (x*H+e) p ∧ old2 x t z n (x*H+e) p≤AA-1 := by
    rw [aa]
    exact ⟨hm.1,by nlinarith only [hm.1,hm.2,dis]⟩
  have midN : 0≤new2 x t z n (x*H+e) p ∧ new2 x t z n (x*H+e) p≤AA-1 := by
    rw [aa]
    exact ⟨by nlinarith only [hm.1,dis],hm.2⟩
  have hbases:=tab.1 2
  have nbases:=new_base_bounds a s s d ha (by omega) (by omega) (by omega) 2
  change 1≤LL ∧ LL<NN at hbases
  change 1≤VV ∧ VV<2*NN+1 at nbases
  have div:=Int.emod_add_mul_ediv NN 2
  have rem0:=Int.emod_nonneg NN (by decide : (2:ℤ)≠0)
  have rem1:=Int.emod_lt_of_pos NN (by decide : (0:ℤ)<2)
  have oldstrip : InStrip f (NN/2) 0 l := by
    change InStrip f (NN/2) 0 (P 0++T 0::P 1++T 1::P 2++T 2::P 3++[T 3])
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (NN/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · constructor <;> nlinarith only [o0,ntW.2.2.1,un.1,un.2.1,div,rem0,rem1]
    · constructor <;> nlinarith only [o1,ntX.2.2.1,midO.1,midO.2,div,rem0,rem1]
    · constructor <;> nlinarith only [o2,ntU.2.2.1,un.2.2.2.2.1,un.2.2.2.2.2.1,div,rem0,rem1]
    · constructor <;> omega
    · simpa only [l,word,zero_add] using fzero
  have npos (i : ℕ) (hi : i∈Pn 0) : 0≤g i := by
    simp only [Pn,Matrix.cons_val_zero,List.mem_cons] at hi
    rcases hi with rfl|hi
    · rw [gear]
      have := (tab.1 0).1
      exact le_trans (by omega : (0:ℤ)≤1) this
    · exact (pos 0 i hi).2
  have newstrip : InStrip g NN 0 ln := by
    apply four_strip g (Pn 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) NN 0
      npos (fun i hi => (pos 1 i hi).2) (fun i hi => (pos 2 i hi).2)
      (fun i hi => (pos 3 i hi).2) le_rfl
    · constructor <;> nlinarith only [n0,ntW.2.2.2,un.2.2.1,un.2.2.2.1]
    · constructor <;> nlinarith only [n1,ntX.2.2.2,midN.1,midN.2]
    · constructor <;> nlinarith only [n2,ntU.2.2.2,un.2.2.2.2.2.2.1,un.2.2.2.2.2.2.2.1]
    · constructor <;> omega
    · simpa only [ln,Pn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',zero_add] using lnzero
  apply (actual_nat_joint_iff a s s d ha (by omega) (by omega) (by omega)).mpr
  refine ⟨l,hpword,oldstrip,0,by omega,?_⟩
  simpa [insertAt,size,k,l,word,ln,Pn,List.append_assoc] using newstrip

end D5.S3.Combinatorics.Circle.FourNegative.SecondThirdMaximum
