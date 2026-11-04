/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Lower
   generality: I
   mirror-B: none(waiver:private-sector-consumed-by-whole-face)
   mirror-E: none(waiver:private-sector-consumed-by-whole-face)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Paid U/W masks in W-U-X-V order with literal cut zero. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.LowerArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding

/-! Paid U/W masks in W-U-X-V order with literal cut zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size sourceMod base newBase charge oldValue newValue chainLength chainStart
  source_totals chain_values nextBase nextNewBase
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private mask full terminal full_split chain_inventory mask_mass mask_positive complement_mass
  terminal_double terminal_nonpositive source_odd native_balance four_checks freshAfter
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private A B L H K SU SV SW heads_positive dictionary pow_split pow_lower full_cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source
open private marked marked_total realize_packets
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical
open private lower_windows cert_K_above_L cert_N_above_L
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.LowerArithmetic
open private positive_ceiling from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding

set_option maxHeartbeats 2400000 in
private theorem lower_lift (a b c : ℕ) (hc : 2≤c) (hca : c<a) (hab : a<b) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j≤a+b+c+a ∧
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma j) := by
  have ha : 2≤a := by omega
  have hb : 2≤b := by omega
  let s : ℕ:=2^(a-c)
  let h : ℕ:=2^(b-a-1)
  let x : ℤ:=2^a
  let z : ℤ:=2^c
  let y : ℤ:=2^b
  let t : ℕ:=if a=c+1 then 2 else 3*2^(a-c-2)
  have hs : (2:ℤ)≤s := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤a-c))
  have hz : 4≤z := by simpa [z] using pow_lower c 2 hc
  have hh : (1:ℤ)≤h := by exact_mod_cast (Nat.one_le_two_pow (n:=b-a-1))
  have xs : x=(s:ℤ)*z := by
    simpa [x,s,z] using pow_split a c (by omega)
  have yh : y=2*x*h := by
    dsimp [y,x,h]
    push_cast
    calc
      (2:ℤ)^b=2^(a+(b-a-1)+1) := congrArg (fun n : ℕ => (2:ℤ)^n) (by omega)
      _ = 2*2^a*2^(b-a-1) := by rw [pow_add,pow_add]; norm_num; ring
  have ht : ((s:ℤ)=2 ∧ (t:ℤ)=2) ∨ ∃ q : ℤ, 1≤q ∧ (s:ℤ)=4*q ∧ (t:ℤ)=3*q := by
    by_cases he : a=c+1
    · left
      simp [s,t,he,show a-c=1 by omega]
    · right
      refine ⟨2^(a-c-2),by simpa using pow_lower (a-c-2) 0 (Nat.zero_le _),?_,?_⟩
      · dsimp [s]
        push_cast
        rw [show a-c=(a-c-2)+2 by omega,pow_add]
        norm_num
        ring
      · simp [t,he]
  have hhd : (h:ℤ)=1 ∨ (h:ℤ)=2 ∨ 4≤(h:ℤ) := by
    by_cases h0 : b=a+1
    · left; simp [h,show b-a-1=0 by omega]
    · by_cases h1 : b=a+2
      · exact Or.inr (Or.inl (by simp [h,show b-a-1=1 by omega]))
      · exact Or.inr (Or.inr (by simpa [h] using pow_lower (b-a-1) 2 (by omega)))
  have hL : 1≤L x z := by
    have hx0 : 0≤x := by dsimp [x]; positivity
    have hz0 : 0≤z := by omega
    have hp : 0≤L x z-1 := by dsimp [L]; ring_nf; positivity
    omega
  have hKL : 1≤K x y z-L x z := by
    have hp:=cert_K_above_L s z h hs hz hh
    rw [xs,yh,xs]
    dsimp [K,H,L] at *
    nlinarith only [hp]
  let ri:=(K x y z+L x z-1)/(2*L x z)
  have ceil:=positive_ceiling (K x y z-L x z) (2*L x z) hKL (by omega)
  have numerator : K x y z-L x z+2*L x z-1=K x y z+L x z-1 := by ring
  have upper : K x y z-L x z+2*L x z=K x y z+L x z := by ring
  dsimp only at ceil
  rw [numerator,upper] at ceil
  change 1≤ri ∧ K x y z-L x z≤2*L x z*ri ∧ 2*L x z*ri<K x y z+L x z at ceil
  let r:=ri.toNat
  have rc : (r:ℤ)=ri := Int.toNat_of_nonneg (by omega)
  have hr : 1≤r := by omega
  have hceil : K x y z-L x z≤2*(r:ℤ)*L x z ∧ 2*(r:ℤ)*L x z<K x y z+L x z := by
    rw [rc]; constructor <;> nlinarith only [ceil.2.1,ceil.2.2]
  have rcap : r<2^(b-1) := by
    have hp:=cert_N_above_L s z h hs hz hh
    have hNL : L x z≤x^2*y*z-1 := by
      rw [xs,yh,xs]
      dsimp [L] at *
      nlinarith only [hp]
    have hyL : y*L x z=x^2*y*z-1+K x y z := by dsimp [L,K,H]; ring
    have hpw : y=2*(2^(b-1):ℕ) := by
      dsimp [y]
      rw [show b=(b-1)+1 by omega,pow_succ]
      push_cast
      ring
    by_contra hn
    have rn : (2^(b-1):ℕ)≤r := by omega
    have rz : ((2^(b-1):ℕ):ℤ)≤r := by exact_mod_cast rn
    have hm:=mul_le_mul_of_nonneg_right rz (show 0≤L x z by omega)
    have hpwL:=congrArg (fun n : ℤ => n*L x z) hpw
    nlinarith only [hm,hpwL,hNL,hyL,hceil.2]
  have ht0 : 1≤t := by
    rcases ht with ⟨_,ht⟩|⟨q,hq,_,ht⟩ <;> omega
  have tcap : t≤2^(a-1) := by
    have hpw : x=2*(2^(a-1):ℕ) := by
      dsimp [x]
      rw [show a=(a-1)+1 by omega,pow_succ]
      push_cast
      ring
    rcases ht with ⟨hs2,ht2⟩|⟨q,hq,hsq,htq⟩
    · have xx : 4≤x := by simpa [x] using pow_lower a 2 ha
      exact_mod_cast (show (t:ℤ)≤(2^(a-1):ℕ) by omega)
    · have hm:=mul_nonneg (show 0≤q by omega) (show 0≤z-4 by omega)
      have tx : 2*(t:ℤ)≤x := by rw [xs,hsq]; nlinarith only [hm,htq]
      exact_mod_cast (show (t:ℤ)≤(2^(a-1):ℕ) by omega)
  have zeven : ∃ z0 : ℤ, z=2*z0 := by
    refine ⟨2^(c-1),?_⟩
    dsimp [z]
    calc
      (2:ℤ)^c=2^((c-1)+1) := congrArg (fun n : ℕ => (2:ℤ)^n) (by omega)
      _ = 2*2^(c-1) := by rw [pow_succ]; ring
  have wr:=lower_windows s z h r t hs hz hh zeven ht hhd (by exact_mod_cast hr)
    (by simpa [xs,yh,mul_assoc] using hceil)
  have wx : (s:ℤ)*z=x := xs.symm
  have wy : 2*(s:ℤ)*z*h=y := by calc
    2*(s:ℤ)*z*h=2*((s:ℤ)*z)*h := by ring
    _=y := by rw [←xs]; exact yh.symm
  simp only [wx,wy] at wr
  have sceq : ((s:ℤ)=2) ↔ s=2 := by omega
  simp only [sceq] at wr
  let U:=mask a b c a 0
  let V:=mask a b c a 1
  let W:=mask a b c a 2
  let X:=mask a b c a 3
  let paid:=t-1
  let P0:=X (full a b c a 3)
  let P1:=U (full a b c a 0 ^^^ paid)++(if s=2 then W r else [])
  let P2:=U paid++V (full a b c a 1)++(if s=2 then [] else W r)
  let P3:=W (full a b c a 2 ^^^ r)
  let n:=terminal a b c a
  let bs : List (List ℕ×ℕ):=[(P0,n 2),(P1,n 0),(P2,n 3),(P3,n 1)]
  have paidcap : paid<2^(chainLength a b c a 0-1) := by simpa [paid,chainLength] using (show t-1<2^(a-1) by omega)
  have rrCap : r<2^(chainLength a b c a 2-1) := by simpa [chainLength] using rcap
  have hp : (blocksWord bs).Perm (List.range (size a b c a)) := by
    have hu:=Multiset.coe_eq_coe.mpr (full_split a b c a 0 paid)
    have hw:=Multiset.coe_eq_coe.mpr (full_split a b c a 2 r)
    apply Multiset.coe_eq_coe.mp
    rw [←chain_inventory a b c a ha hb hc ha]
    simp only [←Multiset.coe_add,Multiset.coe_singleton] at hu hw ⊢
    dsimp [bs,blocksWord,P0,P1,P2,P3,U,V,W,X,n]
    split_ifs
    all_goals simp only [←Multiset.coe_add,Multiset.coe_nil,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton,zero_add,add_zero]
    all_goals rw [←hu,←hw]
    all_goals ac_rfl
  have hpos : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤oldValue a b c a i ∧ 0≤newValue a b c a i := by
    have pos (r : Fin 4) (m i : ℕ) (hi : i∈mask a b c a r m) :=
      mask_positive a b c a m r ha hb hc ha i hi
    intro pkt hpk i hi
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals dsimp [P0,P1,P2,P3,U,V,W,X] at hi
    all_goals try split_ifs at hi
    all_goals try simp only [List.append_nil,List.nil_append,List.mem_append,List.not_mem_nil,or_false,false_or] at hi
    all_goals
      repeat' first
        | exact pos 0 _ _ hi
        | exact pos 1 _ _ hi
        | exact pos 2 _ _ hi
        | exact pos 3 _ _ hi
        | rcases hi with hi|hi
  have hneg : ∀ pkt∈bs, oldValue a b c a pkt.2≤0 ∧ newValue a b c a pkt.2≤0 := by
    intro pkt hpk
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals exact terminal_nonpositive a b c a _ ha hb hc ha
  have ds:=dictionary a b c
  have win (side : Bool) :
      let F:=if side then newBase a b c a else base a b c a
      let E:=if side then base a b c a 0 else 0
      let u : ℤ:=if s=2 then r else 0
      (0≤base a b c a 0-F 3+2*E ∧ base a b c a 0-F 3+2*E≤F 3-1) ∧
      (0≤base a b c a 0-F 3+2*E+2*F 1-2*(t:ℤ)*F 0+2*u*F 2 ∧
        base a b c a 0-F 3+2*E+2*F 1-2*(t:ℤ)*F 0+2*u*F 2≤F 1-1) ∧
      (0≤(2*(r:ℤ)+1)*F 2-F 3 ∧ (2*(r:ℤ)+1)*F 2-F 3≤base a b c a 0-1) ∧ 1≤F 2 := by
    have hx : 4≤x := by simpa [x] using pow_lower a 2 ha
    have hy4 : 4≤y := by simpa [y] using pow_lower b 2 hb
    have head:=heads_positive x y z hx hy4 hz
    cases side
    · simpa [ds.1,x,y,z] using
        And.intro wr.1 (And.intro wr.2.2.1 (And.intro wr.2.2.2.2.1 head.2.2.1))
    · have w:=And.intro wr.2.1
        (And.intro wr.2.2.2.1 (And.intro wr.2.2.2.2.2 head.2.2.2.2.2.1))
      simp [ds.1,ds.2,x,y,z] at w ⊢
      rcases w with ⟨w0,w1,w2,w3⟩
      refine ⟨?_,?_,?_,w3⟩
      all_goals constructor <;> nlinarith only [w0.1,w0.2,w1.1,w1.2,w2.1,w2.2]
  have checks (side : Bool) :
      packetChecks (if side then newValue a b c a else oldValue a b c a)
        (if side then sourceMod a b c a else sourceMod a b c a/2) 0
        (if side then marked (size a b c a) true 0 bs else bs) := by
    let f:=if side then newValue a b c a else oldValue a b c a
    let F:=if side then newBase a b c a else base a b c a
    let E:=if side then base a b c a 0 else 0
    let C:=if side then sourceMod a b c a else sourceMod a b c a/2
    let J:=if side then nextNewBase a b c a else nextBase a b c a
    let u : ℤ:=if s=2 then r else 0
    let Q0:=if side then size a b c a::P0 else P0
    have start : F 0=base a b c a 0+E := by cases side <;> dsimp [F,E,newBase,charge] <;> ring
    have sm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a j-1)) :
        ((mask a b c a j m).map f).sum=(m:ℤ)*F j := by
      have hh:=mask_mass a b c a m j ha hb hc ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have cm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a j-1)) :
        ((mask a b c a j (full a b c a j ^^^ m)).map f).sum=
          (full a b c a j:ℤ)*F j-(m:ℤ)*F j := by
      have hh:=complement_mass a b c a m j ha hb hc ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have pc : (paid:ℤ)=(t:ℤ)-1 := by dsimp [paid]; omega
    have mass0 : (Q0.map f).sum=(full a b c a 3:ℤ)*F 3+E := by
      cases side
      · simpa [Q0,E] using sm 3 _ (full_cap a b c 3)
      · have fresh:=(chain_values a b c a ha hb hc ha).2.2.2
        simp only [Q0,ite_true,List.map_cons,List.sum_cons]
        rw [sm 3 _ (full_cap a b c 3)]
        have hfresh : f (size a b c a)=E := by simpa only [f,E,ite_true] using fresh
        rw [hfresh]
        dsimp [E]
        ring
    have mass1 : (P1.map f).sum=((full a b c a 0:ℤ)-((t:ℤ)-1))*F 0+u*F 2 := by
      dsimp [P1,u]
      split_ifs
      all_goals simp only [List.map_append,List.sum_append,List.map_nil,List.sum_nil]
      all_goals rw [cm 0 paid paidcap,pc]
      · rw [sm 2 r rrCap]; ring
      · ring
    have mass2 : (P2.map f).sum=((t:ℤ)-1)*F 0+(full a b c a 1:ℤ)*F 1+((r:ℤ)-u)*F 2 := by
      dsimp [P2,u]
      split_ifs
      all_goals simp only [List.map_append,List.sum_append,List.map_nil,List.sum_nil]
      all_goals rw [sm 0 paid paidcap,sm 1 _ (full_cap a b c 1),pc]
      · ring
      · rw [sm 2 r rrCap]; ring
    have mass3:=cm 2 r rrCap
    have nb (j : Fin 4) : (full a b c a j:ℤ)*F j+f (n j)=J j-F j := by
      have hh:=native_balance a b c a j ha hb hc ha
      cases side <;> first | exact hh.1 | exact hh.2
    have nt (j : Fin 4) : 2*f (n j)=J j-(2*C+1) := by
      have hh:=terminal_double a b c a j ha hb hc ha
      have odd:=source_odd a b c a (by omega)
      cases side
      · have hn : sourceMod a b c a=2*(sourceMod a b c a/2)+1 := by omega
        simpa only [f,J,C,ite_false,Bool.false_eq_true,←hn] using hh.1
      · exact hh.2
    have j0 : J 0=F 1 := by cases side <;> rfl
    have j1 : J 1=F 2 := by cases side <;> rfl
    have j2 : J 2=F 3 := by cases side <;> rfl
    have j3 : J 3=base a b c a 0 := by cases side <;> rfl
    have nb0:=nb 0
    have nb1:=nb 1
    have nb2:=nb 2
    have nb3:=nb 3
    have nt0:=nt 0
    have nt1:=nt 1
    have nt2:=nt 2
    have nt3:=nt 3
    rw [j0] at nb0 nt0
    rw [j1] at nb1 nt1
    rw [j2] at nb2 nt2
    rw [j3] at nb3 nt3
    have wz:=win side
    have zero : ((blocksWord [(Q0,n 2),(P1,n 0),(P2,n 3),(P3,n 1)]).map f).sum=0 := by
      cases side
      · exact ((hp.map (oldValue a b c a)).sum_eq).trans (source_totals a b c a ha hb hc ha).1
      · simpa [bs,marked,Q0,freshAfter,f,C] using
          marked_total a b c ha hb hc true 0 bs (by simp [bs]) hp
    have chk:=four_checks f C Q0 P1 P2 P3 (n 2) (n 0) (n 3) (n 1)
      (base a b c a 0-F 3+2*E)
      (base a b c a 0-F 3+2*E+2*F 1-2*(t:ℤ)*F 0+2*u*F 2)
      ((2*(r:ℤ)+1)*F 2-F 3) (F 3) (F 1) (base a b c a 0) (F 2)
      (by nlinarith only [mass0,nb3,nt2,nt3])
      (by nlinarith only [mass0,mass1,nb3,nb0,nt2,nt3])
      (by nlinarith only [mass0,mass1,mass2,nb3,nb0,nb1,nt2,nt3,nt1,start])
      zero nt2 nt0 nt3 nt1 wz.1 wz.2.1 wz.2.2.1 wz.2.2.2
    cases side <;> simpa [bs,marked,Q0,freshAfter,f,C] using chk
  exact realize_packets a b c ha hb hc true 0 bs (by simp [bs]) hp hpos hneg (checks false) (checks true)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
