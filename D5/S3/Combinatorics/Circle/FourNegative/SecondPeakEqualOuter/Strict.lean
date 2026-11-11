/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Strict
   generality: I
   mirror-B: none(waiver:private-sector-consumed-by-whole-face)
   mirror-E: none(waiver:private-sector-consumed-by-whole-face)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: All five strict W-X-U-V physical branches at the original seed. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.StrictArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical

/-! All five strict W-X-U-V physical branches at the original seed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open SecondPeakHighD (Submask submask_le submask_predecessor bit_below)
open PacketNormalForm (size base newBase oldValue newValue chainLength chainStart blocksWord)
open private sourceMod
  source_totals chain_values nextBase nextNewBase charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private mask full terminal full_split sub_split chain_inventory mask_mass mask_positive
  complement_mass split_mass terminal_double terminal_nonpositive source_odd native_balance
  four_checks mask_numeric_split
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
open private packetChecks withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private A B L H K SU SV SW heads_positive dictionary pow_split pow_lower full_cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source
open private marked marked_total realize_packets
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical
open private scalar_floor strict_first_windows strict_payment
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.StrictArithmetic

set_option maxHeartbeats 2400000 in
private theorem strict_selectors (a b c : ℕ) (ha : 2≤a) (hac : a<c) (hcb : c<b) :
    let x : ℤ:=2^a
    let z : ℤ:=2^c
    let y : ℤ:=2^b
    let s : ℕ:=3*2^(b-a-2)
    ∃ v t : ℕ, 1≤v ∧ v≤4 ∧ v≤2^(c-1) ∧ 1≤t ∧ t≤s ∧
      s≤2^(b-1) ∧ Submask (t-1) (s-1) ∧
      ((∃ p : ℤ, 2≤p ∧ z=2*x ∧ y=2*p*x ∧ (v:ℤ)=2 ∧ 2*(t:ℤ)=3*p) ∨
      (∃ p : ℤ, 4≤p ∧ y=p*z ∧ (v:ℤ)=1 ∧ (t:ℤ)=B x y/L x z) ∨
      (y=2*z ∧ (v:ℤ)=2 ∧ (t:ℤ)=3) ∨
      (x=4 ∧ z=16 ∧ y=32 ∧ (v:ℤ)=4 ∧ (t:ℤ)=6) ∨
      (8≤x ∧ y=2*z ∧ (v:ℤ)=3 ∧ (t:ℤ)=5)) := by
  let x : ℤ:=2^a
  let z : ℤ:=2^c
  let y : ℤ:=2^b
  let r : ℕ:=2^(b-a-2)
  let s : ℕ:=3*r
  change ∃ v t : ℕ, 1≤v ∧ v≤4 ∧ v≤2^(c-1) ∧ 1≤t ∧ t≤s ∧
      s≤2^(b-1) ∧ Submask (t-1) (s-1) ∧
      ((∃ p : ℤ, 2≤p ∧ z=2*x ∧ y=2*p*x ∧ (v:ℤ)=2 ∧ 2*(t:ℤ)=3*p) ∨
      (∃ p : ℤ, 4≤p ∧ y=p*z ∧ (v:ℤ)=1 ∧ (t:ℤ)=B x y/L x z) ∨
      (y=2*z ∧ (v:ℤ)=2 ∧ (t:ℤ)=3) ∨
      (x=4 ∧ z=16 ∧ y=32 ∧ (v:ℤ)=4 ∧ (t:ℤ)=6) ∨
      (8≤x ∧ y=2*z ∧ (v:ℤ)=3 ∧ (t:ℤ)=5))
  have hx : 4≤x := by simpa [x] using pow_lower a 2 ha
  have hz : 8≤z := by simpa [z] using pow_lower c 3 (by omega)
  have hx0 : 0≤x := by omega
  have hr : 1≤r := Nat.one_le_two_pow
  have hy : y=4*x*r := by
    dsimp [y,x,r]
    push_cast
    calc
      (2:ℤ)^b=2^(a+(b-a-2)+2) := congrArg (fun n : ℕ => (2:ℤ)^n) (by omega)
      _ = 4*2^a*2^(b-a-2) := by rw [pow_add,pow_add]; norm_num; ring
  have hw : (2^(b-1):ℕ)=2*(2^a)*r := by
    dsimp [r]
    calc
      (2:ℕ)^(b-1)=2^(a+(b-a-2)+1) := congrArg (fun n : ℕ => (2:ℕ)^n) (by omega)
      _ = 2*2^a*2^(b-a-2) := by rw [pow_add,pow_add]; norm_num; ring
  have hxN : 4≤(2:ℕ)^a := by exact_mod_cast (show (4:ℤ)≤(2:ℤ)^a from hx)
  have hscap : s≤2^(b-1) := by dsimp [s]; rw [hw]; nlinarith only [hr,hxN]
  have hvcap : 4≤(2:ℕ)^(c-1) := by
    change (2:ℕ)^2≤2^(c-1)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sub (t : ℕ) (ht : t-1<r) : Submask (t-1) (s-1) := by
    simpa [s,r,Nat.mul_comm] using submask_predecessor (b-a-2) 3 (t-1) (by decide) ht
  by_cases hq2 : c=a+1
  · have hz2 : z=2*x := by dsimp [z,x]; rw [hq2,pow_succ]; ring
    let p : ℤ:=2^(b-c)
    have hp : 2≤p := by simpa [p] using pow_lower (b-c) 1 (by omega)
    have yp : y=2*p*x := by rw [show y=2^(b-c)*z from pow_split b c (by omega),hz2]; dsimp [p]; ring
    have ht : 2*(s:ℤ)=3*p := by
      have he : b-c=(b-a-2)+1 := by omega
      dsimp [s,r,p]
      push_cast
      rw [he,pow_succ]
      ring
    refine ⟨2,s,by decide,by decide,by omega,by dsimp [s]; omega,le_rfl,hscap,?_,?_⟩
    · exact fun _ h => h
    · exact Or.inl ⟨p,hp,hz2,yp,rfl,ht⟩
  · by_cases hp4 : c+2≤b
    · let p : ℤ:=2^(b-c)
      have hp : 4≤p := by simpa [p] using pow_lower (b-c) 2 (by omega)
      have yp : y=p*z := pow_split b c (by omega)
      have z4 : 4*x≤z := by
        have hh:=pow_lower (c-a) 2 (by omega)
        have he:=pow_split c a (by omega)
        dsimp [z,x] at *
        nlinarith only [hh,he,mul_nonneg (show 0≤(2:ℤ)^(c-a)-4 by omega) (show 0≤(2:ℤ)^a by positivity)]
      have hz0 : 0≤z := by omega
      have hL : 0<L x z := by dsimp [L]; positivity
      have c0 : 0<p*L x z-B x y := by
        rw [yp]
        let u:=x-4
        let w:=z-4*x
        let h:=p-4
        have hu : 0≤u := by dsimp [u]; omega
        have hw : 0≤w := by dsimp [w]; omega
        have hh : 0≤h := by dsimp [h]; omega
        have ex : x=u+4 := by dsimp [u]; ring
        have ez : z=4*(u+4)+w := by dsimp [u,w]; ring
        have ep : p=h+4 := by dsimp [h]; ring
        rw [ex,ez,ep]; dsimp [L,B]; ring_nf; positivity
      have c1 : 0<B x y-2*L x z-p*(z+1) := by
        rw [yp]
        let u:=x-4
        let w:=z-4*x
        let h:=p-4
        have hu : 0≤u := by dsimp [u]; omega
        have hw : 0≤w := by dsimp [w]; omega
        have hh : 0≤h := by dsimp [h]; omega
        have ex : x=u+4 := by dsimp [u]; ring
        have ez : z=4*(u+4)+w := by dsimp [u,w]; ring
        have ep : p=h+4 := by dsimp [h]; ring
        rw [ex,ez,ep]; dsimp [L,B]; ring_nf; positivity
      let ti:=B x y/L x z
      have hf:=scalar_floor (B x y) (L x z) hL
      have ht2 : 2≤ti := by
        by_contra hn
        have hm:=mul_le_mul_of_nonneg_right (show ti≤1 by omega) hL.le
        have hc:=mul_nonneg (show 0≤p by omega) (show 0≤z+1 by omega)
        dsimp [ti] at hm
        nlinarith only [hm,hf.2,c1,hc]
      have htp : ti<p := by
        by_contra hn
        have hm:=mul_le_mul_of_nonneg_right (show p≤ti by omega) hL.le
        dsimp [ti] at hm
        nlinarith only [hm,hf.1,c0]
      let t:=ti.toNat
      have htcast : (t:ℤ)=ti := Int.toNat_of_nonneg (by omega)
      have hpr : p≤r := by
        have he : b-c≤b-a-2 := by omega
        dsimp [p,r]
        exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) he)
      have htr : t<r := by omega
      refine ⟨1,t,by decide,by decide,by omega,by omega,by dsimp [s]; omega,hscap,sub t (by omega),?_⟩
      exact Or.inr (Or.inl ⟨p,hp,yp,rfl,htcast⟩)
    · have hb1 : b=c+1 := by omega
      have yz : y=2*z := by dsimp [y,z]; rw [hb1,pow_succ]; ring
      by_cases hq8 : a+3≤c
      · have hr4 : 4≤r := by
          change (2:ℕ)^2≤2^(b-a-2)
          exact Nat.pow_le_pow_right (by decide) (by omega)
        refine ⟨2,3,by decide,by decide,by omega,by decide,by dsimp [s]; omega,hscap,sub 3 (by omega),?_⟩
        exact Or.inr (Or.inr (Or.inl ⟨yz,rfl,rfl⟩))
      · have hc2 : c=a+2 := by omega
        have hr2 : r=2 := by dsimp [r]; rw [show b-a-2=1 by omega]; norm_num
        have hs6 : s=6 := by dsimp [s]; rw [hr2]
        by_cases ha2 : a=2
        · refine ⟨4,6,by decide,by decide,by omega,by decide,by omega,hscap,?_,?_⟩
          · rw [hs6]; exact fun _ h => h
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp [x]; rw [ha2]; norm_num,
              by dsimp [z]; rw [hc2,ha2]; norm_num,
              by dsimp [y]; rw [hb1,hc2,ha2]; norm_num,rfl,rfl⟩)))
        · have hx8 : 8≤x := by simpa [x] using pow_lower a 3 (by omega)
          refine ⟨3,5,by decide,by decide,by omega,by decide,by omega,hscap,?_,?_⟩
          · rw [hs6]
            exact SecondPeakHighD.submask_of_land 4 5 (by decide)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx8,yz,rfl,rfl⟩)))

set_option maxHeartbeats 2400000 in
private theorem strict_lift (a b c : ℕ) (ha : 2≤a) (hac : a<c) (hcb : c<b) :
    ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j≤a+b+c+a ∧
      OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+a) sigma j) := by
  have hb : 2≤b := by omega
  have hc : 2≤c := by omega
  let x : ℤ:=2^a
  let z : ℤ:=2^c
  let y : ℤ:=2^b
  let r : ℕ:=2^(b-a-2)
  let s : ℕ:=3*r
  obtain ⟨v,t,hv0,hv4,hv,ht0,hts,hsc,hsub,hbranch⟩ := strict_selectors a b c ha hac hcb
  let M:=s-1
  let T:=t-1
  let w:=mask a b c a 2
  let u:=mask a b c a 0
  let vv:=mask a b c a 1
  let xx:=mask a b c a 3
  let P0:=w (full a b c a 2 ^^^ M)
  let P1:=xx (full a b c a 3)
  let P2:=u (full a b c a 0)++vv (v-1)++w (M ^^^ T)
  let P3:=vv (full a b c a 1 ^^^ (v-1))++w T
  let n:=terminal a b c a
  let bs : List (List ℕ×ℕ):=[(P0,n 2),(P1,n 3),(P2,n 0),(P3,n 1)]
  have hM : M<2^(chainLength a b c a 2-1) := by
    have hs0 : 1≤s := by dsimp [s,r]; have := Nat.one_le_two_pow (n:=b-a-2); omega
    simpa [chainLength,M] using (show s-1<2^(b-1) by omega)
  have hT : T<2^(chainLength a b c a 2-1) := by
    have hle:=submask_le T M hsub
    omega
  have hvC : v-1<2^(chainLength a b c a 1-1) := by simpa [chainLength] using (show v-1<2^(c-1) by omega)
  have hw0:=full_split a b c a 2 M
  have hw1:=sub_split a b c a 2 M T hsub
  have hv0':=full_split a b c a 1 (v-1)
  have hw : (P0++w (M ^^^ T)++w T).Perm (w (full a b c a 2)) := by
    simpa [P0,w,List.append_assoc] using (hw1.append_left P0).trans hw0
  have hp : (blocksWord bs).Perm (List.range (size a b c a)) := by
    have ew:=Multiset.coe_eq_coe.mpr hw
    have ev:=Multiset.coe_eq_coe.mpr hv0'
    apply Multiset.coe_eq_coe.mp
    rw [←chain_inventory a b c a ha hb hc ha]
    simp only [←Multiset.coe_add,Multiset.coe_singleton] at ew ev ⊢
    dsimp [bs,blocksWord,P0,P1,P2,P3,w,u,vv,xx,n] at *
    simp only [←Multiset.coe_add,Multiset.coe_nil,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton,zero_add,add_zero] at *
    rw [←ew,←ev]
    ac_rfl
  have hpos : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤oldValue a b c a i ∧ 0≤newValue a b c a i := by
    have pos (r : Fin 4) (m i : ℕ) (hi : i∈mask a b c a r m) :=
      mask_positive a b c a m r ha hb hc ha i hi
    intro pkt hpk i hi
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals dsimp [P0,P1,P2,P3,w,u,vv,xx] at hi
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
  have hx : 4≤x := by simpa [x] using pow_lower a 2 ha
  have hz : 2*x≤z := by
    have he:=pow_split c a (by omega)
    have hh:=pow_lower (c-a) 1 (by omega)
    dsimp [x,z] at *
    nlinarith only [he,mul_nonneg (show 0≤(2:ℤ)^(c-a)-2 by omega) (show 0≤(2:ℤ)^a by positivity)]
  have hr : (1:ℤ)≤r := by exact_mod_cast (Nat.one_le_two_pow (n:=b-a-2))
  have hy : y=4*x*r := by
    dsimp [x,y,r]
    push_cast
    calc
      (2:ℤ)^b=2^(a+(b-a-2)+2) := congrArg (fun n : ℕ => (2:ℤ)^n) (by omega)
      _ = 4*2^a*2^(b-a-2) := by rw [pow_add,pow_add]; norm_num; ring
  have wf:=strict_first_windows x z r hx hz hr
  have wu:=strict_payment x z y v t hx hz ⟨by exact_mod_cast hv0,by exact_mod_cast hv4⟩
    (by exact_mod_cast ht0) hbranch
  rw [←hy] at wf
  have ds:=dictionary a b c
  have win (side : Bool) :
      let F:=if side then newBase a b c a else base a b c a
      (0≤2*(F 3-(s:ℤ)*F 2) ∧ 2*(F 3-(s:ℤ)*F 2)≤F 3-1) ∧
      (0≤2*(F 0-(s:ℤ)*F 2) ∧ 2*(F 0-(s:ℤ)*F 2)≤base a b c a 0-1) ∧
      (0≤2*((v:ℤ)*F 1-(t:ℤ)*F 2) ∧ 2*((v:ℤ)*F 1-(t:ℤ)*F 2)≤F 1-1) ∧ 1≤F 2 := by
    have head:=heads_positive x y z hx (by have := pow_lower b 2 hb; simpa [y] using this)
      (by omega)
    cases side
    · simpa [s,ds.1,x,y,z] using And.intro wf.1 (And.intro wf.2.2.1 (And.intro wu.1 head.2.2.1))
    · simpa [s,ds.1,ds.2,x,y,z] using And.intro wf.2.1 (And.intro wf.2.2.2 (And.intro wu.2 head.2.2.2.2.2.1))
  have checks (side : Bool) :
      packetChecks (if side then newValue a b c a else oldValue a b c a)
        (if side then sourceMod a b c a else sourceMod a b c a/2) 0
        (if side then marked (size a b c a) false 1 bs else bs) := by
    let f:=if side then newValue a b c a else oldValue a b c a
    let F:=if side then newBase a b c a else base a b c a
    let E:=if side then base a b c a 0 else 0
    let C:=if side then sourceMod a b c a else sourceMod a b c a/2
    let Q1:=if side then P1++[size a b c a] else P1
    have start : F 0=base a b c a 0+E := by
      cases side <;> dsimp [F,E,newBase,charge] <;> ring
    have sm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a j-1)) :
        ((mask a b c a j m).map f).sum=(m:ℤ)*F j := by
      have hh:=mask_mass a b c a m j ha hb hc ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have cm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a j-1)) :
        ((mask a b c a j (full a b c a j ^^^ m)).map f).sum=
          (full a b c a j:ℤ)*F j-(m:ℤ)*F j := by
      have hh:=complement_mass a b c a m j ha hb hc ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have dm : ((w (M ^^^ T)).map f).sum=((M:ℤ)-(T:ℤ))*F 2 := by
      have hh:=((hw1.map f).sum_eq)
      simp only [List.map_append,List.sum_append] at hh
      rw [sm 2 M hM,sm 2 T hT] at hh
      linarith only [hh]
    have mass0:=cm 2 M hM
    have mass1 : (Q1.map f).sum=(full a b c a 3:ℤ)*F 3+E := by
      cases side
      · simpa [Q1,E] using sm 3 _ (full_cap a b c 3)
      · have fresh:=(chain_values a b c a ha hb hc ha).2.2.2
        simp only [Q1,ite_true,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
        rw [sm 3 _ (full_cap a b c 3)]
        have hfresh : f (size a b c a)=E := by simpa only [f,E,ite_true] using fresh
        rw [hfresh]
    have mass2 : (P2.map f).sum=(full a b c a 0:ℤ)*F 0+((v:ℤ)-1)*F 1+((s:ℤ)-(t:ℤ))*F 2 := by
      have mt : (M:ℤ)-(T:ℤ)=(s:ℤ)-(t:ℤ) := by dsimp [M,T]; omega
      simp only [P2,List.map_append,List.sum_append]
      have tv : ((v-1:ℕ):ℤ)=(v:ℤ)-1 := by omega
      rw [sm 0 _ (full_cap a b c 0),sm 1 (v-1) hvC,dm,mt,tv]
    have mass3 : (P3.map f).sum=((full a b c a 1:ℤ)-((v:ℤ)-1))*F 1+((t:ℤ)-1)*F 2 := by
      simp only [P3,List.map_append,List.sum_append]
      rw [cm 1 (v-1) hvC,sm 2 T hT]
      have tv : ((v-1:ℕ):ℤ)=(v:ℤ)-1 := by omega
      have tt : (T:ℤ)=(t:ℤ)-1 := by dsimp [T]; omega
      rw [tv,tt]
      ring
    let J:=if side then nextNewBase a b c a else nextBase a b c a
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
    have zero : ((blocksWord [(P0,n 2),(Q1,n 3),(P2,n 0),(P3,n 1)]).map f).sum=0 := by
      cases side
      · have hz:=((hp.map (oldValue a b c a)).sum_eq).trans (source_totals a b c a ha hb hc ha).1
        exact hz
      · simpa [bs,marked,Q1,withEar,f,C] using marked_total a b c ha hb hc false 1 bs (by simp [bs]) hp
    have mcast : (M:ℤ)=(s:ℤ)-1 := by
      have hs0 : 1≤s := by
        have hr0 : 1≤r := Nat.one_le_two_pow
        dsimp [s]; omega
      dsimp only [M]
      omega
    rw [mcast] at mass0
    have chk:=four_checks f C P0 Q1 P2 P3 (n 2) (n 3) (n 0) (n 1)
      (2*(F 3-(s:ℤ)*F 2)) (2*(F 0-(s:ℤ)*F 2))
      (2*((v:ℤ)*F 1-(t:ℤ)*F 2)) (F 3) (base a b c a 0) (F 1) (F 2)
      (by nlinarith only [mass0,nb2])
      (by nlinarith only [mass0,mass1,nb2,nb3,start])
      (by nlinarith only [mass0,mass1,mass2,nb2,nb3,nb0,start])
      zero nt2 nt3 nt0 nt1 wz.1 wz.2.1 wz.2.2.1 wz.2.2.2
    cases side <;> simpa [bs,marked,Q1,withEar,f,C] using chk
  exact realize_packets a b c ha hb hc false 1 bs (by simp [bs]) hp hpos hneg (checks false) (checks true)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
