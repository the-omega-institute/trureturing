/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Palindromic
   generality: I
   mirror-B: none(waiver:private-sector-consumed-by-whole-face)
   mirror-E: none(waiver:private-sector-consumed-by-whole-face)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Nested palindromic W masks and one literal U0/X0 transposition. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.PalindromicMasks
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical

/-! Nested palindromic W masks and one literal U0/X0 transposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open SecondPeakHighD (Submask)
open PacketNormalForm (size base newBase oldValue newValue chainLength chainStart blocksWord)
open private sourceMod charge
  source_totals chain_values nextBase nextNewBase
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private mask full terminal full_split sub_split chain_inventory mask_mass mask_positive complement_mass
  terminal_double terminal_nonpositive source_odd native_balance four_checks
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
open private packetChecks withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private A B L H K SU SV SW heads_positive dictionary pow_split pow_lower full_cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source
open private marked marked_total realize_packets
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Physical
open private palin_r1 palin_t palin_r2 palin_choices
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.PalindromicMasks
open private palin_windows
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.PalindromicArithmetic

set_option maxHeartbeats 3000000 in
private theorem palindromic_lift (a b : ℕ) (ha : 2≤a) (hab : a+2≤b) :
    ∃ sigma : List (Fin (a+b+b+a)), ∃ j : ℕ, j≤a+b+b+a ∧
      OriginalOrder (a+b+b+a) (1+2^a+2^(a+b)+2^(a+b+b)) sigma ∧
      OriginalOrder (a+b+b+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+b)))
        (earWord (a+b+b+a) sigma j) := by
  have hb : 2≤b := by omega
  let x : ℤ:=2^a
  let q : ℤ:=2^(b-a)
  let y : ℤ:=2^b
  have yh : y=q*x := pow_split b a (by omega)
  let r1:=palin_r1 x q
  let t:=palin_t x q
  let r2:=palin_r2 x q
  let high:=2^(b-a)*(2^(a-1)-1)
  let M1:=high+r1
  let M2:=high+r2
  let s1:=q-r1
  let s2:=q-r2
  let exceptional : Prop:=x=4 ∧ q=8
  let ep0:=SV x y-SU x y+SW x y y-s1*SV x y
  let e : Fin 4:=if ep0<0 then 1 else 2
  obtain ⟨hr1,ht,hr,hE,hF,hqd,hxd,hex,hM1,hM2,hsub,m1,m2⟩:=palin_choices a b ha hab
  have hx : 4≤x := by simpa [x] using pow_lower a 2 ha
  have hq : 4≤q := by simpa [q] using pow_lower (b-a) 2 (by omega)
  have windows:=palin_windows x q r1 t r2 hx hq hr1 ht hr hE hF hqd hxd
    (by intro hx4 hq8; obtain ⟨h1,h2,h3⟩:=hex hx4 hq8; exact ⟨by exact_mod_cast h1,by exact_mod_cast h2,by exact_mod_cast h3⟩)
  rw [←yh] at windows
  let U:=mask a b b a 0
  let V:=mask a b b a 1
  let W:=mask a b b a 2
  let X:=mask a b b a 3
  let P0:=V (full a b b a 1)
  let P1:=W M1
  -- This exchanges the actual first U and X labels, each exactly once.
  let PX:=if exceptional then U 1++X (full a b b a 3 ^^^ 1) else X (full a b b a 3)
  let PU:=if exceptional then X 1++U (full a b b a 0 ^^^ 1) else U (full a b b a 0)
  let P2:=PX++W (M2 ^^^ M1)
  let P3:=PU++W (full a b b a 2 ^^^ M2)
  let n:=terminal a b b a
  let bs : List (List ℕ×ℕ):=[(P0,n 1),(P1,n 2),(P2,n 3),(P3,n 0)]
  have cap1 : M1<2^(chainLength a b b a 2-1) := by simpa [chainLength] using hM1
  have cap2 : M2<2^(chainLength a b b a 2-1) := by simpa [chainLength] using hM2
  have capOne (j : Fin 4) : 1<2^(chainLength a b b a j-1) := by
    fin_cases j <;> dsimp [chainLength]
    all_goals first
      | exact lt_of_lt_of_le (by decide : 1<(2:ℕ)^1) (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : (blocksWord bs).Perm (List.range (size a b b a)) := by
    have hw1:=sub_split a b b a 2 M2 M1 hsub
    have hw2:=full_split a b b a 2 M2
    have hw : (W M1++W (M2 ^^^ M1)++W (full a b b a 2 ^^^ M2)).Perm
        (W (full a b b a 2)) := by
      apply Multiset.coe_eq_coe.mp
      have hh1:=Multiset.coe_eq_coe.mpr hw1
      have hh2:=Multiset.coe_eq_coe.mpr hw2
      simp only [←Multiset.coe_add] at hh1 hh2 ⊢
      calc
        _ = (↑(W (full a b b a 2 ^^^ M2)) : Multiset ℕ)+(↑(W (M2 ^^^ M1))+↑(W M1)) := by ac_rfl
        _ = _ := by rw [hh1,hh2]
    have hu:=Multiset.coe_eq_coe.mpr (full_split a b b a 0 1)
    have hx':=Multiset.coe_eq_coe.mpr (full_split a b b a 3 1)
    have hw':=Multiset.coe_eq_coe.mpr hw
    apply Multiset.coe_eq_coe.mp
    rw [←chain_inventory a b b a ha hb hb ha]
    simp only [←Multiset.coe_add,Multiset.coe_singleton] at hu hx' hw' ⊢
    dsimp [bs,blocksWord,P0,P1,P2,P3,PX,PU,U,V,W,X,n] at *
    split_ifs
    all_goals simp only [←Multiset.coe_add,Multiset.coe_nil,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton,zero_add,add_zero]
    · rw [←hu,←hx',←hw']
      simp only [←Multiset.coe_add]
      ac_rfl
    · rw [←hw']
      simp only [←Multiset.coe_add]
      ac_rfl
  have hpos : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤oldValue a b b a i ∧ 0≤newValue a b b a i := by
    have pos (r : Fin 4) (m i : ℕ) (hi : i∈mask a b b a r m) :=
      mask_positive a b b a m r ha hb hb ha i hi
    intro pkt hpk i hi
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals dsimp [P0,P1,P2,P3,PX,PU,U,V,W,X] at hi
    all_goals try split_ifs at hi
    all_goals try simp only [List.mem_append] at hi
    all_goals
      repeat' first
        | exact pos 0 _ _ hi
        | exact pos 1 _ _ hi
        | exact pos 2 _ _ hi
        | exact pos 3 _ _ hi
        | rcases hi with hi|hi
  have hneg : ∀ pkt∈bs, oldValue a b b a pkt.2≤0 ∧ newValue a b b a pkt.2≤0 := by
    intro pkt hpk
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals exact terminal_nonpositive a b b a _ ha hb hb ha
  have ds:=dictionary a b b
  have win (side : Bool) :
      let F:=if side then newBase a b b a else base a b b a
      let E:=if side then base a b b a 0 else 0
      let paid:=if ep0<0 then E else 0
      let swap:=if exceptional then F 0-F 3 else 0
      (0≤2*(F 2-F 1) ∧ 2*(F 2-F 1)≤F 2-1) ∧
      (0≤2*(F 2-F 1+F 3-s1*F 2+paid) ∧ 2*(F 2-F 1+F 3-s1*F 2+paid)≤F 3-1) ∧
      (0≤2*(F 2-F 1+F 0-s2*F 2+swap) ∧ 2*(F 2-F 1+F 0-s2*F 2+swap)≤base a b b a 0-1) ∧ 1≤F 1 := by
    have hy4 : 4≤y := by simpa [y] using pow_lower b 2 hb
    have head:=heads_positive x y y hx hy4 hy4
    cases side
    · simpa [ds.1,x,y,s1,s2,exceptional,ep0] using And.intro windows.1
        (And.intro windows.2.2.1 (And.intro windows.2.2.2.2.1 head.2.1))
    · have hp:=And.intro windows.2.1 (And.intro windows.2.2.2.1
        (And.intro windows.2.2.2.2.2 head.2.2.2.2.1))
      by_cases he : ep0<0
      all_goals simpa [ds.1,ds.2,x,y,s1,s2,exceptional,ep0,he,add_assoc] using hp
  have checks (side : Bool) :
      packetChecks (if side then newValue a b b a else oldValue a b b a)
        (if side then sourceMod a b b a else sourceMod a b b a/2) 0
        (if side then marked (size a b b a) false e bs else bs) := by
    let f:=if side then newValue a b b a else oldValue a b b a
    let F:=if side then newBase a b b a else base a b b a
    let E:=if side then base a b b a 0 else 0
    let C:=if side then sourceMod a b b a else sourceMod a b b a/2
    let J:=if side then nextNewBase a b b a else nextBase a b b a
    let swap:=if exceptional then F 0-F 3 else 0
    let pay1:=if ep0<0 then E else 0
    let pay2:=if ep0<0 then 0 else E
    let Q1:=if side ∧ ep0<0 then P1++[size a b b a] else P1
    let Q2:=if side ∧ ¬ep0<0 then P2++[size a b b a] else P2
    have start : F 0=base a b b a 0+E := by cases side <;> dsimp [F,E,newBase,charge] <;> ring
    have pays : pay1+pay2=E := by dsimp [pay1,pay2]; split_ifs <;> ring
    have sm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b b a j-1)) :
        ((mask a b b a j m).map f).sum=(m:ℤ)*F j := by
      have hh:=mask_mass a b b a m j ha hb hb ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have cm (j : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b b a j-1)) :
        ((mask a b b a j (full a b b a j ^^^ m)).map f).sum=
          (full a b b a j:ℤ)*F j-(m:ℤ)*F j := by
      have hh:=complement_mass a b b a m j ha hb hb ha hm
      cases side <;> first | exact hh.1 | exact hh.2
    have dm : ((W (M2 ^^^ M1)).map f).sum=((M2:ℤ)-(M1:ℤ))*F 2 := by
      have hh:=((sub_split a b b a 2 M2 M1 hsub).map f).sum_eq
      simp only [List.map_append,List.sum_append] at hh
      rw [sm 2 M1 cap1,sm 2 M2 cap2] at hh
      linarith only [hh]
    have massX : (PX.map f).sum=(full a b b a 3:ℤ)*F 3+swap := by
      dsimp [PX,swap]
      split_ifs
      · simp only [List.map_append,List.sum_append]
        rw [sm 0 1 (capOne 0),cm 3 1 (capOne 3)]
        ring
      · rw [sm 3 _ (full_cap a b b 3)]; ring
    have massU : (PU.map f).sum=(full a b b a 0:ℤ)*F 0-swap := by
      dsimp [PU,swap]
      split_ifs
      · simp only [List.map_append,List.sum_append]
        rw [sm 3 1 (capOne 3),cm 0 1 (capOne 0)]
        ring
      · rw [sm 0 _ (full_cap a b b 0)]; ring
    have mass0:=sm 1 _ (full_cap a b b 1)
    have mass1 : (Q1.map f).sum=(M1:ℤ)*F 2+pay1 := by
      cases side <;> by_cases he : ep0<0
      all_goals simp only [Q1,pay1,E,he,ite_true,ite_false,Bool.false_eq_true,false_and,true_and,
        List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      all_goals rw [sm 2 M1 cap1]
      all_goals try ring
      simp only [f,ite_true]
      rw [(chain_values a b b a ha hb hb ha).2.2.2]
    have mass2 : (Q2.map f).sum=(full a b b a 3:ℤ)*F 3+swap+((M2:ℤ)-(M1:ℤ))*F 2+pay2 := by
      have mp : (P2.map f).sum=(full a b b a 3:ℤ)*F 3+swap+((M2:ℤ)-(M1:ℤ))*F 2 := by
        simp only [P2,List.map_append,List.sum_append,massX,dm]
      cases side <;> by_cases he : ep0<0
      all_goals simp only [Q2,pay2,E,he,ite_true,ite_false,Bool.false_eq_true,false_and,true_and,
        not_true_eq_false,not_false_eq_true,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      all_goals rw [mp]
      all_goals try ring
      simp only [f,ite_true]
      rw [(chain_values a b b a ha hb hb ha).2.2.2]
    have mass3 : (P3.map f).sum=(full a b b a 0:ℤ)*F 0-swap+((full a b b a 2:ℤ)-(M2:ℤ))*F 2 := by
      simp only [P3,List.map_append,List.sum_append,massU]
      rw [cm 2 M2 cap2]
      ring
    have nb (j : Fin 4) : (full a b b a j:ℤ)*F j+f (n j)=J j-F j := by
      have hh:=native_balance a b b a j ha hb hb ha
      cases side <;> first | exact hh.1 | exact hh.2
    have nt (j : Fin 4) : 2*f (n j)=J j-(2*C+1) := by
      have hh:=terminal_double a b b a j ha hb hb ha
      have odd:=source_odd a b b a (by omega)
      cases side
      · have hn : sourceMod a b b a=2*(sourceMod a b b a/2)+1 := by omega
        simpa only [f,J,C,ite_false,Bool.false_eq_true,←hn] using hh.1
      · exact hh.2
    have j0 : J 0=F 1 := by cases side <;> rfl
    have j1 : J 1=F 2 := by cases side <;> rfl
    have j2 : J 2=F 3 := by cases side <;> rfl
    have j3 : J 3=base a b b a 0 := by cases side <;> rfl
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
    have fullcast : (full a b b a 2:ℤ)=((2^(b-1):ℕ):ℤ)-1 := by
      change (((2^(b-1):ℕ)-1:ℕ):ℤ)=((2^(b-1):ℕ):ℤ)-1
      have hp:=Nat.one_le_two_pow (n:=b-1)
      omega
    have mid1 : (M1:ℤ)=(full a b b a 2:ℤ)+1-s1 := by
      change (M1:ℤ)=((2^(b-1):ℕ):ℤ)-q+r1 at m1
      rw [fullcast]
      dsimp only [s1]
      linarith only [m1]
    have mid2 : (M2:ℤ)=(full a b b a 2:ℤ)+1-s2 := by
      change (M2:ℤ)=((2^(b-1):ℕ):ℤ)-q+r2 at m2
      rw [fullcast]
      dsimp only [s2]
      linarith only [m2]
    have wz:=win side
    have zero : ((blocksWord [(P0,n 1),(Q1,n 2),(Q2,n 3),(P3,n 0)]).map f).sum=0 := by
      cases side
      · simpa [Q1,Q2,f] using ((hp.map (oldValue a b b a)).sum_eq).trans (source_totals a b b a ha hb hb ha).1
      · have hz:=marked_total a b b ha hb hb false e bs (by simp [bs]) hp
        by_cases he : ep0<0
        all_goals simpa [bs,marked,e,Q1,Q2,he,withEar,f,C] using hz
    have chk:=four_checks f C P0 Q1 Q2 P3 (n 1) (n 2) (n 3) (n 0)
      (2*(F 2-F 1)) (2*(F 2-F 1+F 3-s1*F 2+pay1))
      (2*(F 2-F 1+F 0-s2*F 2+swap)) (F 2) (F 3) (base a b b a 0) (F 1)
      (by nlinarith only [mass0,nb1])
      (by nlinarith only [mass0,mass1,nb1,nb2,congrArg (fun z : ℤ => z*F 2) mid1])
      (by nlinarith only [mass0,mass1,mass2,nb1,nb2,nb3,start,pays,
        congrArg (fun z : ℤ => z*F 2) mid1,congrArg (fun z : ℤ => z*F 2) mid2])
      zero nt1 nt2 nt3 nt0 wz.1 wz.2.1 wz.2.2.1 wz.2.2.2
    cases side <;> by_cases he : ep0<0
    all_goals simpa [bs,marked,e,Q1,Q2,he,withEar,f,C] using chk
  exact realize_packets a b b ha hb hb false e bs (by simp [bs]) hp hpos hneg (checks false) (checks true)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
