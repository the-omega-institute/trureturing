/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Allocation
   generality: I
   mirror-B: none(waiver:private-consumed-unbounded-allocation)
   mirror-E: none(waiver:private-consumed-unbounded-allocation)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exhaustive unbounded dyadic allocation on every strict a<b=d<c source. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.SourceCertificate
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Paid
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Rounded
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

/-! Exponent gaps exhaust the charts without finite controls. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private A B L K H SU SV SW window roundedV rounding_bounds outer_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic
open private paidQ paidW paid_first paid_margins paid_third
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Paid
open private roundedW adjacent_middle quadruple_middle separated_middle
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Rounded
open private rowBase rowSeams rowHeads source_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.SourceCertificate
open private charge chain_values new_base_bounds from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (base newBase)
open private gap_power power_split half_power
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic

private theorem mask_bound (u : ℤ) (n : ℕ) (hu : 0≤u) (hn : u<(n:ℤ)) : u.toNat<n := by
  have hh : (u.toNat:ℤ)=u := Int.toNat_of_nonneg hu
  exact_mod_cast (show (u.toNat:ℤ)<(n:ℤ) by rw [hh];exact hn)

set_option maxHeartbeats 2400000 in
private theorem strict_certificate (a b c : ℕ) (ha : 2≤a) (hab : a<b) (hbc : b<c) :
    Nonempty (Certificate a b c b) := by
  let x : ℤ:=2^a
  let y : ℤ:=2^b
  let z : ℤ:=2^c
  let r : ℤ:=2^(b-a-1)
  let m : ℤ:=2^(c-b)
  have hx : 4≤x := by have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha;norm_num at hh;exact hh
  have hr : 1≤r := one_le_pow₀ (by norm_num)
  have hm : 2≤m := by
    have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤c-b by omega)
    norm_num at hh
    exact hh
  have hy : (2:ℤ)*r*x=y := by
    have hh:=gap_power b a 1 (by omega)
    dsimp [r,x,y]
    simpa [mul_comm,mul_left_comm,mul_assoc] using hh.symm
  have hz : m*y=z := by
    dsimp [m,y,z]
    rw [←pow_add]
    congr 1
    omega
  have hypos : 8≤y := by nlinarith only [hy,hx,hr]
  have hhalfA : x=2*((2^(a-1):ℕ):ℤ) := by
    simpa only [x,Nat.cast_pow,Nat.cast_ofNat] using half_power a (by omega)
  have hhalfB : y=2*((2^(b-1):ℕ):ℤ) := by
    simpa only [y,Nat.cast_pow,Nat.cast_ofNat] using half_power b (by omega)
  have hhalfC : z=2*((2^(c-1):ℕ):ℤ) := by
    simpa only [z,Nat.cast_pow,Nat.cast_ofNat] using half_power c (by omega)
  have hmZ : m<((2^(c-1):ℕ):ℤ) := by nlinarith only [hz,hhalfC,hypos,hm]
  have hbase : base a b c b=![A x y z,B x y,L x y z,K y z] := by
    funext j
    fin_cases j <;> dsimp [base,A,B,L,K,x,y,z] <;> ring
  have hnew : newBase a b c b=![2*A x y z,SU x y,SV x y z,SW y z] := by
    funext j
    fin_cases j <;> dsimp [newBase,charge]
    all_goals rw [hbase]
    all_goals dsimp [SU,SV,SW,H,y,z] <;> ring
  have hhead (paid side : Bool) (j : Fin 4) : 1≤rowHeads a b c paid side j := by
    have ho:=(chain_values a b c b ha (by omega) (by omega) (by omega)).1
    have hn:=new_base_bounds a b c b ha (by omega) (by omega) (by omega)
    cases side <;> cases paid <;> fin_cases j
    all_goals first | simpa [rowHeads,rowBase] using (ho 0).1
                    | simpa [rowHeads,rowBase] using (ho 1).1
                    | simpa [rowHeads,rowBase] using (ho 2).1
                    | simpa [rowHeads,rowBase] using (ho 3).1
                    | simpa [rowHeads,rowBase] using (hn 0).1
                    | simpa [rowHeads,rowBase] using (hn 1).1
                    | simpa [rowHeads,rowBase] using (hn 2).1
                    | simpa [rowHeads,rowBase] using (hn 3).1
  by_cases hsmall : c-b≤2
  · have hm4 : m≤4 := by
      have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hsmall
      norm_num at hh
      exact hh
    have hsmall' : 4*m≤2*r*x ∨ r=1 ∧ m≤x := by
      by_cases he : r=1
      · exact Or.inr ⟨he,by omega⟩
      · left
        have hr2 : 2≤r := by omega
        nlinarith only [hr2,hx,hm4]
    have fwin:=paid_first x r m hx hr hm hsmall'
    have mids:=paid_margins x r m hx hr hm
    have twin:=paid_third x r m hx hr hm
    dsimp only at fwin mids twin
    rw [hy,hz] at fwin mids twin
    let vv:=(m-1).toNat
    let ww:=(paidW r).toNat
    let qq:=(paidQ r).toNat
    have hw0 : 0≤paidW r := by dsimp [paidW];split_ifs <;> omega
    have hq0 : 0≤paidQ r := by unfold paidQ;split_ifs <;> omega
    have cv : (vv:ℤ)=m-1 := Int.toNat_of_nonneg (by omega)
    have cw : (ww:ℤ)=paidW r := Int.toNat_of_nonneg hw0
    have cq : (qq:ℤ)=paidQ r := Int.toNat_of_nonneg hq0
    have hwm : paidW r<((2^(b-1):ℕ):ℤ) := by
      unfold paidW
      split_ifs with he
      · have hye:=hy
        rw [he] at hye
        norm_num at hye
        nlinarith only [hye,hhalfB,hx]
      · have hp:=mul_pos (show 0<r by omega) (show 0<x-1 by omega)
        nlinarith only [hy,hhalfB,hp]
    have hqm : paidQ r<((2^(a-1):ℕ):ℤ) := by
      unfold paidQ;split_ifs <;> omega
    apply source_certificate a b c ha hab.le hbc true vv ww qq
      (mask_bound _ _ (by omega) (by omega)) (mask_bound _ _ hw0 hwm) (mask_bound _ _ hq0 hqm)
    intro side j
    have hlast : window (rowSeams a b c true side vv ww qq 3) (rowHeads a b c true side 3) := by
      have hh:=hhead true side 3
      simpa [rowSeams,window] using And.intro (show (0:ℤ)≤0 by omega) hh
    have mo : window (L x y z-A x y z) (L x y z) := ⟨mids.2.2.1.le,by have hh:=mids.2.2.2.2.1;omega⟩
    have mn : window (SV x y z-2*A x y z) (SV x y z) := ⟨mids.2.2.2.1.le,by have hh:=mids.2.2.2.2.2;omega⟩
    cases side <;> fin_cases j
    all_goals first
      | exact hlast
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using fwin.1
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using fwin.2
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using mo
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using mn
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using twin.1
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,cq] using twin.2
  · have hm8 : 8≤m := by
      have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤c-b by omega)
      norm_num at hh
      exact hh
    obtain ⟨hv,hvm,hvB,hvU,hvlo⟩:=rounding_bounds x r m hx hr hm8
    have outer:=outer_windows x r m hx hr hm8
    dsimp only at hv hvm hvB hvU hvlo outer
    rw [hy,hz] at hv hvm hvB hvU hvlo outer
    let v:=roundedV x y z
    have hcases : r=1 ∨ r=2 ∨ 4≤r := by
      by_cases h0 : b-a-1=0
      · left;dsimp [r];rw [h0];norm_num
      · by_cases h1 : b-a-1=1
        · right;left;dsimp [r];rw [h1];norm_num
        · right;right
          have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤b-a-1 by omega)
          norm_num at hh
          exact hh
    obtain ⟨w,hw0,hwy,wo,wn⟩ : ∃ w : ℤ, 0≤w ∧ 2*w≤y-2 ∧
        window (K y z-w*L x y z-v*B x y) (K y z) ∧
        window (SW y z-w*SV x y z+A x y z-v*SU x y) (SW y z) := by
      rcases hcases with he|he|he
      · have hy1 : 2*x=y := by simpa only [he,mul_one] using hy
        have hh:=adjacent_middle x m hx hm8
        dsimp only at hh
        rw [hy1,hz] at hh
        exact ⟨1,by omega,by omega,by simpa using hh.1,by simpa using hh.2⟩
      · have hy2 : 4*x=y := by simpa only [he,show (2:ℤ)*2=4 by norm_num] using hy
        have hh:=quadruple_middle x m hx hm8
        dsimp only at hh
        rw [hy2,hz] at hh
        exact ⟨2,by omega,by omega,by simpa using hh.1,by simpa using hh.2⟩
      · have hh:=separated_middle x r m hx he hm8
        dsimp only at hh
        rw [hy,hz] at hh
        exact ⟨roundedW x y z,hh⟩
    let vv:=(v-1).toNat
    let ww:=w.toNat
    have cv : (vv:ℤ)=v-1 := Int.toNat_of_nonneg (by change 0≤roundedV x y z-1;omega)
    have cw : (ww:ℤ)=w := Int.toNat_of_nonneg hw0
    apply source_certificate a b c ha hab.le hbc false vv ww 0
      (mask_bound _ _ (by change 0≤v-1;omega) (by change roundedV x y z-1<((2^(c-1):ℕ):ℤ);omega))
      (mask_bound _ _ hw0 (by nlinarith only [hwy,hhalfB])) (by positivity)
    have wn' : window (SW y z-w*SV x y z-v*SU x y+A x y z) (SW y z) := by
      convert wn using 1 <;> ring
    have on' : window (A x y z-v*SU x y+A x y z) (A x y z) := by
      convert outer.2.2.2 using 1 <;> ring
    intro side j
    have hlast : window (rowSeams a b c false side vv ww 0 3) (rowHeads a b c false side 3) := by
      have hh:=hhead false side 3
      simpa [rowSeams,window] using And.intro (show (0:ℤ)≤0 by omega) hh
    cases side <;> fin_cases j
    all_goals first
      | exact hlast
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using outer.1
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using outer.2.1
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using outer.2.2.1
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using outer.2.2.2
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using wo
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using wn'
      | simpa [rowSeams,rowHeads,rowBase,hbase,hnew,cv,cw,v] using on'

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
