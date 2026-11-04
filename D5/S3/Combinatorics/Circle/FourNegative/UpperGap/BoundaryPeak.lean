/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryPeak
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-weak-peak-physical-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Complete rounded physical masks for every weak middle maximum. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryRounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private base newBase charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private standardMargins standard_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets
open private zpow_four zpow_one head_separation peak_middle_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryRounded
open private multiple_floor_nat multiple_floor_peak first_mask_capacity
  multiple_predecessor_bits rounded_last_packet
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding
open private peak_last_equal_int peak_last_adjacent_int peak_last_capacity_int
  peak_last_rounding_int peak_first_lower_int peak_first_adjacent_int
  peak_first_far_int peak_tied_bc_int
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryInteger
open private all_equal_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction

set_option maxHeartbeats 1800000 in
private theorem peak_first_bounds (a b c : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hab : a≤b) (hcb : c≤b)
    (hne : ¬(a=b ∧ b=c)) :
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let z : ℤ := 2^c
    let A := x*y*z+x*y+x+1
    let C := x*y+x+1
    let B := 2*y*C+1
    ∃ q : ℕ, 1≤q ∧ 2*q<2^b ∧
      0≤B-((2*q:ℕ):ℤ)*A ∧ 0≤2*B-1-2*((2*q:ℕ):ℤ)*A ∧
      0≤2*((2*q:ℕ):ℤ)*A-B-1 := by
  dsimp only
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let C := x*y+x+1
  let B := 2*y*C+1
  have hA : 0<A := by dsimp [A];positivity
  have lower : 0≤B-1-2*A ∧ (0≤B-1-4*A ∨ 0≤4*A-B-1) := by
    by_cases he : b=c
    · subst c
      have h := peak_tied_bc_int (2^a) (2^(b-a-1)) 0
        (zpow_four a ha) (zpow_one _) (by norm_num)
      dsimp only at h
      have ey : (2:ℤ)^a*2*2^(b-a-1)=2^b := by
        calc
          _ = (2:ℤ)^(a+(b-a-1)+1) := by simp only [pow_add];norm_num;ring
          _ = _ := by congr 1;omega
      rw [ey] at h
      exact ⟨by dsimp [B,A,C,x,y,z];nlinarith only [h.1],
        Or.inr (by dsimp [B,A,C,x,y,z];nlinarith only [h.2])⟩
    · have h := peak_first_lower_int (2^a) (2^c) (2^(b-c-1))
        (zpow_four a ha) (zpow_four c hc) (zpow_one _)
      dsimp only at h
      have ey : (2:ℤ)^c*2*2^(b-c-1)=2^b := by
        calc
          _ = (2:ℤ)^(c+(b-c-1)+1) := by simp only [pow_add];norm_num;ring
          _ = _ := by congr 1;omega
      rw [ey] at h
      refine ⟨by dsimp [B,A,C,x,y,z];nlinarith only [h.1],?_⟩
      by_cases hadj : b=c+1
      · have h' := peak_first_adjacent_int (2^a) (2^c) 0
          (zpow_four a ha) (zpow_four c hc) (by norm_num)
        dsimp only at h'
        have ey' : (2:ℤ)^c*2=2^b := by rw [hadj,pow_succ]
        rw [ey'] at h'
        exact Or.inr (by dsimp [B,A,C,x,y,z];nlinarith only [h'])
      · have h' := peak_first_far_int (2^a) (2^c) (2^(b-c-2))
          (zpow_four a ha) (zpow_four c hc) (zpow_one _)
        dsimp only at h'
        have ey' : (2:ℤ)^c*4*2^(b-c-2)=2^b := by
          calc
            _ = (2:ℤ)^(c+(b-c-2)+2) := by simp only [pow_add];norm_num;ring
            _ = _ := by congr 1;omega
        rw [ey'] at h'
        exact Or.inl (by dsimp [B,A,C,x,y,z];nlinarith only [h'])
  let q : ℕ := ((B-1)/(2*A)).toNat
  have hn := multiple_floor_nat A B 2 hA (by norm_num) (by norm_num;linarith only [lower.1])
  change 1≤q ∧ ((2*q:ℕ):ℤ)=2*((B-1)/(2*A)) ∧
    1≤B-((2*q:ℕ):ℤ)*A ∧ B-((2*q:ℕ):ℤ)*A≤2*A at hn
  have peak : 0≤2*((2*q:ℕ):ℤ)*A-B-1 := by
    rcases lower.2 with hbuf|hbuf
    · have h := multiple_floor_peak A 2 B hA (by norm_num) (by nlinarith only [hbuf])
      dsimp only at h
      rw [←hn.2.1] at h
      exact h.2.2
    · have hq : (1:ℤ)≤q := by exact_mod_cast hn.1
      push_cast
      nlinarith only [hq,hbuf,hA]
  have cap : ((2*q:ℕ):ℤ)<y := by
    apply first_mask_capacity A C y (2*q) hA (by dsimp [y];positivity)
      (head_separation x y z (zpow_four a ha) (zpow_four b (by omega)) (zpow_four c hc))
    have hh := hn.2.2.1
    dsimp [B] at hh
    push_cast at hh ⊢
    nlinarith only [hh]
  dsimp only [y] at cap
  refine ⟨q,hn.1,by exact_mod_cast cap,?_,?_,?_⟩
  · exact le_trans (by norm_num) hn.2.2.1
  · nlinarith only [hn.2.2.1]
  · exact peak

set_option maxHeartbeats 1800000 in
private theorem peak_last_bounds (a b c : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hab : a≤b) (hcb : c≤b) :
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let z : ℤ := 2^c
    let A := x*y*z+x*y+x+1
    let L := 2*y*z*(x+1)+z+1
    let M := 2*y*y*z+y*z+y+1
    let D := y*z+y+1
    ∃ w : ℕ, w<2^(b-1) ∧ 0≤M-A-(w:ℤ)*L ∧
      0≤(2*M-D)-2*A-(w:ℤ)*(2*L-z-1) ∧
      0≤2*A+2*(w:ℤ)*L-M-1 ∧ 0≤D-(w:ℤ)*(z+1) := by
  dsimp only
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let L := 2*y*z*(x+1)+z+1
  let M := 2*y*y*z+y*z+y+1
  let D := y*z+y+1
  have ey : 2*(2:ℤ)^(b-1)=y := by
    dsimp [y];rw [mul_comm 2 (2^(b-1)),←pow_succ,Nat.sub_add_cancel (by omega : 1≤b)]
  by_cases he : a=b
  · subst b
    have h := peak_last_equal_int (2^c) (2^(a-c)) 0
      (zpow_four c hc) (zpow_one _) (by norm_num)
    dsimp only at h
    have ex : (2:ℤ)^c*2^(a-c)=2^a := by rw [←pow_add,Nat.add_sub_of_le (by omega : c≤a)]
    rw [ex] at h
    refine ⟨0,by positivity,?_,?_,?_,?_⟩
    all_goals dsimp [A,L,M,D,x,y,z];push_cast
    · nlinarith only [h.1]
    · nlinarith only [h.2.1]
    · nlinarith only [h.2.2]
    · simp only [zero_mul,sub_zero]
      positivity
  · by_cases hadj : b=a+1
    · have h := peak_last_adjacent_int (2^a) (2^c) 0
        (zpow_four a ha) (zpow_four c hc) (by norm_num)
      dsimp only at h
      have ey' : (2:ℤ)^a*2=2^b := by rw [hadj,pow_succ]
      rw [ey'] at h
      refine ⟨1,?_,?_,?_,?_,?_⟩
      · have hh : 2≤(2:ℕ)^(b-1) := by
          simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤b-1 by omega)
        omega
      all_goals dsimp [A,L,M,D,x,y,z];push_cast
      · nlinarith only [h.1]
      · nlinarith only [h.2.1]
      · nlinarith only [h.2.2]
      · have hh := mul_nonneg (show (0:ℤ)≤2^b-1 by have := zpow_one b;omega)
            (show (0:ℤ)≤2^c+1 by positivity)
        nlinarith only [hh]
    · have hcap := peak_last_capacity_int (2^a) (2^c) (2^(b-a-1))
        (zpow_four a ha) (zpow_four c hc) (zpow_one _)
      dsimp only at hcap
      have ey' : (2:ℤ)^a*2*2^(b-a-1)=2^b := by
        calc
          _ = (2:ℤ)^(a+(b-a-1)+1) := by simp only [pow_add];norm_num;ring
          _ = _ := by congr 1;omega
      rw [ey'] at hcap
      have hbuf := peak_last_rounding_int (2^a) (2^c) (2^(b-a-2))
        (zpow_four a ha) (zpow_four c hc) (zpow_one _)
      dsimp only at hbuf
      have ey'' : (2:ℤ)^a*4*2^(b-a-2)=2^b := by
        calc
          _ = (2:ℤ)^(a+(b-a-2)+2) := by simp only [pow_add];norm_num;ring
          _ = _ := by congr 1;omega
      rw [ey''] at hbuf
      have hcap' : 0≤M-2*A ∧ 0≤(y-2)*L-(M+1-2*A) := by
        constructor
        · dsimp [M,A,x,y,z];nlinarith only [hcap.1]
        · dsimp [M,A,L,x,y,z];nlinarith only [hcap.2]
      have hbuf' : 0≤M-D-1-2*L := by
        dsimp [M,D,L,x,y,z];nlinarith only [hbuf]
      have hr := rounded_last_packet A L M z (2^(b-1))
        (by
          have h : (0:ℤ)≤2*y*z*(x+1)+z := by dsimp [x,y,z];positivity
          dsimp only [L]
          omega) (zpow_four c hc) (zpow_one _)
        (by omega) (by rw [ey];nlinarith only [hcap'.2])
        (by rw [ey];dsimp only [D] at hbuf';nlinarith only [hbuf'])
      let w : ℤ := (M+1-2*A+2*L-1)/(2*L)
      have hD : 2*2^(b-1)*z+2*2^(b-1)+1=D := by rw [ey]
      change 1≤w ∧ w≤2^(b-1)-1 ∧ 0≤M-A-w*L ∧
        0≤(2*M-(2*2^(b-1)*z+2*2^(b-1)+1))-2*A-w*(2*L-z-1) ∧
        0≤2*A+2*w*L-M-1 ∧ 0<2*2^(b-1)*z+2*2^(b-1)+1-w*(z+1) at hr
      rw [hD] at hr
      have hw : (w.toNat:ℤ)=w := Int.toNat_of_nonneg (by omega)
      refine ⟨w.toNat,?_,?_,?_,?_,?_⟩
      · have hlt : (w.toNat:ℤ)<(2:ℤ)^(b-1) := by rw [hw];omega
        exact_mod_cast hlt
      all_goals rw [hw]
      · exact hr.2.2.1
      · exact hr.2.2.2.1
      · exact hr.2.2.2.2.1
      · exact hr.2.2.2.2.2.le

set_option maxHeartbeats 1800000 in
private theorem peak_certificate (a b c : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hab : a≤b) (hcb : c≤b) :
    Nonempty (Certificate a b c (b+1)) := by
  by_cases he : a=b ∧ b=c
  · rcases he with ⟨hab',hbc'⟩
    subst b
    subst c
    exact all_equal_certificate a ha
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let B := 2*y*(x*y+x+1)+1
  let L := 2*y*z*(x+1)+z+1
  let M := 2*y*y*z+y*z+y+1
  let D := y*z+y+1
  obtain ⟨q,hq,hqcap,lo,ln,lp⟩ := peak_first_bounds a b c ha hc hab hcb he
  obtain ⟨w,hw,sl,tl,pl,ed⟩ := peak_last_bounds a b c ha hc hab hcb
  have hzpos : (0:ℤ)≤z := by dsimp [z];positivity
  have ey : 2*(2:ℤ)^(b-1)=y := by
    dsimp [y]
    rw [mul_comm 2 (2^(b-1)),←pow_succ,Nat.sub_add_cancel (by omega : 1≤b)]
  have hwz : (w:ℤ)<(2:ℤ)^(b-1) := by exact_mod_cast hw
  have hwy : 2*(w:ℤ)≤y := by nlinarith only [ey,hwz]
  have hprod := mul_le_mul_of_nonneg_right hwy (by omega : 0≤z+1)
  have ed2 : 0≤D-2*(w:ℤ)*(z+1) := by
    dsimp only [D]
    nlinarith only [hprod]
  have hm := peak_middle_bounds a b c ha hc hab hcb
  let u := 2*q-1
  let r : ℕ := if a<c then 1 else 0
  have hu : (u:ℤ)=((2*q:ℕ):ℤ)-1 := by
    dsimp [u];rw [Nat.cast_sub (by omega : 1≤2*q)];norm_num
  have hr : (r:ℤ)=if a<c then (1:ℤ) else 0 := by dsimp [r];split_ifs <;>norm_num
  have hrcap : r<2^b := by
    have hb := Nat.two_pow_pos b
    have hb' : 1<2^b := by
      have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤b by omega)
      norm_num at hh;omega
    dsimp [r];split_ifs <;>omega
  apply standard_certificate a b c (b+1) u r 0 0 w ha (by omega) hc (by omega)
    (by dsimp [u];simpa using (show 2*q-1<2^b by omega))
    (by simpa using hrcap) (by positivity) (by positivity) (by exact hw)
  · intro e _ hre
    by_cases hac : a<c
    · have he0 : e=0 := by
        have he' : (2^0:ℕ).testBit e=true := by simpa [r,hac] using hre
        have ht : 0=e := of_decide_eq_true (by simpa only [Nat.testBit_two_pow] using he')
        exact ht.symm
      subst e
      exact multiple_predecessor_bits 1 q hq 0 (by omega)
    · simp [r,hac] at hre
  · intro e _ hre;simp at hre
  · have hbase : base a b c (b+1)=![A,B,L,M] := by
      funext r
      fin_cases r <;> dsimp [base,A,B,L,M,x,y,z] <;> (try simp only [pow_succ]) <;> ring
    dsimp only [standardMargins,newBase]
    rw [hbase]
    dsimp [charge]
    rw [hu,hr]
    change 0≤B-((2*q:ℕ):ℤ)*A at lo
    change 0≤2*B-1-2*((2*q:ℕ):ℤ)*A at ln
    change 0≤2*((2*q:ℕ):ℤ)*A-B-1 at lp
    change 0≤L-((if a<c then (1:ℤ) else 0)+1)*A ∧
      0≤(2*L-z-1)-2*((if a<c then (1:ℤ) else 0)+1)*A ∧
      0≤2*((if a<c then (1:ℤ) else 0)+1)*A-L-1 at hm
    change 0≤M-A-(w:ℤ)*L at sl
    change 0≤(2*M-D)-2*A-(w:ℤ)*(2*L-z-1) at tl
    change 0≤2*A+2*(w:ℤ)*L-M-1 at pl
    change 0≤D-(w:ℤ)*(z+1) at ed
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals dsimp only [D,y,z] at hm tl ed ed2 hzpos
    all_goals nlinarith only [lo,ln,lp,hm.1,hm.2.1,hm.2.2,sl,tl,pl,ed,ed2,hzpos]

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
