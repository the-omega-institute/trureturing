/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryRounded
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-rounded-physical-boundary-constructions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Rounded masks for the weak-peak and strict-first boundary chambers. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryInteger

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private base newBase charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private standardMargins standard_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets
open private multiple_floor_nat multiple_floor_peak first_mask_capacity
  multiple_predecessor_bits rounded_last_packet
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding
open private first_less_signs_int first_greater_signs_int first_equal_signs_int
  peak_middle_low_int peak_middle_high_int peak_last_equal_int peak_last_adjacent_int
  peak_last_capacity_int peak_last_rounding_int peak_first_lower_int
  peak_first_adjacent_int peak_first_far_int peak_tied_bc_int
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryInteger
open private interval_capacity singleton_capacity
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction

private theorem zpow_four (n : ℕ) (hn : 2≤n) : (4:ℤ)≤2^n := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hn
  norm_num at h
  exact h
private theorem zpow_one (n : ℕ) : (1:ℤ)≤2^n := by
  exact_mod_cast Nat.one_le_two_pow

private theorem head_separation (x y z : ℤ) (hx : 4≤x) (hy : 4≤y) (hz : 4≤z) :
    2*(x*y+x+1)<x*y*z+x*y+x+1 := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ x=u+4 := ⟨x-4,by omega,by ring⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ y=v+4 := ⟨y-4,by omega,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ z=w+4 := ⟨z-4,by omega,by ring⟩
  apply sub_pos.mp
  ring_nf
  positivity

set_option maxHeartbeats 1800000 in
private theorem first_less_certificate (a b c : ℕ)
    (hb : 2≤b) (hbc : b<c) (hca : c<a) :
    Nonempty (Certificate a b c (a+1)) := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let C := x*y+x+1
  let B := 2*x*C+1
  let L := 2*x*z*(x+1)+z+1
  let M := 2*x*y*z+y*z+y+1
  let D := y*z+y+1
  let p : ℕ := 2^(c-b-1)
  let q : ℕ := ((B-1)/(2*A)).toNat
  let u := 2*q-1
  have hx := zpow_four a (by omega)
  have hy := zpow_four b hb
  have hz := zpow_four c (by omega)
  change 4≤x at hx
  change 4≤y at hy
  change 4≤z at hz
  have hA : 0<A := by dsimp [A]; positivity
  have hs := head_separation x y z hx hy hz
  have ex : (2:ℤ)^b*4*2^(c-b-1)*2^(a-c-1)=x := by
    calc
      _ = (2:ℤ)^(b+(c-b-1)+(a-c-1)+2) := by simp only [pow_add]; norm_num; ring
      _ = x := by dsimp [x]; congr 1; omega
  have ez : (2:ℤ)^b*2*2^(c-b-1)=z := by
    calc
      _ = (2:ℤ)^(b+(c-b-1)+1) := by simp only [pow_add]; norm_num; ring
      _ = z := by dsimp [z]; congr 1; omega
  have h := first_less_signs_int (2^b) (2^(c-b-1)) (2^(a-c-1))
    hy (zpow_one _) (zpow_one _)
  dsimp only at h
  rw [ex,ez] at h
  have hpcast : (p:ℤ)=(2:ℤ)^(c-b-1) := by simp [p]
  rw [←hpcast] at h
  have eB : x*2*(x*y+x+1)+1=B := by dsimp [B,C]; ring
  have eL : x*2*z*(x+1)+z+1=L := by dsimp [L];ring
  have eM : x*2*y*z+y*z+y+1=M := by dsimp [M];ring
  rw [eB,eL,eM] at h
  change 0≤B-1-A*4 ∧ 0≤A-C*2 ∧
    0≤L-A-(p:ℤ)*B ∧ 0≤(L*2-z-1)-A*2-(p:ℤ)*(B*2-1) ∧
    0≤A*2+((p:ℤ)*2)*B-L-1 ∧
    0≤M-A ∧ 0≤(M*2-D)-A*2 ∧ 0≤A*2-M-1 at h
  obtain ⟨buffer,sep,sm,tm,pm,sl,tl,pl⟩ := h
  have hn := multiple_floor_nat A B 2 hA (by norm_num) (by norm_num; nlinarith only [buffer,hA])
  dsimp only at hn
  have hq : 1≤q := hn.1
  have hcast : ((2*q:ℕ):ℤ)=2*((B-1)/(2*A)) := by simpa [q] using hn.2.1
  have hu : (u:ℤ)=((2*q:ℕ):ℤ)-1 := by
    dsimp [u]
    rw [Nat.cast_sub (by omega : 1≤2*q)]
    norm_num
  have hpeak := multiple_floor_peak A 2 B hA (by norm_num) (by nlinarith only [buffer])
  dsimp only at hpeak
  rw [←hcast] at hpeak
  have hncap : ((2*q:ℕ):ℤ)<x := by
    apply first_mask_capacity A C x ((2*q:ℕ):ℤ) hA (by omega) hs
    have hh := hn.2.2.1
    change 1≤B-((2*q:ℕ):ℤ)*A at hh
    dsimp [B] at hh
    push_cast at hh ⊢
    nlinarith only [hh]
  dsimp only [x] at hncap
  have hucap : u<2^a := by
    have hncap' : 2*q<2^a := by exact_mod_cast hncap
    omega
  have hpz : 2*(p:ℤ)≤z := by
    calc
      _ = (2:ℤ)^(c-b-1+1) := by dsimp [p];push_cast;rw [pow_succ];ring
      _ ≤ z := by
        dsimp [z]
        exact pow_le_pow_right₀ (by norm_num) (by omega : c-b-1+1≤c)
  have hzpos : (0:ℤ)≤z := by dsimp [z];positivity
  have hD : 0≤D := by dsimp [D];positivity
  apply standard_certificate a b c (a+1) u 0 p 0 0
    (by omega) hb (by omega) (by omega)
  · simpa using hucap
  · positivity
  · exact singleton_capacity (c-1) (c-b-1) (by omega)
  · positivity
  · positivity
  · intro e _ he; simp at he
  · intro e _ he; simp at he
  · have hbase : base a b c (a+1)=![A,B,L,M] := by
      funext r
      fin_cases r <;> dsimp [base,A,B,C,L,M,x,y,z] <;> (try simp only [pow_succ]) <;> ring
    dsimp only [standardMargins,newBase]
    rw [hbase]
    dsimp [charge]
    rw [hu]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals dsimp only [D,y,z] at tm tl hpz hD hzpos
    all_goals nlinarith only [hpeak.1,hpeak.2.1,hpeak.2.2,sm,tm,pm,sl,tl,pl,hpz,hD,hzpos]

set_option maxHeartbeats 1400000 in
private theorem peak_middle_bounds (a b c : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hab : a≤b) (hcb : c≤b) :
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let z : ℤ := 2^c
    let A := x*y*z+x*y+x+1
    let L := 2*y*z*(x+1)+z+1
    let Lp := 2*L-z-1
    let r : ℤ := if a<c then 1 else 0
    0≤L-(r+1)*A ∧ 0≤Lp-2*(r+1)*A ∧ 0≤2*(r+1)*A-L-1 := by
  dsimp only
  by_cases hac : a<c
  · simp only [if_pos hac]
    have h := peak_middle_high_int (2^a) (2^(c-a-1)) (2^(b-c))
      (zpow_four a ha) (zpow_one _) (zpow_one _)
    dsimp only at h
    have ez : (2:ℤ)^a*2*2^(c-a-1)=2^c := by
      calc
        _ = (2:ℤ)^(a+(c-a-1)+1) := by simp only [pow_add];norm_num;ring
        _ = _ := by congr 1;omega
    have ey : (2:ℤ)^c*2^(b-c)=2^b := by rw [←pow_add,Nat.add_sub_of_le hcb]
    rw [ez,ey] at h
    obtain ⟨h0,h1,h2⟩ := h
    exact ⟨by nlinarith only [h0],by nlinarith only [h1],by nlinarith only [h2]⟩
  · simp only [if_neg hac]
    have h := peak_middle_low_int (2^c) (2^(a-c)) (2^(b-a))
      (zpow_four c hc) (zpow_one _) (zpow_one _)
    dsimp only at h
    have ex : (2:ℤ)^c*2^(a-c)=2^a := by rw [←pow_add,Nat.add_sub_of_le (by omega : c≤a)]
    have ey : (2:ℤ)^a*2^(b-a)=2^b := by rw [←pow_add,Nat.add_sub_of_le hab]
    rw [ex,ey] at h
    obtain ⟨h0,h1,h2⟩ := h
    exact ⟨by nlinarith only [h0],by nlinarith only [h1],by nlinarith only [h2]⟩

set_option maxHeartbeats 1800000 in
private theorem first_right_bounds (a b c : ℕ)
    (hc : 2≤c) (hcb : c≤b) (hba : b<a) :
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let z : ℤ := 2^c
    let H : ℤ := 2^(a-b)
    let A := x*y*z+x*y+x+1
    let C := x*y+x+1
    let B := 2*x*C+1
    let L := 2*x*z*(x+1)+z+1
    let M := 2*x*y*z+y*z+y+1
    let D := y*z+y+1
    0≤A-2*C ∧ 0≤L-H*A ∧ 0≤(2*L-z-1)-2*H*A ∧
    0≤2*H*A-L-1 ∧ 0≤M-A ∧ 0≤(2*M-D)-2*A ∧ 0≤2*A-M-1 ∧
    0≤B-1-H*A ∧ (0≤B-1-2*H*A ∨ 0≤2*H*A-B-1) := by
  dsimp only
  by_cases he : c=b
  · subst c
    have h := first_equal_signs_int (2^b) (2^(a-b-1)) 0
      (zpow_four b hc) (zpow_one _) (by norm_num)
    dsimp only at h
    have ex : (2:ℤ)^b*2*2^(a-b-1)=2^a := by
      calc
        _ = (2:ℤ)^(b+(a-b-1)+1) := by simp only [pow_add]; norm_num; ring
        _ = _ := by congr 1; omega
    have eh : (2:ℤ)^(a-b-1)*2=2^(a-b) := by
      rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤a-b)]
    rw [ex,eh] at h
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,_,_,h9,h10,_⟩ := h
    exact ⟨by nlinarith only [h0],by nlinarith only [h1],by nlinarith only [h2],
      by nlinarith only [h3],by nlinarith only [h4],by nlinarith only [h5],
      by nlinarith only [h6],by nlinarith only [h10],Or.inr (by nlinarith only [h9])⟩
  · have h := first_greater_signs_int (2^c) (2^(b-c-1)) (2^(a-b-1))
      (zpow_four c hc) (zpow_one _) (zpow_one _)
    dsimp only at h
    have ey : (2:ℤ)^c*2*2^(b-c-1)=2^b := by
      calc
        _ = (2:ℤ)^(c+(b-c-1)+1) := by simp only [pow_add]; norm_num; ring
        _ = _ := by congr 1; omega
    have ex : (2:ℤ)^c*4*2^(b-c-1)*2^(a-b-1)=2^a := by
      calc
        _ = (2:ℤ)^(c+(b-c-1)+(a-b-1)+2) := by simp only [pow_add]; norm_num; ring
        _ = _ := by congr 1; omega
    have eh : (2:ℤ)^(a-b-1)*2=2^(a-b) := by
      rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤a-b)]
    rw [ex,ey,eh] at h
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
    have hH : (0:ℤ)≤2^(a-b) := by positivity
    have hA : (0:ℤ)≤2^a*2^b*2^c+2^a*2^b+2^a+1 := by positivity
    have hHA := mul_nonneg hH hA
    exact ⟨by nlinarith only [h0],by nlinarith only [h1],by nlinarith only [h2],
      by nlinarith only [h3],by nlinarith only [h4],by nlinarith only [h5],
      by nlinarith only [h6],by nlinarith only [h7,hHA],Or.inl (by nlinarith only [h7])⟩

set_option maxHeartbeats 1800000 in
private theorem first_right_certificate (a b c : ℕ)
    (hc : 2≤c) (hcb : c≤b) (hba : b<a) :
    Nonempty (Certificate a b c (a+1)) := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let C := x*y+x+1
  let B := 2*x*C+1
  let L := 2*x*z*(x+1)+z+1
  let M := 2*x*y*z+y*z+y+1
  let D := y*z+y+1
  let H : ℕ := 2^(a-b)
  let q : ℕ := ((B-1)/((H:ℤ)*A)).toNat
  let n : ℕ := H*q
  let u := n-1
  let r := H-1
  have hH : 1≤H := Nat.one_le_two_pow
  have hHz : (0:ℤ)<H := by exact_mod_cast hH
  have hA : 0<A := by dsimp [A]; positivity
  have h := first_right_bounds a b c hc hcb hba
  have hHcast : (H:ℤ)=(2:ℤ)^(a-b) := by simp [H]
  rw [←hHcast] at h
  change 0≤A-2*C ∧ 0≤L-(H:ℤ)*A ∧ 0≤(2*L-z-1)-2*(H:ℤ)*A ∧
    0≤2*(H:ℤ)*A-L-1 ∧ 0≤M-A ∧ 0≤(2*M-D)-2*A ∧ 0≤2*A-M-1 ∧
    0≤B-1-(H:ℤ)*A ∧ (0≤B-1-2*(H:ℤ)*A ∨ 0≤2*(H:ℤ)*A-B-1) at h
  obtain ⟨sep,sm,tm,pm,sl,tl,pl,lower,buffer⟩ := h
  have hn := multiple_floor_nat A B H hA hH (by omega)
  change 1≤q ∧ (n:ℤ)=(H:ℤ)*((B-1)/((H:ℤ)*A)) ∧
    1≤B-(n:ℤ)*A ∧ B-(n:ℤ)*A≤(H:ℤ)*A at hn
  have hnH : (H:ℤ)≤n := by
    have hq : (1:ℤ)≤q := by exact_mod_cast hn.1
    dsimp [n]
    push_cast
    nlinarith only [hq,hHz]
  have peak : 0≤2*(n:ℤ)*A-B-1 := by
    rcases buffer with hbuf|hbuf
    · have hh := multiple_floor_peak A H B hA hHz (by nlinarith only [hbuf])
      dsimp only at hh
      rw [←hn.2.1] at hh
      exact hh.2.2
    · nlinarith only [hnH,hA,hbuf]
  have hncap : (n:ℤ)<x := by
    apply first_mask_capacity A C x n hA (by dsimp [x];positivity)
      (head_separation x y z (zpow_four a (by omega)) (zpow_four b (by omega)) (zpow_four c hc))
    have hh := hn.2.2.1
    dsimp [B] at hh
    push_cast at hh ⊢
    nlinarith only [hh]
  have hn1 : 1≤n := by exact_mod_cast (show (1:ℤ)≤n by omega)
  have hu : (u:ℤ)=(n:ℤ)-1 := by dsimp [u];rw [Nat.cast_sub hn1];norm_num
  have hr : (r:ℤ)=(H:ℤ)-1 := by dsimp [r];rw [Nat.cast_sub hH];norm_num
  dsimp only [x] at hncap
  have hcU : u<2^a := by
    have hnx : n<2^a := by exact_mod_cast hncap
    dsimp [u];omega
  have hcR : r<2^a := by
    exact interval_capacity a (a-b) (by omega)
  have hzpos : (0:ℤ)≤z := by dsimp [z];positivity
  have hD : 0≤D := by dsimp [D];positivity
  apply standard_certificate a b c (a+1) u r 0 0 0 (by omega) (by omega) hc (by omega)
    (by simpa using hcU) (by simpa using hcR) (by positivity) (by positivity) (by positivity)
  · intro e _ he
    have he' : e<a-b := by simpa [r,H,Nat.testBit_two_pow_sub_one] using he
    exact multiple_predecessor_bits (a-b) q hn.1 e he'
  · intro e _ he;simp at he
  · have hbase : base a b c (a+1)=![A,B,L,M] := by
      funext r
      fin_cases r <;> dsimp [base,A,B,C,L,M,x,y,z] <;> (try simp only [pow_succ]) <;> ring
    dsimp only [standardMargins,newBase]
    rw [hbase]
    dsimp [charge]
    rw [hu,hr]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals dsimp only [D,y,z] at tm tl hD hzpos
    all_goals nlinarith only [hn.2.2.1,peak,sm,tm,pm,sl,tl,pl,hD,hzpos]

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
