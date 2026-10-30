/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoFloors
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoFloors
   mirror-E: none(waiver:private-constructor-implementation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded floor and ceiling certificates for the minimum-two physical masks. -/
module
import all D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

private theorem floor_bounds (n d : ℤ) (hd : 0<d) :
    d*(n/d)≤n ∧ n<d*(n/d+1) := by
  have h0 := Int.emod_nonneg n (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos n hd
  have he := Int.mul_ediv_add_emod n d
  constructor <;> nlinarith

private theorem a_two_far (q h : ℤ) (hq : 1≤q) (hh : 32*q≤h) :
    Certificate 4 (2*h) (8*q) (constructor 4 (2*h) (8*q)) := by
  let n := oldHeight 4 (2*h) (8*q) .alpha
  let d := 1+8*q+8*q*4
  let v := n/d
  have hn : n=32*h*q-20*q-1 := by
    dsimp [n,oldHeight,cap,atNegative]
    have ht : 8*q/2=4*q := by omega
    rw [ht]; ring
  have hd : d=40*q+1 := by dsimp [d]; ring
  have hv := floor_bounds n d (by rw [hd]; omega)
  change d*v≤n ∧ n<d*(v+1) at hv
  have hv0 : 0≤v := Int.ediv_nonneg (by rw [hn]; nlinarith) (by rw [hd]; omega)
  have hvh : 5*v<4*h := by
    by_contra hn'
    have hp := mul_nonneg (show 0≤q by omega) (show 0≤5*v-4*h by omega)
    rw [hn,hd] at hv
    nlinarith
  have ht2 : 8*q/2=4*q := by omega
  have hs2 : 2*h/2=h := by omega
  have ht8 : 8*q/8=q := by omega
  have hcon : constructor 4 (2*h) (8*q)=makePlan 11 .bga .q ⟨q,0,1⟩ ⟨0,v,0⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, ht8] <;> rfl
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
  · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [ht2,hs2]
    rw [hn,hd] at hv
    norm_num
    repeat' constructor
    all_goals nlinarith [mul_nonneg (show 0≤h-32*q by omega) (show 0≤q-1 by omega), sq_nonneg (q-1)]

private theorem c_two_far_s (q h : ℤ) (hq : 1≤q) (hh : 64*q≤h) :
    Certificate (64*q) (4*h) 4 (constructor (64*q) (4*h) 4) := by
  let n := (64*q)*(4*h)-64*q-2
  let d := 4*(64*q)+5
  let y := n/d
  have hd : 0<d := by dsimp [d]; omega
  have hy := floor_bounds n d hd
  change d*y≤n ∧ n<d*(y+1) at hy
  have hy0 : 0≤y := Int.ediv_nonneg (by dsimp [n]; nlinarith) (by omega)
  have hyh : y<h := by
    by_contra hn
    have hp := mul_nonneg (show 0≤q by omega) (show 0≤y-h by omega)
    dsimp [n,d] at hy
    nlinarith
  have hr2 : 64*q/2=32*q := by omega
  have hs2 : 4*h/2=2*h := by omega
  have hw : 25*(64*q)/64=25*q := by omega
  have hcon : constructor (64*q) (4*h) 4=makePlan 29 .bga .q ⟨1,y,0⟩ ⟨0,0,25*q⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hw] <;> rfl
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,hs2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,hs2]
    dsimp [n,d] at hy
    norm_num
    repeat' constructor
    all_goals nlinarith [mul_nonneg (show 0≤h-64*q by omega) (show 0≤q-1 by omega),sq_nonneg (q-1)]

private theorem c_two_far_r (e : ℕ) (h : ℤ)
    (hq : 2≤(2:ℤ)^e) (hh : 8≤h) (hrel : h≤4*(2:ℤ)^e) :
    Certificate (64*(2:ℤ)^e) (4*h) 4
      (constructor (64*(2:ℤ)^e) (4*h) 4) := by
  let q : ℤ := 2^e
  change 2≤q at hq
  change h≤4*q at hrel
  let n := 128*q+2-9*h
  let d := 36*h+1
  let m := -(-n/d)
  have hd : 0<d := by dsimp [d]; omega
  have hm := floor_bounds (-n) d hd
  have hmneg : -n/d = -m := by simp [m]
  rw [hmneg] at hm
  have hn : 0<n := by dsimp [n]; omega
  have hm0 : 0≤m := by
    by_contra ht
    have hp := mul_nonpos_of_nonneg_of_nonpos hd.le (show m≤0 by omega)
    nlinarith [hm.1]
  have hmq : m<q := by
    have hb : n≤d*(q-1) := by
      dsimp [n,d]
      nlinarith [mul_nonneg (show 0≤q-2 by omega) (show 0≤h-8 by omega)]
    by_contra ht
    have hp := mul_nonneg hd.le (show 0≤m-q by omega)
    nlinarith [hm.2]
  have hG : 0≤192*q+3-5*h-(20*h+1)*m := by
    by_contra ht
    have hp := mul_nonpos_of_nonneg_of_nonpos hd.le
      (show 192*q+3-5*h-(20*h+1)*m≤0 by omega)
    have hr := mul_nonneg (show 0≤h by omega) (show 0≤4*q-h by omega)
    have hc := mul_nonneg (show 0≤20*h+1 by omega)
      (show 0≤n+d-d*m by nlinarith [hm.2])
    dsimp [n,d] at hp hc
    nlinarith
  have hr2 : 64*q/2=32*q := by omega
  have hs2 : 4*h/2=2*h := by omega
  have hsv : 4*h/4=h := by omega
  have hs9 : 9*(4*h)/4=9*h := by omega
  have hw : 25*(64*q)/64=25*q := by omega
  have hmform : -(-(2*(64*q)+2-9*(4*h)/4)/(9*(4*h)+1))=m := by
    rw [hs9]
    dsimp [m,n,d]
    congr 2 <;> ring
  have hcon : constructor (64*q) (4*h) 4=makePlan 28 .agb .q ⟨1,h-1,m⟩ ⟨0,0,25*q⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hmform,hsv,hw]
  change Certificate (64*q) (4*h) 4 (constructor (64*q) (4*h) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,hs2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,by simp,?_⟩
    have hmn : m.toNat<2^e := by
      have he := Int.toNat_of_nonneg hm0
      exact_mod_cast (show (m.toNat:ℤ)<(2:ℤ)^e by change _<q; omega)
    have hp : (25*q).toNat=2^e*25 := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num; ring
    rw [hp]
    exact disjoint_low_bits e m.toNat 25 hmn
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,hs2]
    dsimp [n,d] at hm
    norm_num
    repeat' constructor
    all_goals nlinarith [mul_nonneg (show 0≤q-2 by omega) (show 0≤h-8 by omega)]

private theorem b_two_diagonal (q : ℤ) (hq : 1≤q) :
    Certificate (16*q) 4 (16*q) (constructor (16*q) 4 (16*q)) := by
  let n := oldHeight (16*q) 4 (16*q) .gamma
  let d := 1+16*q+(16*q)*4
  let v := n/d
  have hr2 : 16*q/2=8*q := by omega
  have hn : n=512*q*q-40*q-1 := by
    dsimp [n,oldHeight,cap,atNegative]; rw [hr2]; ring
  have hd : d=80*q+1 := by dsimp [d]; ring
  have hv := floor_bounds n d (by rw [hd]; omega)
  change d*v≤n ∧ n<d*(v+1) at hv
  have hv0 : 0≤v := Int.ediv_nonneg (by rw [hn]; nlinarith) (by rw [hd]; omega)
  have hvc : v<8*q := by
    apply Int.ediv_lt_of_lt_mul (by rw [hd]; omega)
    rw [hn,hd]; nlinarith [sq_nonneg q]
  have hcon : constructor (16*q) 4 (16*q)=makePlan 13 .bag .p ⟨0,0,8*q-1⟩ ⟨v,0,0⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2] <;> rfl
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2]
    rw [hn,hd] at hv
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]

private theorem b_two_tall (h w : ℤ) (hh : 4≤h) (hw : 4*h≤w) :
    Certificate (2*h) 4 (2*w) (constructor (2*h) 4 (2*w)) := by
  let n := cap (2*h) 4 (2*w)
  let d := 1+2*h+(2*h)*4
  let v := n/d
  have hr2 : 2*h/2=h := by omega
  have ht2 : 2*w/2=w := by omega
  have hn : n=8*h*w-1 := by dsimp [n,cap]; rw [ht2]; ring
  have hd : d=10*h+1 := by dsimp [d]; ring
  have hv := floor_bounds n d (by rw [hd]; omega)
  change d*v≤n ∧ n<d*(v+1) at hv
  have hv0 : 0≤v := Int.ediv_nonneg (by rw [hn]; nlinarith) (by rw [hd]; omega)
  have hvc : v<w := by
    apply Int.ediv_lt_of_lt_mul (by rw [hd]; omega)
    rw [hn,hd]; nlinarith
  have hcon : constructor (2*h) 4 (2*w)=makePlan 12 .bag .q ⟨v,0,0⟩ ⟨0,0,h-1⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2] <;> rfl
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2]
    rw [hn,hd] at hv
    norm_num
    repeat' constructor
    all_goals nlinarith [mul_nonneg (show 0≤h-4 by omega) (show 0≤w-4*h by omega),sq_nonneg (h-4)]

private theorem b_two_next_arithmetic (h : ℤ) (hh : 4≤h) (hnodiv : ¬(5:ℤ)∣8*h) :
    Certificate (2*h) 4 (4*h) (constructor (2*h) 4 (4*h)) := by
  let n := cap (2*h) 4 (4*h)
  let d := 1+2*h+(2*h)*4
  let v := n/d
  let z := 8*h/5
  have hz : 0≤8*h-5*z ∧ 8*h-5*z<5 := by
    have hh' := floor_bounds (8*h) 5 (by norm_num)
    change 5*z≤8*h ∧ 8*h<5*(z+1) at hh'
    omega
  have hz1 : 1≤8*h-5*z := by
    by_contra ht
    apply hnodiv
    exact ⟨z,by omega⟩
  have hz0 : 0≤z := Int.ediv_nonneg (by omega) (by norm_num)
  have hzmax : z≤2*h-1 := by omega
  have hr2 : 2*h/2=h := by omega
  have ht2 : 4*h/2=2*h := by omega
  have hn : n=16*h*h-1 := by dsimp [n,cap]; rw [ht2]; ring
  have hd : d=10*h+1 := by dsimp [d]; ring
  have hvz : v=z := by
    apply (Int.ediv_eq_iff_of_pos (by rw [hd]; omega)).mpr
    rw [hn,hd]
    constructor <;> nlinarith [mul_nonneg (show 0≤h by omega)
      (show 0≤8*h-5*z-1 by omega),
      mul_nonneg (show 0≤h by omega) (show 0≤4-(8*h-5*z) by omega)]
  have hv0 : 0≤v := by omega
  have hvc : v<2*h := by omega
  have hrem : 0≤n-d*v ∧ n-d*v<8*h := by
    rw [hvz,hn,hd]
    constructor <;> nlinarith [mul_nonneg (show 0≤h by omega)
      (show 0≤8*h-5*z-1 by omega),
      mul_nonneg (show 0≤h by omega) (show 0≤4-(8*h-5*z) by omega)]
  have hcon : constructor (2*h) 4 (4*h)=makePlan 12 .bag .q ⟨v,0,0⟩ ⟨0,0,h-1⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2] <;> rfl
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2]
    rw [hn,hd] at hrem
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (h-4)]

private theorem b_two_next (e : ℕ) :
    Certificate (8*(2:ℤ)^e) 4 (16*(2:ℤ)^e)
      (constructor (8*(2:ℤ)^e) 4 (16*(2:ℤ)^e)) := by
  have hp : 1≤(2:ℤ)^e := by exact_mod_cast Nat.one_le_two_pow
  have hn : ¬(5:ℕ)∣2^(e+5) := by
    intro h
    have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow h
    norm_num at hh
  have hnZ : ¬(5:ℤ)∣8*(4*2^e) := by
    have he : 8*(4*(2:ℤ)^e)=2^(e+5) := by rw [pow_add]; norm_num; ring
    rw [he]
    exact_mod_cast hn
  convert b_two_next_arithmetic (4*2^e) (by omega) hnZ using 1 <;> ring

private theorem b_two_far (h q : ℤ) (hq : 1≤q) (hh : 16*q≤h)
    (hex : 2≤q ∨ 32≤h) :
    Certificate (2*h) 4 (8*q) (constructor (2*h) 4 (8*q)) := by
  let n := 64*h*q-10*h-32*q-4
  let d := 64*q+5
  let z := n/d
  have hd : 0<d := by dsimp [d]; omega
  have hz := floor_bounds n d hd
  change d*z≤n ∧ n<d*(z+1) at hz
  have hz0 : 0≤z := Int.ediv_nonneg
    (by dsimp [n]; nlinarith [mul_nonneg (show 0≤h-16*q by omega) (show 0≤q-1 by omega),sq_nonneg (q-1)]) hd.le
  have hzc : z<h := by
    apply Int.ediv_lt_of_lt_mul hd
    dsimp [n,d]; nlinarith
  have hb : 2048*q*q+496*q+30≤h*(160*q-25) := by
    rcases hex with hex|hex
    · nlinarith [mul_nonneg (show 0≤h-16*q by omega) (show 0≤160*q-25 by omega),sq_nonneg (q-2)]
    · by_cases hq2 : 2≤q
      · nlinarith [mul_nonneg (show 0≤h-16*q by omega) (show 0≤160*q-25 by omega),sq_nonneg (q-2)]
      · have he : q=1 := by omega
        subst q; nlinarith
  have htail : 32*h*q-16*q-3-(32*q+5)*z≤5*h := by
    by_contra ht
    have hp := mul_pos hd (show 0<32*h*q-16*q-3-(32*q+5)*z-5*h by omega)
    have hc := mul_pos (show 0<32*q+5 by omega)
      (show 0<d*(z+1)-n by nlinarith [hz.2])
    dsimp [n,d] at hp hc
    nlinarith
  have hr2 : 2*h/2=h := by omega
  have ht2 : 8*q/2=4*q := by omega
  have hp : 3*(8*q)/8=3*q := by omega
  have hzform : (4*(2*h)*(8*q)-5*(2*h)-4*(8*q)-4)/(8*(8*q)+5)=z := by
    dsimp [z,n,d]
    congr 1 <;> ring
  have hcon : constructor (2*h) 4 (8*q)=makePlan 16 .agb .t ⟨3*q,0,0⟩ ⟨0,0,z⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hp,hzform]
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2]
    dsimp [n,d] at hz
    norm_num
    repeat' constructor
    all_goals nlinarith [mul_nonneg (show 0≤h-16*q by omega) (show 0≤q-1 by omega),sq_nonneg (q-1)]

private theorem a_two_ordered_small (q : ℤ) (hq : 2≤q) :
    Certificate 4 8 (8*q) (constructor 4 8 (8*q)) := by
  have ht2 : 8*q/2=4*q := by omega
  have hq' : 8*q/8=q := by omega
  have hv : (8*(8*q)-3*8-4)/(5*(8*q)+1)=1 := by
    apply (Int.ediv_eq_iff_of_pos (by omega)).mpr
    constructor <;> nlinarith
  have hv' : (8*(8*q)-24-4)/(5*(8*q)+1)=1 := by simpa using hv
  have hcon : constructor 4 8 (8*q)=chooseEar 4 8 (8*q) 7 ⟨3*q,0,0⟩ ⟨0,1,1⟩ := by
    simp [constructor,show 8*q≠4 by omega,show 8≤8*q by omega,hq',hv']
    all_goals simp only [show q*3=3*q by ring]
  rw [hcon]
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,?_,?_⟩
    · dsimp [Bounded,makePlan]; rw [ht2]; omega
    · dsimp [Bounded,makePlan]; rw [ht2]; omega
    · simp [Separate,makePlan]
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [ht2]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [ht2] at he
      norm_num at *
      omega

private theorem a_two_ordered (h q : ℤ) (hh : 8≤h) (hq : 1≤q) :
    Certificate 4 (2*h) (2*h*q) (constructor 4 (2*h) (2*h*q)) := by
  let n := (2*h)*(2*h*q)-3*(2*h)-4
  let d := 5*(2*h*q)+1
  let v := n/d
  have hp : 0≤h*h*q := mul_nonneg (by nlinarith [sq_nonneg h]) (by omega)
  have hp' := mul_nonneg (show 0≤q-1 by omega) (sq_nonneg h)
  have hd : 0<d := by dsimp [d]; nlinarith
  have hv := floor_bounds n d hd
  change d*v≤n ∧ n<d*(v+1) at hv
  have hv0 : 0≤v := Int.ediv_nonneg (by dsimp [n]; nlinarith [sq_nonneg (h-8)]) hd.le
  have hvc : v<h := by
    apply Int.ediv_lt_of_lt_mul hd
    dsimp [n,d]; nlinarith
  have hs2 : 2*h/2=h := by omega
  have ht2 : 2*h*q/2=h*q := Int.ediv_eq_of_eq_mul_right (by norm_num) (by ring)
  have htq : 2*h*q/(2*h)=q := Int.ediv_eq_of_eq_mul_right (by omega) rfl
  have hs4 : 2*h≠4 := by omega
  have ht4 : 2*h*q≠4 := by nlinarith
  have hst : 2*h≤2*h*q := by nlinarith
  have hcon : constructor 4 (2*h) (2*h*q)=chooseEar 4 (2*h) (2*h*q) 7
      ⟨q*(h-1),0,0⟩ ⟨0,v,1⟩ := by
    simp only [constructor, hs4,ht4,hst, and_false,false_and,and_true,true_and,
      ite_false,ite_true, hs2,htq] <;> rfl
  rw [hcon]
  have htail : n-d*v≤h*(2*h*q+1) := by
    have hc := mul_nonneg (show 0≤h-8 by omega) (show 0≤h*q by nlinarith)
    dsimp [d] at hv
    nlinarith [hv.2]
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,?_,?_⟩
    · dsimp [Bounded,makePlan]
      rw [hs2,ht2]
      exact ⟨mul_nonneg (by omega) (by omega), by nlinarith,
        by omega, by omega, by omega, by omega⟩
    · dsimp [Bounded,makePlan]
      rw [hs2,ht2]
      exact ⟨by omega, mul_pos (by omega) (by omega), hv0, hvc, by omega, by omega⟩
    · simp [Separate,makePlan]
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [hs2,ht2]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [hs2,ht2] at he
      dsimp [n,d] at hv htail
      norm_num at *
      repeat' constructor
      all_goals nlinarith [mul_nonneg (show 0≤h-8 by omega) (show 0≤q-1 by omega)]


end D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
