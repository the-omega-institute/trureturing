/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoMasks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeMinimumTwoMasks
   mirror-E: none(waiver:private-constructor-implementation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact physical masks and dyadic rows for the minimum-two constructor. -/
module
import Mathlib.Data.Nat.Bitwise
import D5.S3.Combinatorics.Circle.ThreeBitSource

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

private structure Mask where
  u : ℤ
  v : ℤ
  w : ℤ

private inductive Negative | alpha | beta | gamma
  deriving DecidableEq
private inductive Order | abg | bag | gba | agb | bga | gab
  deriving DecidableEq
private inductive Ear | p | q | t
  deriving DecidableEq

private def atNegative {α : Type* } (A B G : α) : Negative → α
  | .alpha => A | .beta => B | .gamma => G
private def Order.first : Order → Negative
  | .abg | .agb => .alpha
  | .bag | .bga => .beta
  | .gba | .gab => .gamma
private def Order.middle : Order → Negative
  | .abg | .gba => .beta
  | .bag | .gab => .alpha
  | .agb | .bga => .gamma
private def Order.last : Order → Negative
  | .abg | .bag => .gamma
  | .gba | .bga => .alpha
  | .agb | .gab => .beta

private def oldMass (r s t : ℤ) (m : Mask) : ℤ :=
  (1 + r + r * s) * m.u + (1 + t + t * r) * m.v + (1 + s + s * t) * m.w
private def newMass (r s t : ℤ) (m : Mask) : ℤ :=
  (2 * (1 + r + r * s)) * m.u + (2 * (1 + t + t * r) - 1) * m.v + (2 * (1 + s + s * t) - s - 1) * m.w
private def cap (r s t : ℤ) : ℤ := r * s * (t / 2) - 1
private def oldHeight (r s t : ℤ) : Negative → ℤ :=
  atNegative (cap r s t - (r + 1) * (t / 2))
    (cap r s t - (t + 1) * (s / 2)) (cap r s t - (s + 1) * (r / 2))
private def newHeight (r s t : ℤ) (n : Negative) : ℤ :=
  2 * oldHeight r s t n + atNegative 1 (s / 2 + 1) ((s + 1) * (r / 2) + 1) n

private structure Plan where
  row : ℕ
  order : Order
  ear : Ear
  p : Mask
  t : Mask

private def makePlan (row : ℕ) (o : Order) (e : Ear) (p t : Mask) : Plan :=
  ⟨row,o,e,p,t⟩
private def chooseEar (r s t : ℤ) (row : ℕ) (p z : Mask) : Plan :=
  makePlan row .abg
    (if newHeight r s t .gamma - newMass r s t z ≤ s * t + s / 2 then .q else .t) p z

/-- Each branch fixes physical masks; the middle block is their physical complement. -/
private def constructor (r s t : ℤ) : Plan :=
  if r = 4 ∧ s = 4 ∧ t = 4 then makePlan 0 .abg .p ⟨1,0,0⟩ ⟨0,0,1⟩
  else if r = 4 ∧ s = 4 then
    if t = 8 then makePlan 1 .bag .q ⟨1,1,0⟩ ⟨2,0,0⟩
    else makePlan 2 .bag .q ⟨t / 16,1,0⟩ ⟨t / 8,0,1⟩
  else if r = 4 ∧ t = 4 then makePlan 3 .gba .q ⟨0,s / 8,1⟩ ⟨1,s / 8 - 1,0⟩
  else if s = 4 ∧ t = 4 then
    if r = 8 then makePlan 4 .bag .q ⟨1,0,1⟩ ⟨0,0,2⟩
    else if r = 16 then makePlan 5 .agb .q ⟨1,0,1⟩ ⟨0,1,2⟩
    else makePlan 6 .agb .q ⟨1,0,r / 16⟩ ⟨0,1,5 * r / 32⟩
  else if r = 4 then
    if s ≤ t then chooseEar r s t 7 ⟨(t / s) * (s / 2 - 1),0,0⟩
      ⟨0,(s * t - 3 * s - 4) / (5 * t + 1),1⟩
    else if s = 2 * t then
      if t = 8 then makePlan 9 .abg .q ⟨0,6,0⟩ ⟨1,0,1⟩
      else chooseEar r s t 8 ⟨t / 2 - 1,1,0⟩ ⟨0,t / 4,1⟩
    else if s = 4 * t then chooseEar r s t 10 ⟨t / 2 - 3,9,0⟩
      ⟨0,if t = 8 then 2 else if t = 16 then 6 else t / 2,1⟩
    else makePlan 11 .bga .q ⟨t / 8,0,1⟩
      ⟨0,(oldHeight r s t .alpha) / (1 + t + t * r),0⟩
  else if s = 4 then
    if 2 * r ≤ t then makePlan 12 .bag .q ⟨cap r s t / (1 + r + r * s),0,0⟩ ⟨0,0,r / 2 - 1⟩
    else if t = r then makePlan 13 .bag .p ⟨0,0,r / 2 - 1⟩
      ⟨oldHeight r s t .gamma / (1 + r + r * s),0,0⟩
    else if r = 2 * t then
      if t = 8 then makePlan 15 .agb .q ⟨2,0,1⟩ ⟨1,0,4⟩
      else makePlan 14 .agb .t ⟨3 * t / 8,0,0⟩ ⟨1,0,t - 5⟩
    else makePlan 16 .agb .t ⟨3 * t / 8,0,0⟩
      ⟨0,0,(4 * r * t - 5 * r - 4 * t - 4) / (8 * t + 5)⟩
  else if r = 8 ∧ s = 8 then makePlan 17 .abg .t ⟨1,1,0⟩ ⟨0,0,2⟩
  else if (r = 8 ∧ s = 16) ∨ (r = 16 ∧ s = 8) then
    makePlan 18 .bga .q ⟨1,1,1⟩ ⟨0,2,2⟩
  else if r = 16 ∧ s = 16 then makePlan 19 .bga .q ⟨1,3,0⟩ ⟨0,4,2⟩
  else if s = 8 then makePlan 20 .gab .q ⟨1,0,5 * r / 32⟩ ⟨0,3,r / 16⟩
  else if s = 16 then
    let yz := if r = 32 then (5,0) else if r = 64 then (10,1) else (19 * r / 128,r / 32)
    makePlan 21 .gab .q ⟨1,0,yz.1⟩ ⟨0,7,yz.2⟩
  else if r = 8 then makePlan 22 .bga .q ⟨1,3 * s / 16,0⟩
    ⟨0,if s = 32 then 0 else s / 64,3⟩
  else if r = 16 then makePlan 23 .bga .q ⟨1,7 * s / 32,0⟩
    ⟨0,if s = 32 then 0 else s / 64,6⟩
  else if r = 32 then
    if s = 32 ∨ s = 64 then makePlan 24 .agb .q ⟨1,s / 4 - 1,0⟩ ⟨0,0,12⟩
    else makePlan 25 .bga .q ⟨1,29 * s / 128,0⟩ ⟨0,s / 64,12⟩
  else if r = s ∨ 2 * r = s then makePlan 26 .agb .q ⟨1,s / 4 - 1,0⟩ ⟨0,0,25 * r / 64⟩
  else if r = 2 * s then makePlan 27 .gab .q ⟨1,0,3 * r / 16⟩ ⟨0,s / 2 - 1,0⟩
  else if 4 * s ≤ r then makePlan 28 .agb .q
    ⟨1,s / 4 - 1,-(-(2 * r + 2 - 9 * s / 4) / (9 * s + 1))⟩ ⟨0,0,25 * r / 64⟩
  else makePlan 29 .bga .q ⟨1,(r * s - r - 2) / (4 * r + 5),0⟩ ⟨0,0,25 * r / 64⟩

private def Bounded (r s t : ℤ) (m : Mask) : Prop :=
  0 ≤ m.u ∧ m.u < t / 2 ∧ 0 ≤ m.v ∧ m.v < s / 2 ∧ 0 ≤ m.w ∧ m.w < r / 2
private def Separate (p z : Mask) : Prop :=
  Disjoint p.u.toNat.bitIndices.toFinset z.u.toNat.bitIndices.toFinset ∧ Disjoint p.v.toNat.bitIndices.toFinset z.v.toNat.bitIndices.toFinset ∧ Disjoint p.w.toNat.bitIndices.toFinset z.w.toNat.bitIndices.toFinset

private def Seams (r s t : ℤ) (p : Plan) : Prop :=
  let H := oldHeight r s t
  let K := newHeight r s t
  let x := oldMass r s t p.p
  let z := oldMass r s t p.t
  let xn := newMass r s t p.p + if p.ear = .p then 1 + r + r * s else 0
  let zn := newMass r s t p.t + if p.ear = .t then 1 + r + r * s else 0
  H p.order.first ≤ x ∧ x ≤ cap r s t ∧ z ≤ H p.order.last ∧ H p.order.middle + H p.order.last - z ≤ cap r s t ∧ K p.order.first ≤ xn ∧ xn ≤ 2 * cap r s t + 1 ∧ zn ≤ K p.order.last ∧ K p.order.middle + K p.order.last - zn ≤ 2 * cap r s t + 1

private def Certificate (r s t : ℤ) (p : Plan) : Prop :=
  Bounded r s t p.p ∧ Bounded r s t p.t ∧ Separate p.p p.t ∧ Seams r s t p

private theorem disjoint_scaled_bits (d x y : ℕ)
    (h : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint (2 ^ d * x).bitIndices.toFinset (2 ^ d * y).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [Nat.bitIndices_two_pow_mul,List.mem_toFinset,List.mem_map] at hi hj
  obtain ⟨j,hjmem,hji⟩ := hi
  obtain ⟨l,hl,hli⟩ := hj
  have he : j = l := by omega
  subst l
  exact Finset.disjoint_left.mp h (by simpa using hjmem) (by simpa using hl)

private theorem disjoint_low_bits (d x y : ℕ) (hx : x < 2 ^ d) :
    Disjoint x.bitIndices.toFinset (2 ^ d * y).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hb : x.testBit i = true := Nat.mem_bitIndices.mp (List.mem_toFinset.mp hi)
  simp only [Nat.bitIndices_two_pow_mul,List.mem_toFinset,List.mem_map] at hj
  obtain ⟨j,_,hji⟩ := hj
  have hi0 : d ≤ i := by omega
  have hxi : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi0)
  rw [Nat.testBit_eq_false_of_lt hxi] at hb
  contradiction

private theorem axes_two (d : ℕ) :
    Certificate 4 4 (16 * (2 : ℤ) ^ d) (constructor 4 4 (16 * (2 : ℤ) ^ d)) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Nat.one_le_two_pow)
  have h4 : 16 * q ≠ 4 := by omega
  have h8 : 16 * q ≠ 8 := by omega
  have hd16 : 16 * q / 16 = q := by omega
  have hd8 : 16 * q / 8 = 2 * q := by omega
  have hc : constructor 4 4 (16 * q) = makePlan 2 .bag .q ⟨q,1,0⟩ ⟨2 * q,0,1⟩ := by
    simp [constructor,h4,h8,hd16,hd8]
  change Certificate 4 4 (16 * q) (constructor 4 4 (16 * q))
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    have hbits : Disjoint q.toNat.bitIndices.toFinset (2 * q).toNat.bitIndices.toFinset := by
      have hdis : Disjoint (1 : ℕ).bitIndices.toFinset (2 : ℕ).bitIndices.toFinset := by decide
      have hqnat : q.toNat = 2 ^ d := by
        dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)] <;> rfl
      rw [Int.toNat_mul (by norm_num) (by omega), hqnat]
      change Disjoint (2 ^ d).bitIndices.toFinset (2 * 2 ^ d).bitIndices.toFinset
      simpa only [mul_one, Nat.mul_comm] using disjoint_scaled_bits d 1 2 hdis
    exact ⟨hbits,by simp,by simp⟩
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private theorem axes_three (d : ℕ) :
    Certificate 4 (8 * (2 : ℤ) ^ d) 4 (constructor 4 (8 * (2 : ℤ) ^ d) 4) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 8 * q ≠ 4 := by omega
  have hd8 : 8 * q / 8 = q := by omega
  have hc : constructor 4 (8 * q) 4 = makePlan 3 .gba .q ⟨0,q,1⟩ ⟨1,q - 1,0⟩ := by
    simp [constructor,h4,hd8]
  change Certificate 4 (8 * q) 4 (constructor 4 (8 * q) 4)
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,?_,by simp⟩
    have hh : (q - 1).toNat < 2 ^ d := by
      have he : ((q - 1).toNat : ℤ) = q - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast (show ((q - 1).toNat : ℤ) < (2 : ℤ) ^ d by dsimp [q] at he; omega)
    have hqnat : q.toNat = 2 ^ d := by
      dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)] <;> rfl
    rw [hqnat]
    simpa only [mul_one] using (disjoint_low_bits d (q - 1).toNat 1 hh).symm
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private theorem axes_six (d : ℕ) :
    Certificate (32 * (2 : ℤ) ^ d) 4 4 (constructor (32 * (2 : ℤ) ^ d) 4 4) := by
  let q : ℤ := 2 ^ d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 32 * q ≠ 4 := by omega
  have h8 : 32 * q ≠ 8 := by omega
  have h16 : 32 * q ≠ 16 := by omega
  have hd16 : 32 * q / 16 = 2 * q := by omega
  have hd32 : 5 * (32 * q) / 32 = 5 * q := by omega
  have hc : constructor (32 * q) 4 4 = makePlan 6 .agb .q ⟨1,0,2 * q⟩ ⟨0,1,5 * q⟩ := by
    simp [constructor,h4,h8,h16,hd16,hd32]
  change Certificate (32 * q) 4 4 (constructor (32 * q) 4 4)
  rw [hc]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Bounded,makePlan]; omega
  · dsimp [Separate,makePlan]
    have hdis : Disjoint (2 : ℕ).bitIndices.toFinset (5 : ℕ).bitIndices.toFinset := by decide
    refine ⟨by simp,by simp,?_⟩
    have hqnat : q.toNat = 2 ^ d := by
      dsimp [q]; rw [Int.toNat_pow_of_nonneg (by norm_num)] <;> rfl
    rw [Int.toNat_mul (by norm_num) (by omega), Int.toNat_mul (by norm_num) (by omega), hqnat]
    change Disjoint (2 * 2 ^ d).bitIndices.toFinset (5 * 2 ^ d).bitIndices.toFinset
    simpa only [Nat.mul_comm] using disjoint_scaled_bits d 2 5 hdis
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    omega

private def exceptionalTriples : List (ℤ × ℤ × ℤ) :=
  [(4,16,8),(4,32,8),(4,64,16),(16,4,8),(8,8,4),
      (8,16,4),(16,8,4),(16,16,4),(32,16,4),(64,16,4),(8,32,4),
      (16,32,4),(32,32,4),(32,64,4),(32,4,8),(8,4,8),(4,8,8)]

private theorem a_two_twice (d : ℕ) :
    Certificate 4 (32 * (2 : ℤ)^d) (16 * (2 : ℤ)^d)
      (constructor 4 (32 * (2 : ℤ)^d) (16 * (2 : ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hs : 32*q≠4 := by omega
  have ht : 16*q≠4 := by omega
  have ht8 : 16*q≠8 := by omega
  have hst : ¬32*q≤16*q := by omega
  have hrel : 32*q=2*(16*q) := by ring
  have ht2 : 16*q/2=8*q := by omega
  have ht4 : 16*q/4=4*q := by omega
  have hs2 : 32*q/2=16*q := by omega
  have hcon : constructor 4 (32*q) (16*q)=
      chooseEar 4 (32*q) (16*q) 8 ⟨8*q-1,1,0⟩ ⟨0,4*q,1⟩ := by
    simp [constructor,hs,ht,hst,ht8,ht2,ht4]
    all_goals simp_all
  change Certificate 4 (32*q) (16*q) (constructor 4 (32*q) (16*q))
  rw [hcon]
  have hsep : Separate (⟨8*q-1,1,0⟩ : Mask) ⟨0,4*q,1⟩ := by
    refine ⟨by simp [Separate],?_,by simp⟩
    have hp : (4*q).toNat=2^(d+2) := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (1:ℕ).bitIndices.toFinset (4*q).toNat.bitIndices.toFinset
    rw [hp]
    simpa only [mul_one] using disjoint_low_bits (d+2) 1 1 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,hsep,?_⟩
    · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
    · dsimp [Bounded,makePlan]; rw [ht2,hs2]; omega
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [ht2,hs2]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [ht2,hs2] at he
      norm_num at *
      constructor <;> try omega
      all_goals repeat' constructor
      all_goals nlinarith [sq_nonneg (q-1)]

private theorem int_scaled_bits (d x y : ℕ)
    (h : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint ((x:ℤ)*2^d).toNat.bitIndices.toFinset
      ((y:ℤ)*2^d).toNat.bitIndices.toFinset := by
  rw [Int.toNat_mul (by positivity) (by positivity),
    Int.toNat_mul (by positivity) (by positivity),
    Int.toNat_pow_of_nonneg (by norm_num)]
  simpa only [Int.toNat_natCast, show (2:ℤ).toNat=2 from rfl, Nat.mul_comm] using disjoint_scaled_bits d x y h

private theorem c_two_small_s_eight (d : ℕ) :
    Certificate (32*(2:ℤ)^d) 8 4 (constructor (32*(2:ℤ)^d) 8 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 32*q≠4 := by omega
  have h8 : 32*q≠8 := by omega
  have h16 : 32*q≠16 := by omega
  have hd16 : 32*q/16=2*q := by omega
  have hd32 : 5*(32*q)/32=5*q := by omega
  have hr2 : 32*q/2=16*q := by omega
  have hcon : constructor (32*q) 8 4=makePlan 20 .gab .q ⟨1,0,5*q⟩ ⟨0,3,2*q⟩ := by
    simp [constructor,h4,h8,h16,hd16,hd32]
  change Certificate (32*q) 8 4 (constructor (32*q) 8 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,by simp,?_⟩
    exact int_scaled_bits d 5 2 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hr2]
    omega

private theorem c_two_small_s_sixteen (d : ℕ) :
    Certificate (128*(2:ℤ)^d) 16 4 (constructor (128*(2:ℤ)^d) 16 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 128*q≠4 := by omega
  have h8 : 128*q≠8 := by omega
  have h16 : 128*q≠16 := by omega
  have h32 : 128*q≠32 := by omega
  have h64 : 128*q≠64 := by omega
  have hd128 : 19*(128*q)/128=19*q := by omega
  have hd32 : 128*q/32=4*q := by omega
  have hr2 : 128*q/2=64*q := by omega
  have hcon : constructor (128*q) 16 4=makePlan 21 .gab .q ⟨1,0,19*q⟩ ⟨0,7,4*q⟩ := by
    simp [constructor,h4,h8,h16,h32,h64,hd128,hd32]
  change Certificate (128*q) 16 4 (constructor (128*q) 16 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,by simp,?_⟩
    exact int_scaled_bits d 19 4 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hr2]
    omega

private theorem c_two_small_r_eight (d : ℕ) :
    Certificate 8 (64*(2:ℤ)^d) 4 (constructor 8 (64*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 64*q≠4 := by omega
  have h8 : 64*q≠8 := by omega
  have h16 : 64*q≠16 := by omega
  have h32 : 64*q≠32 := by omega
  have hd16 : 3*(64*q)/16=12*q := by omega
  have hd64 : 64*q/64=q := by omega
  have hs2 : 64*q/2=32*q := by omega
  have hcon : constructor 8 (64*q) 4=makePlan 22 .bga .q ⟨1,12*q,0⟩ ⟨0,q,3⟩ := by
    simp [constructor,h4,h8,h16,h32,hd16,hd64]
  change Certificate 8 (64*q) 4 (constructor 8 (64*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,?_,by simp⟩
    simpa [q] using int_scaled_bits d 12 1 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem c_two_small_r_sixteen (d : ℕ) :
    Certificate 16 (64*(2:ℤ)^d) 4 (constructor 16 (64*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 64*q≠4 := by omega
  have h8 : 64*q≠8 := by omega
  have h16 : 64*q≠16 := by omega
  have h32 : 64*q≠32 := by omega
  have hd32 : 7*(64*q)/32=14*q := by omega
  have hd64 : 64*q/64=q := by omega
  have hs2 : 64*q/2=32*q := by omega
  have hcon : constructor 16 (64*q) 4=makePlan 23 .bga .q ⟨1,14*q,0⟩ ⟨0,q,6⟩ := by
    simp [constructor,h4,h8,h16,h32,hd32,hd64]
  change Certificate 16 (64*q) 4 (constructor 16 (64*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,?_,by simp⟩
    simpa [q] using int_scaled_bits d 14 1 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem c_two_small_r_thirtytwo (d : ℕ) :
    Certificate 32 (128*(2:ℤ)^d) 4 (constructor 32 (128*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have h4 : 128*q≠4 := by omega
  have h8 : 128*q≠8 := by omega
  have h16 : 128*q≠16 := by omega
  have h32 : 128*q≠32 := by omega
  have h64 : 128*q≠64 := by omega
  have hd128 : 29*(128*q)/128=29*q := by omega
  have hd64 : 128*q/64=2*q := by omega
  have hs2 : 128*q/2=64*q := by omega
  have hcon : constructor 32 (128*q) 4=makePlan 25 .bga .q ⟨1,29*q,0⟩ ⟨0,2*q,12⟩ := by
    simp [constructor,h4,h8,h16,h32,h64,hd128,hd64]
  change Certificate 32 (128*q) 4 (constructor 32 (128*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Bounded,makePlan]; rw [hs2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨by simp,?_,by simp⟩
    exact int_scaled_bits d 29 2 (by decide)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    rw [hs2]
    omega

private theorem a_two_four_times (d : ℕ) :
    Certificate 4 (128*(2:ℤ)^d) (32*(2:ℤ)^d)
      (constructor 4 (128*(2:ℤ)^d) (32*(2:ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hs4 : 128*q≠4 := by omega
  have ht4 : 32*q≠4 := by omega
  have ht8 : 32*q≠8 := by omega
  have ht16 : 32*q≠16 := by omega
  have hst : ¬128*q≤32*q := by omega
  have htwo : 128*q≠2*(32*q) := by omega
  have hfour : 128*q=4*(32*q) := by ring
  have hth : 32*q/2=16*q := by omega
  have hsh : 128*q/2=64*q := by omega
  have hcon : constructor 4 (128*q) (32*q)=
      chooseEar 4 (128*q) (32*q) 10 ⟨16*q-3,9,0⟩ ⟨0,16*q,1⟩ := by
    simp [constructor,hs4,ht4,ht8,ht16,hst,htwo,hth]
    all_goals simp_all
  change Certificate 4 (128*q) (32*q) (constructor 4 (128*q) (32*q))
  rw [hcon]
  have hsep : Separate (⟨16*q-3,9,0⟩ : Mask) ⟨0,16*q,1⟩ := by
    refine ⟨by simp [Separate],?_,by simp⟩
    have hp : (16*q).toNat=2^(d+4) := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (9:ℕ).bitIndices.toFinset (16*q).toNat.bitIndices.toFinset
    rw [hp]
    simpa only [mul_one] using disjoint_low_bits (d+4) 9 1 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)
  unfold chooseEar
  split_ifs with he
  all_goals
    refine ⟨?_,?_,hsep,?_⟩
    · dsimp [Bounded,makePlan]; rw [hth,hsh]; omega
    · dsimp [Bounded,makePlan]; rw [hth,hsh]; omega
    · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
        Order.first,Order.middle,Order.last,atNegative]
      simp only [hth,hsh]
      dsimp [newHeight,oldHeight,oldMass,newMass,cap,atNegative] at he
      simp only [hth,hsh] at he
      norm_num at *
      repeat' constructor
      all_goals nlinarith [sq_nonneg (q-1)]

private theorem b_two_twice (d : ℕ) :
    Certificate (32*(2:ℤ)^d) 4 (16*(2:ℤ)^d)
      (constructor (32*(2:ℤ)^d) 4 (16*(2:ℤ)^d)) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hr4 : 32*q≠4 := by omega
  have ht4 : 16*q≠4 := by omega
  have ht8 : 16*q≠8 := by omega
  have hlarge : ¬2*(32*q)≤16*q := by omega
  have hdiag : 16*q≠32*q := by omega
  have hrel : 32*q=2*(16*q) := by ring
  have hr2 : 32*q/2=16*q := by omega
  have ht2 : 16*q/2=8*q := by omega
  have hmask : 3*(16*q)/8=6*q := by omega
  have hcon : constructor (32*q) 4 (16*q)=
      makePlan 14 .agb .t ⟨6*q,0,0⟩ ⟨1,0,16*q-5⟩ := by
    simp [constructor,hr4,ht4,ht8,hlarge,hdiag,hmask]
    all_goals simp_all
  change Certificate (32*q) 4 (16*q) (constructor (32*q) 4 (16*q))
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Separate,makePlan]
    refine ⟨?_,by simp,by simp⟩
    have hp : (6*q).toNat=2^(d+1)*3 := by
      dsimp [q]
      rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
      norm_num [pow_add]
      ring
    change Disjoint (6*q).toNat.bitIndices.toFinset (1:ℕ).bitIndices.toFinset
    rw [hp]
    exact (disjoint_low_bits (d+1) 1 3 (by
      have h := Nat.one_le_two_pow (n:=d)
      simp only [pow_add] at *
      omega)).symm
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2]
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]

private theorem c_two_equal (d : ℕ) :
    Certificate (64*(2:ℤ)^d) (64*(2:ℤ)^d) 4
      (constructor (64*(2:ℤ)^d) (64*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hr2 : 64*q/2=32*q := by omega
  have hs2 : 64*q/2=32*q := by omega
  have hv : 64*q/4=16*q := by omega
  have hw : 25*(64*q)/64=25*q := by omega
  have hw' : 3*(64*q)/16=12*q := by omega
  have hcon : constructor (64*q) (64*q) 4 =
      makePlan 26 .agb .q ⟨1,16*q-1,0⟩ ⟨0,0,25*q⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2,hs2,hv,hw,hw']
  change Certificate (64*q) (64*q) 4 (constructor (64*q) (64*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,hs2]
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]

private theorem c_two_double_s (d : ℕ) :
    Certificate (64*(2:ℤ)^d) (128*(2:ℤ)^d) 4
      (constructor (64*(2:ℤ)^d) (128*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hr2 : 64*q/2=32*q := by omega
  have hs2 : 128*q/2=64*q := by omega
  have hv : 128*q/4=32*q := by omega
  have hw : 25*(64*q)/64=25*q := by omega
  have hw' : 3*(64*q)/16=12*q := by omega
  have hcon : constructor (64*q) (128*q) 4 =
      makePlan 26 .agb .q ⟨1,32*q-1,0⟩ ⟨0,0,25*q⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2,hs2,hv,hw,hw']
  change Certificate (64*q) (128*q) 4 (constructor (64*q) (128*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,hs2]
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]

private theorem c_two_double_r (d : ℕ) :
    Certificate (64*(2:ℤ)^d) (32*(2:ℤ)^d) 4
      (constructor (64*(2:ℤ)^d) (32*(2:ℤ)^d) 4) := by
  let q : ℤ := 2^d
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have hr2 : 64*q/2=32*q := by omega
  have hs2 : 32*q/2=16*q := by omega
  have hv : 32*q/4=8*q := by omega
  have hw : 25*(64*q)/64=25*q := by omega
  have hw' : 3*(64*q)/16=12*q := by omega
  have hcon : constructor (64*q) (32*q) 4 =
      makePlan 27 .gab .q ⟨1,0,12*q⟩ ⟨0,16*q-1,0⟩ := by
    simp (disch := omega) only [constructor, ite_true, ite_false, ite_eq_left, ite_eq_right, and_true, true_and, true_or, or_true, hr2,hs2,hv,hw,hw']
  change Certificate (64*q) (32*q) 4 (constructor (64*q) (32*q) 4)
  rw [hcon]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · dsimp [Bounded,makePlan]; simp only [hr2,hs2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,hs2]
    norm_num
    repeat' constructor
    all_goals nlinarith [sq_nonneg (q-1)]


end D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
