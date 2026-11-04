/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAAdjacent
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAAdjacent
   mirror-E: none(waiver:private-mask-certificates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Adjacent two-chain masks and unbounded ceiling estimates. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! Explicit mask certificates for one strict physical chamber. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
open ThreeNegativeMinimumTwoJointLift
open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.agb Order.bag Ear Ear.p Ear.q Ear.t Plan Plan.p Plan.t Plan.order Plan.ear
  atNegative Order.first Order.middle Order.last
  oldMass newMass cap oldHeight newHeight Bounded Seams Certificate makePlan Separate
  disjoint_low_bits
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks

private theorem adjacent_floor_bounds (n d : ℤ) (hd : 0 < d) :
    d * (n / d) ≤ n ∧ n < d * (n / d + 1) := by
  have h0 := Int.emod_nonneg n (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos n hd
  have he := Int.mul_ediv_add_emod n d
  constructor <;> nlinarith

set_option maxHeartbeats 1600000 in
-- Unbounded Euclidean division and polynomial bounds require the larger elaboration budget.
private theorem adjacent_head (s q : ℤ) (hs : 8 ≤ s) (hq : 2 ≤ q)
    (hs2 : 2 * (s / 2) = s) (hq2 : 2 * (q / 2) = q)
    (region : q ≤ s / 2 ∨ q = s ∨ q = 2 * s ∨ 4 * s ≤ q) :
    let t := s * q
    let u := 1 + 2 * t * (s + 1)
    let L := 1 + s + s * t
    let C := s * t * t - 1
    ∃ p w : ℤ, 0 ≤ p ∧ p < t / 2 ∧ 0 ≤ w ∧ w < q ∧
      (q=2 → w=0) ∧ 0 ≤ C - u * p - L * w ∧
      2 * (C - u * p - L * w) + (s + 1) * w ≤ s * t + s / 2 - 1 := by
  dsimp only
  let t := s * q
  let u := 1 + 2 * t * (s + 1)
  let L := 1 + s + s * t
  let C := s * t * t - 1
  let M := (s - 1) * (q / 2)
  let G0 := s * q * q - (s - 1) * (q / 2) - 1
  have hu : 0 < u := by dsimp [u,t]; positivity
  have hL : 0 < L := by dsimp [L,t]; positivity
  have ht : 2 * s ≤ t := by dsimp [t]; nlinarith
  have ht2 : 2 * (t / 2)=t := by
    have he : t=2 * ((s / 2) * q) := by
      dsimp [t]
      nlinarith only [show q * (2 * (s / 2) - s)=0 by rw [hs2]; ring]
    rw [he]; omega
  have hM2 : 2 * M=(s - 1) * q := by
    dsimp [M]
    nlinarith [show (s - 1) * (2 * (q / 2) - q)=0 by rw [hq2]; ring]
  have hG0 : 0 ≤ G0 := by
    dsimp [G0,M] at hM2 ⊢
    nlinarith [mul_nonneg (show 0≤s * q by positivity) (show 0≤q - 1 by omega)]
  have hCM : C=u * M + G0 := by
    dsimp [C,u,M,G0,t]
    dsimp [M] at hM2
    linear_combination - s * q * (s + 1) * hM2
  have hcap (p w R : ℤ) (hp : 0 ≤ p) (hw : 0 ≤ w) (hR : 0 ≤ R)
      (he : C=u * p + L * w + R) : p < t / 2 := by
    have hx : u * p ≤ C := by nlinarith [mul_nonneg hL.le hw]
    have hc : C < u * (t / 2) := by
      dsimp [C,u]
      nlinarith [show s * t * (2 * (t / 2) - t)=0 by rw [ht2]; ring,
        show t * (2 * (t / 2) - t)=0 by rw [ht2]; ring, sq_nonneg t]
    exact (mul_lt_mul_iff_of_pos_left hu).mp (lt_of_le_of_lt hx hc)
  rcases region with hsmall | hsame | hdouble | hlarge
  · have hp : 0 ≤ M := by
      dsimp [M]; exact mul_nonneg (by omega) (by omega)
    have he : C - u * M - L * 0=G0 := by nlinarith
    refine ⟨M,0,hp,hcap M 0 G0 hp (by omega) hG0 (by nlinarith),by omega,by omega,
      by simp,by nlinarith only [hCM,hG0],?_⟩
    rw [he]
    have hprod := mul_nonneg (show 0≤s * q by dsimp [t] at * ; nlinarith)
      (show 0≤s - 2 * q by omega)
    dsimp [G0,t] at * 
    nlinarith
  · subst q
    have hp : 0 ≤ M - 1 := by dsimp [M]; nlinarith
    let R := (3 * s * s - 5 * s) / 2 - 3
    have hR2 : 2 * R=3 * s * s - 5 * s - 6 := by
      dsimp [R]
      have he : 3 * s * s - 5 * s=2 * ((3 * s - 5) * (s / 2)) := by nlinarith
      rw [he]; omega
    have hR : 0 ≤ R := by nlinarith [sq_nonneg (s - 8)]
    have he : C=u * (M - 1) + L * 3 + R := by
      dsimp [C,u,L,M,t] at * 
      nlinarith [show s * (s * s + s) * (2 * (s / 2) - s)=0 by rw [hs2]; ring]
    have hw : 3 < s := by omega
    refine ⟨M - 1,3,hp,hcap _ _ R hp (by omega) hR he,by omega,hw,by omega,by nlinarith only [he,hR],?_⟩
    have hprod := mul_nonneg (show 0≤s - 8 by omega) (mul_self_nonneg s)
    dsimp [t] at * 
    nlinarith [sq_nonneg (s - 8)]
  · subst q
    have hq2' : (2 * s) / 2=s := by omega
    have hp : 0 ≤ M - 1 := by dsimp [M]; rw [hq2']; nlinarith
    let R := 3 * s * s - 3 * s - 4
    have hR : 0 ≤ R := by dsimp [R]; nlinarith [sq_nonneg (s - 8)]
    have he : C=u * (M - 1) + L * 4 + R := by
      dsimp [C,u,L,M,R,t]
      rw [hq2']; ring
    refine ⟨M - 1,4,hp,hcap _ _ R hp (by omega) hR he,by omega,by omega,by omega,
      by nlinarith only [he,hR],?_⟩
    have hprod := mul_nonneg (show 0≤s - 8 by omega) (mul_self_nonneg s)
    dsimp [R,t] at * 
    nlinarith [sq_nonneg (s - 8)]
  · let e := 2 * s * (q - 1) - 1
    let G := C % u
    let i := (u - G - 1) / e + 1
    let w := 2 * i
    let p := C / u - i + 1
    let R := G + e * i - u
    have he : 0 < e := by dsimp [e]; nlinarith
    have hG : 0 ≤ G ∧ G < u := ⟨Int.emod_nonneg _ (ne_of_gt hu),Int.emod_lt_of_pos _ hu⟩
    have hi := adjacent_floor_bounds (u - G - 1) e he
    have hi1 : 1 ≤ i := by
      have hf := Int.ediv_nonneg (show 0≤u - G - 1 by omega) he.le
      dsimp [i]; omega
    have hue : u < (s + 2) * e := by
      dsimp [u,t,e]
      obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp hs
      obtain ⟨y,hy,hqy⟩ := le_iff_exists_nonneg_add.mp hlarge
      rw [← hqy]
      nlinarith [mul_nonneg hx hy, sq_nonneg x]
    have hi2 : i ≤ s + 2 := by dsimp [i] at * ; nlinarith
    have hR : 0 ≤ R ∧ R < e := by dsimp [R,i]; constructor <;> nlinarith
    have hF := adjacent_floor_bounds C u hu
    have hFM : M ≤ C / u := by
      by_contra hn
      have hp := mul_le_mul_of_nonneg_left (show C / u + 1≤M by omega) hu.le
      nlinarith
    have hp0 : 0 ≤ p := by
      have hm : s + 1 ≤ M := by
        dsimp [M]
        have hp := mul_nonneg (show 0≤s - 1 by omega) (show 0≤q - 4 * s by omega)
        nlinarith [sq_nonneg (s - 8)]
      dsimp [p]; omega
    have hw0 : 0 ≤ w := by dsimp [w]; omega
    have hwq : w < q := by dsimp [w]; omega
    have hce : C=u * p + L * w + R := by
      have hmod := Int.mul_ediv_add_emod C u
      change u * (C / u) + G=C at hmod
      dsimp [p,w,R,e,u,L,t] at * 
      nlinarith
    have hbudget : 2 * R + (s + 1) * w ≤ 4 * s * q + 2 * s * s + 2 * s := by
      have hi2mul := mul_le_mul_of_nonneg_left hi2 (show 0≤s + 1 by omega)
      dsimp [w,e] at * 
      nlinarith
    have hgap : 4 * s * q + 2 * s * s + 2 * s < s * t + s / 2 - 1 := by
      dsimp [t]
      obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp hs
      obtain ⟨y,hy,hqy⟩ := le_iff_exists_nonneg_add.mp hlarge
      rw [← hqy]
      nlinarith [mul_nonneg hx hy, mul_nonneg (mul_self_nonneg x) hy, sq_nonneg x,
        mul_nonneg hx (mul_self_nonneg x)]
    refine ⟨p,w,hp0,hcap p w R hp0 hw0 hR.1 hce,hw0,hwq,by omega,?_,?_⟩
    · nlinarith only [hce,hR.1]
    · nlinarith only [hce,hbudget,hgap]

set_option maxHeartbeats 1600000 in
-- Unbounded Euclidean division and polynomial bounds require the larger elaboration budget.
private theorem adjacent_certificate (b d : ℕ) (hb : 3 ≤ b) (hd : 1 ≤ d) :
    let s : ℤ := 2 ^ b
    let q : ℤ := 2 ^ d
    let t := s * q
    ∃ plan : Plan, Certificate (2 * t) s t plan := by
  dsimp only
  generalize hsdef : (2:ℤ) ^ b=s
  generalize hqdef : (2:ℤ) ^ d=q
  let t := s * q
  have hs : 8 ≤ s := by rw [←hsdef]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hb)
  have hq : 2 ≤ q := by rw [←hqdef]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hd)
  have hs2 : 2 * (s / 2)=s := by
    have hf : s=2 * (2:ℤ) ^ (b - 1) := by
      calc
        s = (2:ℤ) ^ b := hsdef.symm
        _ = 2 ^ ((b - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    rw [hf]; omega
  have hq2 : 2 * (q / 2)=q := by
    have hf : q=2 * (2:ℤ) ^ (d - 1) := by
      calc
        q = (2:ℤ) ^ d := hqdef.symm
        _ = 2 ^ ((d - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    rw [hf]; omega
  have region : q≤s / 2 ∨ q=s ∨ q=2 * s ∨ 4 * s≤q := by
    rcases lt_trichotomy d b with hdb | heq | hdb
    · left
      have hs' : s=2 * (2:ℤ) ^ (b - 1) := by
        calc
          s = (2:ℤ) ^ b := hsdef.symm
          _ = 2 ^ ((b - 1) + 1) := by congr 1; omega
          _ = _ := by rw [pow_succ]; ring
      have hp : q≤(2:ℤ) ^ (b - 1) := by
        rw [←hqdef]
        exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (show d≤b - 1 by omega))
      omega
    · right; left; rw [←hsdef,←hqdef,heq]
    · by_cases he : d=b + 1
      · right; right; left
        rw [←hsdef,←hqdef,he,pow_succ]; ring
      · right; right; right
        have hp : (2:ℤ) ^ (b + 2)≤q := by
          rw [←hqdef]
          exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (show b + 2≤d by omega))
        rw [←hsdef]
        simpa [pow_add,mul_comm] using hp
  obtain ⟨p,w,hp0,hpt,hw0,hwq,hw2,hR,hbudget⟩ := adjacent_head s q hs hq hs2 hq2 region
  let h := if q=2 then 3 else q
  let z := t - h
  have ht : 2 * s≤t := by dsimp [t]; nlinarith
  have ht2 : 2 * (t / 2)=t := by
    have he : t=2 * ((s / 2) * q) := by
      dsimp [t]
      nlinarith only [show q * (2 * (s / 2) - s)=0 by rw [hs2]; ring]
    rw [he]; omega
  have hr2 : (2 * t) / 2=t := by omega
  have hqt : q<t := by
    dsimp [t]
    nlinarith only [mul_pos (show 0<s - 1 by omega) (show 0<q by omega)]
  have hz : 0≤z ∧ z<t := by
    dsimp [z,h,t]
    split_ifs with he
    · rw [he]; omega
    · have hp := mul_pos (show 0<s - 1 by omega) (show 0<q by omega)
      constructor <;> nlinarith only [hp,hq,hs]
  have hq4 : q=2 ∨ 4≤q := by
    by_cases he : d=1
    · left; rw [←hqdef,he]; norm_num
    · right
      rw [←hqdef]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (show 2≤d by omega))
  have hdis : Disjoint w.toNat.bitIndices.toFinset z.toNat.bitIndices.toFinset := by
    by_cases he : q=2
    · rw [hw2 he]; simp
    · have hz' : z=q * (s - 1) := by dsimp [z,h,t]; rw [ite_eq_right he]; ring
      have hnat : z.toNat=2 ^ d * (s - 1).toNat := by
        rw [hz',Int.toNat_mul (by omega) (by omega)]
        rw [←hqdef]; norm_cast
      rw [hnat]
      apply disjoint_low_bits
      have hwn : (w.toNat:ℤ)=w := Int.toNat_of_nonneg hw0
      have hbound : (w.toNat:ℤ)<(2:ℤ) ^ d := by rw [hwn,hqdef]; exact hwq
      exact_mod_cast hbound
  let C := (2 * t) * s * (t / 2) - 1
  let H := C - (s + 1) * t
  let K := 2 * H + (s + 1) * t + 1
  let L := 1 + s + s * t
  let delta := H - L * z
  let D := K - (2 * L - s - 1) * z
  have htail : 0≤delta ∧ D≤(2 * t + 1) * t := by
    dsimp [delta,H,C,D,K,L,z,h]
    rcases hq4 with he | he
    · rw [ite_eq_left he]
      dsimp [t]
      rw [he]
      have hdiv : s * 2 / 2=s := by omega
      rw [hdiv]
      constructor <;> nlinarith only [hs,sq_nonneg (s - 8)]
    · rw [ite_eq_right (by omega)]
      dsimp [t] at * 
      have hp := mul_nonneg (show 0≤s * q by positivity) (show 0≤s * q - 2 * s - 1 by nlinarith [mul_nonneg (show 0≤s by omega) (show 0≤q - 4 by omega)])
      constructor <;> nlinarith [show s * q * s * (2 * (s * q / 2) - s * q)=0 by rw [ht2]; ring]
  change ∃ plan : Plan, Certificate (2 * t) s t plan
  refine ⟨makePlan 0 Order.bag Ear.q (Mask.mk p 0 w) (Mask.mk 0 0 z),?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2]
    exact ⟨hp0,hpt,by omega,by omega,hw0,lt_trans hwq hqt⟩
  · dsimp [Bounded,makePlan]; rw [hr2]
    exact ⟨by omega,by change 0<t / 2; omega,by omega,by omega,hz.1,hz.2⟩
  · simpa [Separate,makePlan] using hdis
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    norm_num
    try rw [hr2]
    dsimp [C,H,K,L,delta,D] at htail
    have hLp : 0≤(1 + s + s * t) * w := mul_nonneg (by positivity) hw0
    have hLz : 0≤(s + 1) * z := mul_nonneg (by omega) hz.1
    have he : (2 * t) * s * (t / 2) - 1=s * t * t - 1 := by nlinarith [show s * t * (2 * (t / 2) - t)=0 by rw [ht2]; ring]
    repeat' constructor
    all_goals nlinarith only [hR,hbudget,htail.1,htail.2,hLp,hLz,he,
      hs2,ht2,hs,hq,hw0,hz.1,
      show (t + 1) * (2 * (s / 2) - s)=0 by rw [hs2]; ring,
      show (2 * t + 1) * (2 * (t / 2) - t)=0 by rw [ht2]; ring,
      show 0≤(s + 1) * t by positivity]

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
