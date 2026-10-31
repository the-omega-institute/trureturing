/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAFar
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAFar
   mirror-E: none(waiver:private-mask-certificates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded far masks in the strict smallest-b largest-a chamber. -/
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

private theorem floor_bounds (n d : ℤ) (hd : 0 < d) :
    d * (n / d) ≤ n ∧ n < d * (n / d + 1) := by
  have h0 := Int.emod_nonneg n (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos n hd
  have he := Int.mul_ediv_add_emod n d
  constructor <;> nlinarith

set_option maxHeartbeats 1600000 in
-- Unbounded Euclidean division and polynomial bounds require the larger elaboration budget.
private theorem far_certificate (s q h : ℤ) (hs : 8 ≤ s) (hq : 1 ≤ q) (hh : 1 ≤ h)
    (hs2 : 2 * (s / 2) = s) :
    let t := 2 * s * q
    let r := 4 * t * h
    let u := 1 + r + r * s
    let L := 1 + s + s * t
    let H := oldHeight r s t Negative.beta
    let z := (2 * H + s / 2 + 1 - u) / (2 * L - s - 1)
    Certificate r s t (makePlan 0 Order.agb Ear.t (Mask.mk ((s - 1) * q) 0 0) (Mask.mk 0 0 z)) := by
  dsimp only
  generalize htdef : 2 * s * q = t
  generalize hrdef : 4 * t * h = r
  let u := 1 + r + r * s
  let L := 1 + s + s * t
  let C := r * s * (t / 2) - 1
  let H := C - (t + 1) * (s / 2)
  let lam := 2 * L - s - 1
  let Y := 2 * H + s / 2 + 1 - u
  let z := Y / lam
  let R := Y - lam * z
  let delta := H - L * z
  have ht : 2 * s ≤ t := by nlinarith [mul_nonneg (show 0≤s by omega) (show 0≤q - 1 by omega)]
  have hr : 4 * t ≤ r := by nlinarith [mul_nonneg (show 0≤t by omega) (show 0≤h - 1 by omega)]
  have htHalf : t / 2=s * q := by
    have he : t=2 * (s * q) := by nlinarith only [htdef]
    rw [he]; omega
  have hrHalf : r / 2=2 * t * h := by
    have he : r=2 * (2 * t * h) := by nlinarith only [hrdef]
    rw [he]; omega
  have ht2 : 2 * (t / 2)=t := by rw [htHalf]; nlinarith only [htdef]
  have hr2 : 2 * (r / 2)=r := by rw [hrHalf]; nlinarith only [hrdef]
  have hC : 2 * C=r * s * t - 2 := by
    dsimp [C]
    nlinarith only [show r * s * (2 * (t / 2) - t)=0 by rw [ht2]; ring]
  have hH : 2 * H=2 * C - (t + 1) * s := by
    dsimp [H]
    nlinarith only [show (t + 1) * (2 * (s / 2) - s)=0 by rw [hs2]; ring]
  have hs0 : 0 ≤ s / 2 := by omega
  have ht0 : 0 < t := by omega
  have hr0 : 0 < r := by omega
  have hL : 0 < L := by dsimp [L]; positivity
  have hlam : 0 < lam := by dsimp [lam,L]; nlinarith
  have hYe : Y=r * (s * t - s - 1) - s * t - s / 2 - 2 := by
    dsimp [Y,u]
    nlinarith only [hH,hC,hs2]
  have hY : 0 ≤ Y := by
    have hp : 0 ≤ r * (s * t - s - 1) - s * t - s - 2 := by
      obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp hs
      obtain ⟨y,hy,hty⟩ := le_iff_exists_nonneg_add.mp ht
      obtain ⟨v,hv,hrv⟩ := le_iff_exists_nonneg_add.mp hr
      rw [← hrv,← hty]
      ring_nf
      positivity
    nlinarith only [hYe,hp,hs2,hs]
  have hz0 : 0 ≤ z := Int.ediv_nonneg hY hlam.le
  have hz := floor_bounds Y lam hlam
  change lam * z ≤ Y ∧ Y < lam * (z + 1) at hz
  have hR : 0 ≤ R ∧ R < lam := by dsimp [R]; constructor <;> nlinarith
  have hzr : z < r / 2 := by
    have hEe : 2 * (lam * (r / 2) - Y)=3 * r * (s + 1) + lam + 3 := by
      dsimp [lam,L,Y,H,C,u]
      linear_combination (2 * L - s - 1) * hr2 - 2 * r * s * ht2 + (2 * t + 1) * hs2
    have hE : 0 < lam * (r / 2) - Y := by
      nlinarith [mul_pos hr0 (show 0<s + 1 by omega)]
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (show r / 2 ≤ z by omega) hlam.le
    omega
  have hdel : 0 < 2 * delta ∧ 2 * delta < u - 1 := by
    let M := L * (u - s / 2 - 1) - H * (s + 1)
    have hid : lam * delta = M + L * R := by
      dsimp [lam,delta,M,R,Y]; ring
    have hM : 2 * M = (s + 1) * (r * s * t - 1 + 2 * u) + L := by
      dsimp [M,H,C,L,u]
      linear_combination - r * s * (s + 1) * ht2 + t * hs2
    have hM0 : 0 < M := by
      have hu0 : 0 < u := by dsimp [u]; positivity
      have hn0 : 0 < r * s * t - 1 := by
        have hrs : 1≤r * s := by nlinarith [mul_pos hr0 (show 0<s by omega)]
        have hprod := mul_le_mul_of_nonneg_right hrs ht0.le
        nlinarith
      nlinarith [mul_pos (show 0<s + 1 by omega) (show 0<r * s * t - 1 + 2 * u by omega)]
    have hd0 : 0 < 2 * delta := by
      have hp := mul_nonneg hL.le hR.1
      nlinarith
    refine ⟨hd0, ?_⟩
    by_cases corner : q=1 ∧ h=1
    · obtain ⟨rfl,rfl⟩ := corner
      have ht' : t=2 * s := by nlinarith only [htdef]
      have hr' : r=8 * s := by nlinarith only [hrdef,ht']
      have htHalf' : t / 2=s := by rw [ht']; omega
      have hrHalf' : r / 2=4 * s := by rw [hr']; omega
      have hz' : z=r / 2 - 4 := by
        apply (Int.ediv_eq_iff_of_pos hlam).mpr
        have hrem2 : 2 * (Y - lam * (r / 2 - 4))=(s - 4) * (4 * s - 1) := by
          rw [hYe]
          dsimp [lam,L]
          rw [hrHalf',ht',hr']
          nlinarith only [hs2]
        have hrem0 : 0 ≤ Y - lam * (r / 2 - 4) := by
          have hp := mul_nonneg (show 0≤s - 4 by omega) (show 0≤4 * s - 1 by omega)
          nlinarith only [hrem2,hp]
        have hlcorner : lam=4 * s * s + s + 1 := by
          dsimp [lam,L]; rw [ht']; ring
        have hremLt : Y - lam * (r / 2 - 4)<lam := by
          nlinarith only [hrem2,hlcorner,hs,sq_nonneg (s - 4)]
        constructor <;> nlinarith only [hrem0,hremLt]
      have hde : 2 * delta=6 * s * s - s + 6 := by
        dsimp [delta]
        rw [hz',hrHalf']
        dsimp [L]
        rw [ht'] at hH hC
        rw [hr'] at hC
        rw [ht']
        nlinarith only [hH,hC]
      dsimp [u]
      rw [hr']
      nlinarith [sq_nonneg (s - 4)]
    · have hd : 0 < r * (s + 1) * (s * t - s - 1) - L * (2 * lam + 1) - s - 1 := by
        rcases le_or_gt 2 q with hq2 | hq2
        · have ht4 : 4 * s ≤ t := by nlinarith [mul_nonneg (show 0≤s by omega) (show 0≤q - 2 by omega)]
          obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp (show (4:ℤ) ≤ s by omega)
          obtain ⟨y,hy,hty⟩ := le_iff_exists_nonneg_add.mp ht4
          obtain ⟨v,hv,hrv⟩ := le_iff_exists_nonneg_add.mp hr
          dsimp [lam,L]
          rw [← hrv,← hty]
          ring_nf
          positivity
        · have hq1 : q=1 := by omega
          have hh2 : 2 ≤ h := by omega
          have hr8 : 8 * t ≤ r := by nlinarith [mul_nonneg (show 0≤t by omega) (show 0≤h - 2 by omega)]
          obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp (show (4:ℤ) ≤ s by omega)
          obtain ⟨y,hy,hty⟩ := le_iff_exists_nonneg_add.mp ht
          obtain ⟨v,hv,hrv⟩ := le_iff_exists_nonneg_add.mp hr8
          dsimp [lam,L]
          rw [← hrv,← hty]
          ring_nf
          positivity
      have heq : lam * (u - 1) - 2 * M - 2 * L * lam =
          r * (s + 1) * (s * t - s - 1) - L * (2 * lam + 1) - s - 1 := by
        rw [hM]
        dsimp [lam,L,u]
        ring
      have hp := mul_lt_mul_of_pos_left hR.2 hL
      have hineq : lam * (2 * delta) < lam * (u - 1) := by nlinarith
      exact (mul_lt_mul_iff_of_pos_left hlam).mp hineq
  have hlam : lam < (s + 1) * (r / 2) := by
    dsimp [lam,L]
    nlinarith [mul_nonneg (show 0≤s + 1 by omega) (show 0≤r - 4 * t by omega),
      mul_nonneg (show 0≤s - 1 by omega) (show 0≤t - 2 * s by omega),
      show (s + 1) * (2 * (r / 2) - r)=0 by rw [hr2]; ring]
  have hp0 : 0 ≤ (s - 1) * q := mul_nonneg (by omega) (by omega)
  have hpc : (s - 1) * q < t / 2 := by rw [htHalf]; nlinarith
  have hepsEq : 2 * ((1 + r + r * s) * ((s - 1) * q) - (C - (r + 1) * (t / 2))) =
      2 * q * (r + 1) * (s - 1) + t + 2 := by
    rw [htHalf]
    dsimp [C]
    rw [htHalf]
    nlinarith only [htdef]
  have heps : 1 < 2 * ((1 + r + r * s) * ((s - 1) * q) - (C - (r + 1) * (t / 2))) := by
    rw [hepsEq]
    have hp : 0≤2 * q * (r + 1) * (s - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)) (by omega)
    nlinarith only [hp,ht0]
  have hepsc : 2 * ((1 + r + r * s) * ((s - 1) * q) - (C - (r + 1) * (t / 2))) < (r + 1) * t := by
    rw [hepsEq]
    have hp := mul_nonneg (show 0≤r - s by omega) (show 0≤q - 1 by omega)
    nlinarith only [htdef,hp,hr,ht,hs,hq,
      show (r + 1) * (2 * s * q - t)=0 by rw [htdef]; ring]
  change Certificate r s t (makePlan 0 Order.agb Ear.t (Mask.mk ((s - 1) * q) 0 0) (Mask.mk 0 0 z))
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; exact ⟨hp0,hpc,by omega,by omega,by omega,by omega⟩
  · dsimp [Bounded,makePlan]; exact ⟨by omega,by omega,by omega,by omega,hz0,hzr⟩
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    norm_num
    dsimp [delta,H,C,L,u,R,Y,lam] at hdel hR hlam
    repeat' constructor
    all_goals nlinarith only [hdel.1,hdel.2,hR.1,hR.2,hlam,heps,hepsc,
      hs2,hr2,ht2,
      show (s + 1) * (2 * (r / 2) - r)=0 by rw [hr2]; ring,
      show (t + 1) * (2 * (s / 2) - s)=0 by rw [hs2]; ring,
      show (r + 1) * (2 * (t / 2) - t)=0 by rw [ht2]; ring]

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
