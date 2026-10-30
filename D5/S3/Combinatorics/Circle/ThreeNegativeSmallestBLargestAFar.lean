/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAFar
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestBLargestAFar
   mirror-E: none(waiver:private-mask-certificates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded far masks in the strict smallest-b largest-a chamber. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
open ThreeNegativeMinimumTwoJointLift
open private Mask Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Ear Plan Plan.p Plan.t Plan.order Plan.ear atNegative Order.first Order.middle Order.last
  oldMass newMass cap oldHeight newHeight Bounded Seams Certificate makePlan Separate
  disjoint_low_bits
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks

private theorem floor_bounds (n d : ℤ) (hd : 0 < d) :
    d * (n / d) ≤ n ∧ n < d * (n / d + 1) := by
  have h0 := Int.emod_nonneg n (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos n hd
  have he := Int.mul_ediv_add_emod n d
  constructor <;> nlinarith

private theorem far_certificate (s q h : ℤ) (hs : 8 ≤ s) (hq : 1 ≤ q) (hh : 1 ≤ h)
    (hs2 : 2 * (s / 2) = s) :
    let t := 2 * s * q
    let r := 4 * t * h
    let u := 1 + r + r * s
    let L := 1 + s + s * t
    let H := oldHeight r s t .beta
    let z := (2 * H + s / 2 + 1 - u) / (2 * L - s - 1)
    Certificate r s t (makePlan 0 .agb .t ⟨(s-1)*q,0,0⟩ ⟨0,0,z⟩) := by
  dsimp only
  let t := 2 * s * q
  let r := 4 * t * h
  let u := 1 + r + r * s
  let L := 1 + s + s * t
  let C := r * s * (t / 2) - 1
  let H := C - (t + 1) * (s / 2)
  let lam := 2 * L - s - 1
  let Y := 2 * H + s / 2 + 1 - u
  let z := Y / lam
  let R := Y - lam * z
  let delta := H - L * z
  have ht : 2 * s ≤ t := by dsimp [t]; nlinarith
  have hr : 4 * t ≤ r := by dsimp [r]; nlinarith
  have ht2 : 2 * (t / 2) = t := by dsimp [t]; omega
  have hr2 : 2 * (r / 2) = r := by dsimp [r]; omega
  have hs0 : 0 ≤ s / 2 := by omega
  have ht0 : 0 < t := by omega
  have hr0 : 0 < r := by omega
  have hL : 0 < L := by dsimp [L]; positivity
  have hlam : 0 < lam := by dsimp [lam,L]; nlinarith
  have hY : 0 ≤ Y := by
    dsimp [Y,H,C,u]
    nlinarith [mul_nonneg (r-4*t) (s*t-s-1),
      mul_nonneg (t-2*s) (s-1), mul_nonneg (s-8) (t-1), sq_nonneg t]
  have hz0 : 0 ≤ z := Int.ediv_nonneg hY hlam.le
  have hz := floor_bounds Y lam hlam
  change lam*z ≤ Y ∧ Y < lam*(z+1) at hz
  have hR : 0 ≤ R ∧ R < lam := by dsimp [R]; constructor <;> nlinarith
  have hzr : z < r / 2 := by
    have hE : 0 < lam * (r / 2) - Y := by
      dsimp [lam,L,Y,H,C,u]
      nlinarith
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (show r/2 ≤ z by omega) hlam.le
    omega
  have hdel : 0 < 2 * delta ∧ 2 * delta < u - 1 := by
    let M := L * (u - s / 2 - 1) - H * (s + 1)
    have hid : lam * delta = M + L * R := by
      dsimp [lam,delta,M,R,Y]; ring
    have hM : 2 * M = (s + 1) * (r*s*t-1+2*u) + L := by
      dsimp [M,H,C,L,u]
      nlinarith [show r*s*(2*(t/2)-t)=0 by rw [ht2]; ring,
        show (t+1)*(2*(s/2)-s)=0 by rw [hs2]; ring]
    have hM0 : 0 < M := by
      have hu0 : 0 < u := by dsimp [u]; positivity
      have hn0 : 0 < r*s*t-1 := by nlinarith [mul_pos hr0 (show 0<s by omega)]
      nlinarith [mul_pos (show 0<s+1 by omega) (show 0<r*s*t-1+2*u by omega)]
    have hd0 : 0 < 2 * delta := by
      have hp := mul_nonneg hL.le hR.1
      nlinarith
    refine ⟨hd0, ?_⟩
    by_cases corner : q=1 ∧ h=1
    · obtain ⟨rfl,rfl⟩ := corner
      have ht' : t=2*s := by dsimp [t]; ring
      have hr' : r=8*s := by dsimp [r]; rw [ht']; ring
      have hz' : z=r/2-4 := by
        apply (Int.ediv_eq_iff_of_pos hlam).mpr
        dsimp [Y,H,C,lam,L,u]
        rw [hr',ht'] at *
        have hsdiv : s/2*2=s := by omega
        constructor <;> nlinarith [sq_nonneg (s-4),
          mul_nonneg (s-4) (4*s-1)]
      dsimp [delta]
      rw [hz']
      dsimp [H,C,L,u] at *
      rw [hr',ht'] at *
      nlinarith [sq_nonneg (s-4)]
    · have hd : 0 < r*(s+1)*(s*t-s-1)-L*(2*lam+1)-s-1 := by
        rcases le_or_gt 2 q with hq2 | hq2
        · have ht4 : 4*s ≤ t := by dsimp [t]; nlinarith
          obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp (show (4:ℤ) ≤ s by omega)
          obtain ⟨y,hy,hty⟩ := le_iff_exists_nonneg_add.mp ht4
          obtain ⟨v,hv,hrv⟩ := le_iff_exists_nonneg_add.mp hr
          dsimp [lam,L]
          rw [hrv,hty]
          ring_nf
          positivity
        · have hq1 : q=1 := by omega
          have hh2 : 2 ≤ h := by omega
          have hr8 : 8*t ≤ r := by dsimp [r]; nlinarith
          obtain ⟨x,hx,rfl⟩ := le_iff_exists_nonneg_add.mp (show (4:ℤ) ≤ s by omega)
          obtain ⟨y,hy,hty⟩ := le_iff_exists_nonneg_add.mp ht
          obtain ⟨v,hv,hrv⟩ := le_iff_exists_nonneg_add.mp hr8
          dsimp [lam,L]
          rw [hrv,hty]
          ring_nf
          positivity
      have heq : lam*(u-1)-2*M-2*L*lam =
          r*(s+1)*(s*t-s-1)-L*(2*lam+1)-s-1 := by
        rw [hM]
        dsimp [lam,L,u]
        ring
      have hp := mul_lt_mul_of_pos_left hR.2 hL
      have hineq : lam*(2*delta) < lam*(u-1) := by nlinarith
      exact (mul_lt_mul_left hlam).mp hineq
  have hlam : lam < (s+1)*(r/2) := by
    dsimp [lam,L]
    nlinarith [mul_nonneg (s+1) (r-4*t), mul_nonneg (s-1) (t-2*s)]
  have hp0 : 0 ≤ (s-1)*q := by positivity
  have hpc : (s-1)*q < t/2 := by dsimp [t]; omega
  have heps : 1 < 2*((1+r+r*s)*((s-1)*q) - (C-(r+1)*(t/2))) := by
    dsimp [C,t] at *
    nlinarith [mul_nonneg (r+1) ((s-1)*q), mul_nonneg s q]
  have hepsc : 2*((1+r+r*s)*((s-1)*q) - (C-(r+1)*(t/2))) < (r+1)*t := by
    dsimp [C,t,r] at *
    nlinarith [mul_nonneg (r+1-s) q]
  change Certificate r s t (makePlan 0 .agb .t ⟨(s-1)*q,0,0⟩ ⟨0,0,z⟩)
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; exact ⟨hp0,hpc,by omega,by omega,by omega,by omega⟩
  · dsimp [Bounded,makePlan]; exact ⟨by omega,by omega,by omega,by omega,hz0,hzr⟩
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    norm_num
    change _ at hdel
    dsimp [delta,H,C,L,u,R,Y,lam] at hdel hR hlam
    repeat' constructor <;> nlinarith

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestBLargestAJointLift
