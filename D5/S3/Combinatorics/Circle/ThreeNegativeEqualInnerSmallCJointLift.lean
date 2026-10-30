/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualInnerSmallCJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualInnerSmallCJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical joint lifts for every two at most c less than equal a and b. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! A floor-selected physical order and literal ear for the equal first two gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerSmallCJointLift

open SourceWidth PeriodicShortening RunFirstEarTransport
open ThreeNegativeMinimumTwoJointLift

open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.agb Ear Ear.t Plan Plan.p Plan.t Plan.order Plan.ear
  Order.first Order.middle Order.last atNegative oldMass newMass cap oldHeight newHeight
  makePlan Bounded Separate Seams Certificate
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private theorem floor_unique (Y d z : ℤ) (hd : 0 < d)
    (hlo : d * z ≤ Y) (hhi : Y < d * (z + 1)) : Y / d = z := by
  apply (Int.ediv_eq_iff_of_pos hd).2
  constructor <;> nlinarith only [hlo,hhi]

/-- Here r = 4m and t = 2n. The alternatives are exactly r / t = 2,4, or at least 8. -/
private theorem floor_selector (m n : ℤ) (hn : 4 ≤ n) (hm : n ≤ m)
    (hdyad : m = n ∨ m = 2 * n ∨ 4 * n ≤ m) :
    let d := 16 * m * n + 4 * m + 1
    let Y := 32 * m ^ 2 * n - 16 * m ^ 2 - 8 * m * n - 6 * m - 2
    let z := Y / d
    0 ≤ z ∧ z < 2 * m ∧ (4 * m + 1) * z + 2 * m + 1 ≤ 8 * m ^ 2 ∧
      Y - d * z < (4 * m + 1) * z + 2 * m + 1 := by
  dsimp only
  let d := 16 * m * n + 4 * m + 1
  let Y := 32 * m ^ 2 * n - 16 * m ^ 2 - 8 * m * n - 6 * m - 2
  let z := Y / d
  change 0 ≤ z ∧ z < 2 * m ∧ (4 * m + 1) * z + 2 * m + 1 ≤ 8 * m ^ 2 ∧
    Y - d * z < (4 * m + 1) * z + 2 * m + 1
  have hm0 : 0 < m := by omega
  have hn0 : 0 ≤ n := by omega
  have hd : 0 < d := by dsimp [d]; positivity
  have hY : 0 < Y := by
    let x := m - n
    let y := n - 4
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hmx : m = x + (y + 4) := by dsimp [x,y]; ring
    have hny : n = y + 4 := by dsimp [y]; ring
    dsimp [Y]
    rw [hmx,hny]
    ring_nf
    positivity
  have hf := floor_bounds Y d hd
  change d * z ≤ Y ∧ Y < d * (z + 1) at hf
  have hz0 : 0 ≤ z := Int.ediv_nonneg (le_of_lt hY) (le_of_lt hd)
  have hupper : Y < d * (2 * m) := by
    apply sub_pos.mp
    convert (show (0 : ℤ) < 24 * m ^ 2 + 8 * m * n + 8 * m + 2 by positivity) using 1
    dsimp [Y,d]
    ring
  have hzlt : z < 2 * m := by
    by_contra hh
    have hp := mul_le_mul_of_nonneg_left (show 2 * m ≤ z by omega) (le_of_lt hd)
    omega
  have hhu : (4 * m + 1) * z + 2 * m + 1 ≤ 8 * m ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left (show z ≤ 2 * m - 1 by omega)
      (show 0 ≤ 4 * m + 1 by omega)
    nlinarith only [hp]
  refine ⟨hz0,hzlt,hhu,?_⟩
  rcases hdyad with he|he|he
  · subst m
    have hdY : Y = d * (2 * n - 2) := by dsimp [Y,d]; ring
    have hz : z = 2 * n - 2 := by
      exact floor_unique Y d (2 * n - 2) hd (by rw [hdY]) (by rw [hdY]; nlinarith)
    rw [hz,hdY]
    nlinarith [sq_nonneg n]
  · subst m
    have hdY : Y = d * (4 * n - 4) + (16 * n ^ 2 + 16 * n + 2) := by dsimp [Y,d]; ring
    have hrem : 0 ≤ 16 * n ^ 2 + 16 * n + 2 ∧ 16 * n ^ 2 + 16 * n + 2 < d := by
      dsimp [d]
      constructor
      · positivity
      · nlinarith [sq_nonneg (n - 1)]
    have hz : z = 4 * n - 4 := by
      apply floor_unique Y d (4 * n - 4) hd <;> nlinarith only [hdY,hrem.1,hrem.2]
    rw [hz,hdY]
    have hpos : 0 < 16 * n ^ 2 - 40 * n - 5 := by
      let y := n - 4
      have hy : 0 ≤ y := by dsimp [y]; omega
      have he : n = y + 4 := by dsimp [y]; ring
      rw [he]; ring_nf; positivity
    nlinarith
  · have hlow : d * (m + 1) ≤ Y := by
      let x := m - 4 * n
      let y := n - 4
      have hx : 0 ≤ x := by dsimp [x]; omega
      have hy : 0 ≤ y := by dsimp [y]; omega
      have hmx : m = x + 4 * (y + 4) := by dsimp [x,y]; ring
      have hny : n = y + 4 := by dsimp [y]; ring
      apply sub_nonneg.mp
      dsimp [Y,d]
      rw [hmx,hny]; ring_nf; positivity
    have hzlo : m + 1 ≤ z := by
      by_contra hh
      have hp := mul_le_mul_of_nonneg_left (show z + 1 ≤ m + 1 by omega) (le_of_lt hd)
      omega
    have hreserve : d < (4 * m + 1) * z + 2 * m + 1 := by
      have hp := mul_le_mul_of_nonneg_left hzlo (show 0 ≤ 4 * m + 1 by omega)
      have hmn := mul_nonneg (show 0 ≤ m - 4 * n by omega) (show 0 ≤ 4 * m by omega)
      dsimp [d]
      nlinarith
    nlinarith [hf.2]

private theorem floor_certificate (m n q : ℤ) (hn : 4 ≤ n) (hm : n ≤ m)
    (hq : 2 ≤ q) (hrq : 4 * m = q * (2 * n)) (hdyad : m = n ∨ m = 2 * n ∨ 4 * n ≤ m) :
    let Y := 32 * m ^ 2 * n - 16 * m ^ 2 - 8 * m * n - 6 * m - 2
    let d := 16 * m * n + 4 * m + 1
    Certificate (4 * m) (4 * m) (2 * n)
      (makePlan 0 Order.agb Ear.t (Mask.mk (n - 1) (q - 1) 0) (Mask.mk 0 0 (Y / d))) := by
  dsimp only
  let Y := 32 * m ^ 2 * n - 16 * m ^ 2 - 8 * m * n - 6 * m - 2
  let d := 16 * m * n + 4 * m + 1
  let z := Y / d
  change Certificate (4 * m) (4 * m) (2 * n)
    (makePlan 0 Order.agb Ear.t (Mask.mk (n - 1) (q - 1) 0) (Mask.mk 0 0 z))
  let u := 1 + 4 * m + 16 * m ^ 2
  let B := 1 + 2 * n + 8 * m * n
  let L := 1 + 4 * m + 8 * m * n
  let C := 16 * m ^ 2 * n - 1
  let Ha := C - (4 * m + 1) * n
  let Hb := C - (2 * n + 1) * (2 * m)
  let Hg := C - (4 * m + 1) * (2 * m)
  let Ka := 2 * Ha + 1
  let Kb := 2 * Hb + 2 * m + 1
  let Kg := 2 * Hg + (4 * m + 1) * (2 * m) + 1
  let R := Y - d * z
  let h := (4 * m + 1) * z + 2 * m + 1
  have hm0 : 0 < m := by omega
  have hn0 : 0 ≤ n := by omega
  have hq0 : 0 ≤ q - 1 := by omega
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨hz0,hzlt,hh,hrh⟩ := floor_selector m n hn hm hdyad
  change 0 ≤ z at hz0
  change z < 2 * m at hzlt
  change h ≤ 8 * m ^ 2 at hh
  change R < h at hrh
  have hR : 0 ≤ R := by
    have hf := (floor_bounds Y d hd).1
    change d * z ≤ Y at hf
    dsimp [R]; omega
  have hqcap : q - 1 < 2 * m := by nlinarith
  have hBq : B * q = u + q - 1 := by
    dsimp [B,u]
    nlinarith only [hrq,congrArg (fun x : ℤ => (4 * m) * x) hrq]
  have hBu : u * n - B = Ha := by dsimp [u,B,Ha,C]; ring
  have hx : u * (n - 1) + B * (q - 1) = Ha + q - 1 := by
    nlinarith only [hBq,hBu]
  have hxn : (2 * u) * (n - 1) + (2 * B - 1) * (q - 1) = Ka + q - 2 := by
    dsimp [Ka]
    nlinarith only [hx]
  have hY : Y = Kb - u := by dsimp [Y,Kb,Hb,C,u]; ring
  have hdelta : 2 * (Hb - L * z) = u + R - h := by
    dsimp [R,h,L,d]
    rw [hY]
    dsimp [Kb]
    ring
  have hhu : h < u := by dsimp [u]; nlinarith [sq_nonneg m]
  have hdelta0 : 0 ≤ Hb - L * z := by omega
  have hdeltaUpper : Hb - L * z ≤ (4 * m + 1) * (2 * m) := by
    dsimp [u] at hdelta
    nlinarith only [hdelta,hrh]
  have hRupper : R ≤ (4 * m + 1) * (2 * m) := by
    nlinarith only [hrh,hh,show 0 < m by omega]
  have htail : d * z + u ≤ Kb := by dsimp [R] at hR; omega
  have hnewTail : Kg + Kb - (d * z + u) ≤ 2 * C + 1 := by
    have he : Kb - (d * z + u) = R := by dsimp [R]; omega
    change 2 * (C - (4 * m + 1) * (2 * m)) + (4 * m + 1) * (2 * m) + 1 + Kb - (d * z + u) ≤ 2 * C + 1
    nlinarith only [he,hRupper]
  have hxcap : Ha + q - 1 ≤ C := by
    dsimp [Ha]
    have hp := mul_nonneg (show 0 ≤ 4 * m + 1 by omega) (show 0 ≤ n - 1 by omega)
    nlinarith
  have hr2 : 4 * m / 2 = 2 * m := by omega
  have ht2 : 2 * n / 2 = n := by omega
  have hseams : Ha ≤ u * (n - 1) + B * (q - 1) ∧ u * (n - 1) + B * (q - 1) ≤ C ∧
      L * z ≤ Hb ∧ Hg + Hb - L * z ≤ C ∧
      Ka ≤ (2 * u) * (n - 1) + (2 * B - 1) * (q - 1) ∧
      (2 * u) * (n - 1) + (2 * B - 1) * (q - 1) ≤ 2 * C + 1 ∧
      d * z + u ≤ Kb ∧ Kg + Kb - (d * z + u) ≤ 2 * C + 1 := by
    rw [hx,hxn]
    refine ⟨by omega,hxcap,by omega,?_,by omega,?_,htail,hnewTail⟩
    · change C - (4 * m + 1) * (2 * m) + Hb - L * z ≤ C
      linarith only [hdeltaUpper]
    · dsimp [Ka]
      omega
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · dsimp [Bounded,makePlan]; rw [hr2,ht2]; omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hr2,ht2,add_zero,mul_zero,zero_add]
    dsimp [Ha,Hb,Hg,Ka,Kb,Kg,u,B,L,C,d] at hseams
    ring_nf at hseams ⊢
    exact hseams

/-- One physical joint order for the entire family 2<=c < a = b, in the original phase. -/
theorem actualSource_three_negative_equal_inner_small_c_joint_lift (a b c : ℕ)
    (hc : 2 ≤ c) (hab : a = b) (hca : c < a) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ, j ≤ a + b + c ∧
      OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b))) (earWord (a + b + c) sigma j) := by
  by_cases hc2 : c = 2
  · exact actualSource_three_negative_minimum_two_joint_lift a b c (by omega)
      (by omega) hc (by omega)
  subst b
  have hc3 : 3 ≤ c := by omega
  let m : ℤ := 2 ^ (a - 2)
  let n : ℤ := 2 ^ (c - 1)
  let q : ℤ := 2 ^ (a - c)
  have hn : 4 ≤ n := by
    simpa [n] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 2 ≤ c - 1 by omega)
  have hm : n ≤ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : 2 ≤ q := by
    simpa [q] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ a - c by omega)
  have hr : (2 : ℤ) ^ a = 4 * m := by
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 2) + 2) := by congr 1; omega
      _ = 4 * m := by rw [pow_add]; norm_num; dsimp [m]; ring
  have ht : (2 : ℤ) ^ c = 2 * n := by
    calc
      (2 : ℤ) ^ c = 2 ^ ((c - 1) + 1) := by congr 1; omega
      _ = 2 * n := by rw [pow_succ]; dsimp [n]; ring
  have hrq : 4 * m = q * (2 * n) := by
    rw [← hr,← ht]
    dsimp [q]
    rw [← pow_add]
    congr 1
    omega
  have hdyad : m = n ∨ m = 2 * n ∨ 4 * n ≤ m := by
    by_cases h1 : a = c + 1
    · left
      dsimp [m,n]
      congr 1
      omega
    by_cases h2 : a = c + 2
    · right; left
      dsimp [m,n]
      calc
        (2 : ℤ) ^ (a - 2) = 2 ^ ((c - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (c - 1) := by rw [pow_succ]; ring
    · right; right
      have hp : (2 : ℤ) ^ ((c - 1) + 2) ≤ 2 ^ (a - 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_add] at hp
      norm_num at hp
      dsimp [m,n]
      nlinarith only [hp]
  let Y := 32 * m ^ 2 * n - 16 * m ^ 2 - 8 * m * n - 6 * m - 2
  let d := 16 * m * n + 4 * m + 1
  apply realize a a c (by omega) (by omega) hc
    (makePlan 0 Order.agb Ear.t (Mask.mk (n - 1) (q - 1) 0) (Mask.mk 0 0 (Y / d)))
  rw [hr,ht]
  exact floor_certificate m n q hn hm hq hrq hdyad

#print axioms actualSource_three_negative_equal_inner_small_c_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerSmallCJointLift
