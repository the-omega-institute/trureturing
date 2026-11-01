/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualInnerLargeCJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualInnerLargeCJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Adaptive dyadic grain and a common physical order for equal first gaps. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! A literal marked physical order throughout `2 ≤ a = b < c`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport

open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.abg Order.first Order.middle Order.last Ear Ear.p Ear.q Ear.t
  Plan Plan.p Plan.t Plan.order Plan.ear makePlan Bounded Separate Seams Certificate
  oldMass newMass cap oldHeight newHeight atNegative
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

-- The two masks occupy three separated binary bands: above q, below the grain,
-- and between the grain and q, respectively.
private theorem three_band_disjoint (e g x d v : ℕ) (hge : g ≤ e)
    (hd : d < 2 ^ g) (hz : 2 ^ g * v < 2 ^ e) :
    Disjoint (2 ^ e * x + d).bitIndices.toFinset (2 ^ g * v).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hp := Nat.mem_bitIndices.mp (List.mem_toFinset.mp hi)
  have hzi := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hj)
  have hie : i < e := by
    by_contra hn
    have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show e ≤ i by omega)
    omega
  have hdi : d < 2 ^ e := lt_of_lt_of_le hd
    (Nat.pow_le_pow_right (by decide) hge)
  rw [Nat.testBit_two_pow_mul_add x hdi i, ite_eq_left hie] at hp
  simp only [Nat.bitIndices_two_pow_mul, List.mem_toFinset, List.mem_map] at hj
  obtain ⟨j, _, hji⟩ := hj
  have hgi : g ≤ i := by omega
  have hlt : d < 2 ^ i := lt_of_lt_of_le hd
    (Nat.pow_le_pow_right (by decide) hgi)
  rw [Nat.testBit_eq_false_of_lt hlt] at hp
  contradiction

private theorem ceiling_bounds (q u : ℤ) (hq : 1 ≤ q) (hu : 0 < u) :
    let d := (q - 1)/u + 1
    1 ≤ d ∧ 1 ≤ u * d + 1 - q ∧ u * d + 1 - q ≤ u := by
  have hf := floor_bounds (q - 1) u hu
  have hn := Int.ediv_nonneg (by omega : 0 ≤ q - 1) hu.le
  dsimp only
  constructor
  · omega
  · constructor <;> nlinarith only [hf.1, hf.2]

private def equalPlan (R : ℤ) (p z : ℕ) (last : Bool) : Plan :=
  makePlan 0 Order.abg (if last then Ear.t else Ear.q)
    (Mask.mk p 0 0) (Mask.mk z 0 (R - 1))

-- These are the actual alpha-beta-gamma seams for the selected masks.
set_option maxHeartbeats 800000 in
-- The coupled mask and charge bounds expand several nonlinear products.
private theorem equal_seams (R q d : ℤ) (p z : ℕ) (hR : 2 ≤ R) (hq : 2 ≤ q)
    (hp : (p : ℤ) = (R - 1) * q + d)
    (he : 1 ≤ (1 + 2 * R + 4 * R ^ 2) * d + 1 - q)
    (hex : (1 + 2 * R + 4 * R ^ 2) * d + 1 - q ≤ R * q * (1 + 2 * R))
    (hz : 0 ≤ 4 * R ^ 2 * (q - 1) - (1 + 2 * R + 4 * R ^ 2) * z)
    (last : Bool)
    (hbranch : if last then
      q = 2 ∧ 4 * R ^ 2 * (q - 1) - (1 + 2 * R + 4 * R ^ 2) * z = 4 * R ^ 2
      else 2 * (4 * R ^ 2 * (q - 1) - (1 + 2 * R + 4 * R ^ 2) * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R) :
    Seams (2 * R) (2 * R) (2 * R * q) (equalPlan R p z last) := by
  have hRp : 0 < R := by omega
  have hqp : 0 < q := by omega
  have hr : (2 * R)/2 = R := by omega
  have ht : (2 * R * q)/2 = R * q := by
    rw [show 2 * R * q = 2 * (R * q) by ring]
    omega
  have hcharge : 4 * R ^ 2 ≥ 1 + 2 * R + 4 * R ^ 2 - 4 * R ^ 2 := by nlinarith
  have hz0 : 0 ≤ (z : ℤ) := Nat.cast_nonneg z
  cases last
  · change 2 * (4 * R ^ 2 * (q - 1) - (1 + 2 * R + 4 * R ^ 2) * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R at hbranch
    dsimp [Seams, equalPlan, makePlan, oldMass, newMass, oldHeight, newHeight, cap,
      Order.first, Order.middle, Order.last, atNegative]
    simp only [hr, ht, add_zero, mul_zero]
    rw [hp]
    repeat' constructor
    all_goals nlinarith only [he, hex, hz, hbranch, hz0, hR, hq,
      mul_nonneg (show 0 ≤ R - 1 by omega) (show 0 ≤ 2 * R * q by positivity)]
  · change q = 2 ∧ 4 * R ^ 2 * (q - 1) - (1 + 2 * R + 4 * R ^ 2) * z = 4 * R ^ 2 at hbranch
    obtain ⟨rfl, hdelta⟩ := hbranch
    dsimp [Seams, equalPlan, makePlan, oldMass, newMass, oldHeight, newHeight, cap,
      Order.first, Order.middle, Order.last, atNegative]
    simp only [hr, ht, add_zero, mul_zero]
    rw [hp]
    repeat' constructor
    all_goals nlinarith only [he, hex, hdelta, hz0, hR, hcharge,
      mul_nonneg (show 0 ≤ R - 1 by omega) (show 0 ≤ R by omega)]

set_option maxHeartbeats 800000 in
-- The coupled mask and charge bounds expand several nonlinear products.
private theorem adaptive_arithmetic (R q h : ℤ) (hR : 2 ≤ R) (hq : 2 ≤ q)
    (hh : 1 ≤ h) (hdyadic : q = 2 ∨ q = 4 ∨ 8 ≤ q)
    (hscale : (h = 1 ∧ q < 4 * R ^ 2) ∨ q = 4 * R ^ 2 * h) :
    let u := 1 + 2 * R + 4 * R ^ 2
    let d := (q - 1)/u + 1
    let z := 2 * h * ((4 * R ^ 2 * (q - 1))/(2 * h * u))
    let p := (R - 1) * q + d
    1 ≤ d ∧ d ≤ h ∧ 0 ≤ p ∧ p < R * q ∧ 0 ≤ z ∧ z < q - 1 ∧
      1 ≤ u * d + 1 - q ∧ u * d + 1 - q ≤ R * q * (1 + 2 * R) ∧
      0 ≤ 4 * R ^ 2 * (q - 1) - u * z ∧
      (q = 2 → z = 0 ∧ 4 * R ^ 2 * (q - 1) - u * z = 4 * R ^ 2) ∧
      (q ≠ 2 → 2 * (4 * R ^ 2 * (q - 1) - u * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R) := by
  dsimp only
  let u := 1 + 2 * R + 4 * R ^ 2
  let d := (q - 1)/u + 1
  let z := 2 * h * ((4 * R ^ 2 * (q - 1))/(2 * h * u))
  let p := (R - 1) * q + d
  change 1 ≤ d ∧ d ≤ h ∧ 0 ≤ p ∧ p < R * q ∧ 0 ≤ z ∧ z < q - 1 ∧
    1 ≤ u * d + 1 - q ∧ u * d + 1 - q ≤ R * q * (1 + 2 * R) ∧
    0 ≤ 4 * R ^ 2 * (q - 1) - u * z ∧
    (q = 2 → z = 0 ∧ 4 * R ^ 2 * (q - 1) - u * z = 4 * R ^ 2) ∧
    (q ≠ 2 → 2 * (4 * R ^ 2 * (q - 1) - u * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R)
  have hRpos : 0 < R := by omega
  have hqpos : 0 < q := by omega
  have hhpos : 0 < h := by omega
  have hqm : 0 ≤ q - 1 := by omega
  have hu : 0 < u := by dsimp [u]; positivity
  have huR : 4 * R ^ 2 < u := by dsimp [u]; omega
  have hRp : 0 < 4 * R ^ 2 := by positivity
  have hden : 0 < 2 * h * u := by positivity
  obtain ⟨hd1, he1, heu⟩ := ceiling_bounds q u (by omega) hu
  change 1 ≤ d at hd1
  change 1 ≤ u * d + 1 - q at he1
  change u * d + 1 - q ≤ u at heu
  have hdh : d ≤ h := by
    rcases hscale with ⟨rfl, hsmall⟩ | hscale
    · have hd0 : (q - 1)/u = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      dsimp [d]; omega
    · by_contra hn
      have hf := (floor_bounds (q - 1) u hu).1
      have hde : (q - 1)/u = d - 1 := by dsimp [d]; omega
      rw [hde] at hf
      have hm := mul_le_mul_of_nonneg_left (show h ≤ d - 1 by omega) hu.le
      have hs : 4 * R ^ 2 * h < u * h := mul_lt_mul_of_pos_right huR (by omega)
      omega
  have hhq : h < q := by
    rcases hscale with ⟨rfl, _⟩ | hs
    · omega
    · have hsq : 16 ≤ 4 * R ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ h by omega)
      nlinarith only [hs, hm, hh]
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact add_nonneg (mul_nonneg (by omega) hqpos.le) (by omega)
  have hpq : p < R * q := by dsimp [p]; nlinarith only [hdh, hhq]
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact mul_nonneg (by positivity) (Int.ediv_nonneg (by positivity) hden.le)
  have hf := floor_bounds (4 * R ^ 2 * (q - 1)) (2 * h * u) hden
  have hrem : 0 ≤ 4 * R ^ 2 * (q - 1) - u * z ∧ 4 * R ^ 2 * (q - 1) - u * z < 2 * h * u := by
    dsimp [z]
    constructor <;> nlinarith only [hf.1, hf.2]
  have hzq : z < q - 1 := by
    have hmul : u * z < u * (q - 1) := by
      have hs := mul_lt_mul_of_pos_right huR (show 0 < q - 1 by omega)
      nlinarith only [hrem.1, hs]
    exact lt_of_mul_lt_mul_left hmul hu.le
  have heupper : u * d + 1 - q ≤ R * q * (1 + 2 * R) := by
    by_cases hq2 : q = 2
    · have hh1 : h = 1 := by
        rcases hscale with h|hs
        · exact h.1
        · have hm := mul_le_mul_of_nonneg_right
            (show 16 ≤ 4 * R ^ 2 by nlinarith) (show 0 ≤ h by omega)
          omega
      have hd : d = 1 := by omega
      rw [hd, hq2]
      dsimp [u]
      nlinarith
    · have hq4 : 4 ≤ q := by rcases hdyadic with h|h|h <;> omega
      have hsmall : u ≤ 4 * R * (1 + 2 * R) := by dsimp [u]; nlinarith
      have hm := mul_le_mul_of_nonneg_right hq4
        (show 0 ≤ R * (1 + 2 * R) by positivity)
      nlinarith only [heu, hsmall, hm]
  have htwo : q = 2 → z = 0 ∧ 4 * R ^ 2 * (q - 1) - u * z = 4 * R ^ 2 := by
    intro hq2
    have hh1 : h = 1 := by
      rcases hscale with h|hs
      · exact h.1
      · have hm := mul_le_mul_of_nonneg_right
          (show 16 ≤ 4 * R ^ 2 by nlinarith) (show 0 ≤ h by omega)
        omega
    have hf0 : (4 * R ^ 2 * (q - 1))/(2 * h * u) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · rw [hq2, hh1]
        dsimp [u]
        nlinarith
    have hz : z = 0 := by dsimp [z]; rw [hf0]; ring
    exact ⟨hz, by rw [hz, hq2]; ring⟩
  have hlarge : q ≠ 2 → 2 * (4 * R ^ 2 * (q - 1) - u * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R := by
    intro hn2
    by_cases hq4 : q = 4
    · have hh1 : h = 1 := by
        rcases hscale with h|hs
        · exact h.1
        · have hm := mul_le_mul_of_nonneg_right
            (show 16 ≤ 4 * R ^ 2 by nlinarith) (show 0 ≤ h by omega)
          omega
      have hflow : 2 * h * u ≤ 4 * R ^ 2 * (q - 1) := by
        rw [hq4, hh1]; dsimp [u]; nlinarith
      have hfhigh : 4 * R ^ 2 * (q - 1) < 2 * (2 * h * u) := by
        rw [hq4, hh1]; dsimp [u]; nlinarith
      have hf1 : (4 * R ^ 2 * (q - 1))/(2 * h * u) = 1 := by
        have hlt2 : (4 * R ^ 2 * (q - 1))/(2 * h * u) < 2 :=
          (Int.ediv_lt_iff_lt_mul hden).mpr (by nlinarith only [hfhigh])
        have hge1 : 1 ≤ (4 * R ^ 2 * (q - 1))/(2 * h * u) :=
          (Int.le_ediv_iff_mul_le hden).mpr (by nlinarith only [hflow])
        omega
      have hz : z = 2 := by dsimp [z]; rw [hf1, hh1]; ring
      rw [hz, hq4]; dsimp [u]; nlinarith
    · have hq8 : 8 ≤ q := by rcases hdyadic with h|h|h <;> omega
      rcases hscale with ⟨hh1, hsmall⟩ | hs
      · rw [hh1] at hrem
        have hbound : 4 * u + 4 * R ^ 2 < 32 * R ^ 2 + R := by
          dsimp [u]
          nlinarith [sq_nonneg (R - 2)]
        have hm := mul_le_mul_of_nonneg_right hq8 (show 0 ≤ 4 * R ^ 2 by positivity)
        nlinarith only [hrem.2, hbound, hm]
      · have hu21 : 16 * u ≤ 21 * (4 * R ^ 2) := by
          dsimp [u]
          nlinarith [mul_nonneg (show 0 ≤ R - 2 by omega) (show 0 ≤ 5 * R + 2 by omega)]
        have hm := mul_le_mul_of_nonneg_right hu21 (show 0 ≤ h by omega)
        have hRq : 4 * R ^ 2 ≤ q := by
          have hm := mul_le_mul_of_nonneg_left hh hRp.le
          nlinarith only [hs, hm]
        have hqR : 25 * q < 16 * q * R ^ 2 := by
          have hm := mul_le_mul_of_nonneg_right
            (show 4 ≤ R ^ 2 by nlinarith) (show 0 ≤ q by omega)
          nlinarith only [hm, hq]
        nlinarith only [hrem.2, hm, hs, hRq, hqR]
  exact ⟨hd1, hdh, hp0, hpq, hz0, hzq, he1, heupper, hrem.1, htwo, hlarge⟩

set_option maxHeartbeats 1000000 in
-- The coupled mask and charge bounds expand several nonlinear products.
private theorem adaptive_certificate (a n : ℕ) (ha : 2 ≤ a) (hn : 1 ≤ n) :
    ∃ plan : Plan, Certificate ((2 : ℤ) ^ a) (2 ^ a) (2 ^ (a + n)) plan := by
  let R : ℤ := 2 ^ (a - 1)
  let q : ℤ := 2 ^ n
  let h : ℤ := 2 ^ (n - 2 * a)
  let u := 1 + 2 * R + 4 * R ^ 2
  let d := (q - 1)/u + 1
  let v := (4 * R ^ 2 * (q - 1))/(2 * h * u)
  let g := n - 2 * a + 1
  let p : ℕ := 2 ^ n * (R - 1).toNat + d.toNat
  let z : ℕ := 2 ^ g * v.toNat
  have hR : 2 ≤ R := by
    change (2 : ℤ) ^ 1 ≤ 2 ^ (a - 1)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : 2 ≤ q := by
    change (2 : ℤ) ^ 1 ≤ 2 ^ n
    exact pow_le_pow_right₀ (by norm_num) hn
  have hh : 1 ≤ h := by dsimp [h]; exact_mod_cast Nat.one_le_two_pow
  have hRpos : 0 < R := by omega
  have hqpos : 0 < q := by omega
  have hhpos : 0 < h := by omega
  have hqm : 0 ≤ q - 1 := by omega
  have hr : (2 : ℤ) ^ a = 2 * R := by
    dsimp [R]
    rw [←pow_succ']
    congr 1
    omega
  have ht : (2 : ℤ) ^ (a + n) = 2 * R * q := by rw [pow_add, hr]
  have hr2 : (2 : ℤ) ^ (2 * a) = 4 * R ^ 2 := by
    rw [show 2 * a = a + a by omega, pow_add, hr]
    ring
  have hscale : (h = 1 ∧ q < 4 * R ^ 2) ∨ q = 4 * R ^ 2 * h := by
    by_cases hsmall : n < 2 * a
    · left
      constructor
      · dsimp [h]; rw [Nat.sub_eq_zero_of_le (by omega)]; norm_num
      · rw [←hr2]
        exact pow_lt_pow_right₀ (by norm_num) hsmall
    · right
      rw [←hr2]
      dsimp [q, h]
      rw [←pow_add]
      congr 1
      omega
  have hdyadic : q = 2 ∨ q = 4 ∨ 8 ≤ q := by
    by_cases h1 : n = 1
    · left; dsimp [q]; rw [h1]; norm_num
    · by_cases h2 : n = 2
      · right; left; dsimp [q]; rw [h2]; norm_num
      · right; right
        change (2 : ℤ) ^ 3 ≤ 2 ^ n
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨hd1, hdh, hp0, hpcap, hz0, hzq, he1, heupper, hdelta, htwo, hlarge⟩ :=
    adaptive_arithmetic R q h hR hq hh hdyadic hscale
  change 1 ≤ d at hd1
  change d ≤ h at hdh
  change 0 ≤ (R - 1) * q + d at hp0
  change (R - 1) * q + d < R * q at hpcap
  change 0 ≤ 2 * h * v at hz0
  change 2 * h * v < q - 1 at hzq
  change 1 ≤ u * d + 1 - q at he1
  change u * d + 1 - q ≤ R * q * (1 + 2 * R) at heupper
  change 0 ≤ 4 * R ^ 2 * (q - 1) - u * (2 * h * v) at hdelta
  change q = 2 → 2 * h * v = 0 ∧ 4 * R ^ 2 * (q - 1) - u * (2 * h * v) = 4 * R ^ 2 at htwo
  change q ≠ 2 → 2 * (4 * R ^ 2 * (q - 1) - u * (2 * h * v)) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R at hlarge
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 ≤ v := Int.ediv_nonneg (by positivity) (by positivity)
  have hgrain : (2 : ℤ) ^ g = 2 * h := by
    dsimp [g, h]
    rw [pow_succ]
    ring
  have hg : g ≤ n := by dsimp [g]; omega
  have hpcast : (p : ℤ) = (R - 1) * q + d := by
    dsimp [p]
    push_cast
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ R - 1), Int.toNat_of_nonneg (by omega : 0 ≤ d)]
    change q * (R - 1) + d = _
    ring
  have hzcast : (z : ℤ) = 2 * h * v := by
    dsimp [z]
    push_cast
    rw [hgrain, Int.toNat_of_nonneg hv]
  have hdgrain : d.toNat < 2 ^ g := by
    have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
    have hlt : (d.toNat : ℤ) < (2 : ℤ) ^ g := by rw [he, hgrain]; omega
    exact_mod_cast hlt
  have hzband : 2 ^ g * v.toNat < 2 ^ n := by
    have hlt : ((2 ^ g * v.toNat : ℕ) : ℤ) < (2 : ℤ) ^ n := by
      change (z : ℤ) < q
      rw [hzcast]
      omega
    exact_mod_cast hlt
  have hsep : Separate (Mask.mk (p : ℤ) 0 0) (Mask.mk (z : ℤ) 0 (R - 1)) := by
    refine ⟨?_, by simp, by simp⟩
    change Disjoint ((p : ℤ).toNat.bitIndices.toFinset) ((z : ℤ).toNat.bitIndices.toFinset)
    simp only [Int.toNat_natCast]
    exact three_band_disjoint n g (R - 1).toNat d.toNat v.toNat hg hdgrain hzband
  have hrhalf : 2 * R/2 = R := by omega
  have hthalf : 2 * R * q/2 = R * q := by
    rw [show 2 * R * q = 2 * (R * q) by ring]
    omega
  have hpBound : Bounded (2 * R) (2 * R) (2 * R * q) (Mask.mk (p : ℤ) 0 0) := by
    dsimp [Bounded]
    rw [hrhalf, hthalf, hpcast]
    exact ⟨hp0, hpcap, by omega, by omega, by omega, by omega⟩
  have hzBound : Bounded (2 * R) (2 * R) (2 * R * q) (Mask.mk (z : ℤ) 0 (R - 1)) := by
    dsimp [Bounded]
    rw [hrhalf, hthalf, hzcast]
    have hmul : q ≤ R * q := by nlinarith [mul_nonneg (show 0 ≤ R - 1 by omega) hqpos.le]
    exact ⟨hz0, by omega, by omega, by omega, by omega, by omega⟩
  by_cases hq2 : q = 2
  · refine ⟨equalPlan R p z true, ?_⟩
    rw [hr, ht]
    refine ⟨hpBound, hzBound, hsep, ?_⟩
    apply equal_seams R q d p z hR hq hpcast he1 heupper
    · rw [hzcast]; exact hdelta
    · change q = 2 ∧ 4 * R ^ 2 * (q - 1) - u * z = 4 * R ^ 2
      exact ⟨hq2, by rw [hzcast]; exact (htwo hq2).2⟩
  · refine ⟨equalPlan R p z false, ?_⟩
    rw [hr, ht]
    refine ⟨hpBound, hzBound, hsep, ?_⟩
    apply equal_seams R q d p z hR hq hpcast he1 heupper
    · rw [hzcast]; exact hdelta
    · change 2 * (4 * R ^ 2 * (q - 1) - u * z) + 4 * R ^ 2 ≤ 4 * q * R ^ 2 + R
      rw [hzcast]
      exact hlarge hq2

/-- One physical permutation and one literal insertion for all `2 ≤ a = b < c`. -/
theorem actualSource_three_negative_equal_inner_large_c_joint_lift
    (a b c : ℕ) (ha : 2 ≤ a) (hab : a = b) (hbc : b < c) :
    ∃ sigma : List (Fin (a + b + c)), ∃ j : ℕ, j ≤ a + b + c ∧
      OriginalOrder (a + b + c) (1 + 2 ^ a + 2 ^ (a + b)) sigma ∧
      OriginalOrder (a + b + c + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b)))
        (earWord (a + b + c) sigma j) := by
  subst b
  obtain ⟨plan, hcert⟩ := adaptive_certificate a (c - a) ha (by omega)
  have hc : a + (c - a) = c := by omega
  rw [hc] at hcert
  exact realize a a c ha ha (by omega) plan hcert

#print axioms actualSource_three_negative_equal_inner_large_c_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualInnerLargeCJointLift
