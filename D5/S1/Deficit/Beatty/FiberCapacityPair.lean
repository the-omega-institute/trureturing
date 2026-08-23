/- GID: D5/S1/Deficit/Beatty/FiberCapacityPair
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/FiberCapacityPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every positive golden a-fiber is finite with capacity four or five, every nonnegative dual b-fiber has capacity two or three, and the b-coordinates in an a-fiber form an integer interval; Sturmian frequency and limiting distribution are not covered. -/

import D5.S1.Deficit.Beatty.FiberCoordinateBeattyForms
import D5.S1.Depth.GoldenPowerRounding
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.OrdConnected

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'golden_fiber_capacity_pair' D5 Golden/Frozen/accepted` returned no matches.
   * Searches for `capacity`, `fiber.*card`, `goldenFiber`, `fiberA`, and `fiberB` found
     `D5.S1.Eigenstructure.GoldenFiberCapacityPairs.golden_fiber_capacity_pairs`, which only
     evaluates the floor/ceiling pairs of the second and third golden powers; it neither counts
     coordinate fibers nor supplies a fiber witness, so it is not a public cover.
   * `FiberCoordinateBeattyForms.mem_goldenFiber_iff` publicly supplies the displacement equation
     for the a-fiber. No public or private declaration found by the searches states an actual
     golden fiber cardinality or interval-support theorem.
   * The proof below reuses the coordinate definitions and golden-ratio floor laws, then uses
     finite integer interval cardinalities and elementary linear arithmetic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.FiberCapacityPair

open D5.S1.Deficit.FiberCoordinateBeattyForms
open D5.S1.Depth.GoldenPowerRounding
open D5.S1.Words.GoldenFiberCoordinates

/-- The dual fiber with fixed second golden coordinate. -/
noncomputable def goldenDualFiber (b : ℤ) : Set ℕ :=
  {v | fiberB v = b}

/-- The least second coordinate in the interval parametrizing the `a`-fiber. -/
noncomputable def fiberSupportLower (a : ℤ) : ℤ :=
  ⌊((a : ℝ) - 1) * Real.goldenRatio⌋

/-- The greatest second coordinate in the interval parametrizing the `a`-fiber. -/
noncomputable def fiberSupportUpper (a : ℤ) : ℤ :=
  ⌊((a : ℝ) + 1) * Real.goldenRatio⌋

/-- The word index reconstructed from its two golden fiber coordinates. -/
noncomputable def fiberIndex (a b : ℤ) : ℕ :=
  (a + 2 * b).toNat

private theorem fiber_linear_identity (v : ℕ) :
    fiberA v + 2 * fiberB v = (v : ℤ) := by
  simp only [fiberA, fiberB]
  ring

private theorem fiberA_zero : fiberA 0 = 0 := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) := by
    rw [Int.floor_eq_iff]
    norm_num only [Int.cast_one]
    exact ⟨Real.one_lt_goldenRatio.le, Real.goldenRatio_lt_two⟩
  rw [fiberA, goldenShift, Nat.cast_zero, zero_add, one_mul, hfloor]
  norm_num

private theorem parameter_nonneg {a b : ℤ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + 2 * b := by
  omega

private theorem fiberIndex_cast {a b : ℤ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    (fiberIndex a b : ℤ) = a + 2 * b := by
  simp [fiberIndex, Int.toNat_of_nonneg (parameter_nonneg ha hb)]

private theorem fiberIndex_pos {a b : ℤ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    1 ≤ fiberIndex a b := by
  rw [← Int.ofNat_le, fiberIndex_cast ha hb]
  omega

private theorem quotient_floor_parameter_iff {a b : ℤ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    ⌊(((fiberIndex a b : ℕ) : ℝ) + 1) / Real.goldenRatio ^ 2⌋ = b ↔
      fiberSupportLower a ≤ b ∧ b ≤ fiberSupportUpper a := by
  have hsq := Real.goldenRatio_sq
  have hpos : 0 < Real.goldenRatio :=
    lt_trans (by norm_num) Real.one_lt_goldenRatio
  have hsqpos : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos hpos
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by rw [hsq]
      _ = Real.goldenRatio ^ 2 + Real.goldenRatio := by ring
      _ = 2 * Real.goldenRatio + 1 := by rw [hsq]; ring
  have hcast : ((fiberIndex a b : ℕ) : ℝ) = (a : ℝ) + 2 * (b : ℝ) := by
    exact_mod_cast fiberIndex_cast ha hb
  have hleft_identity :
      Real.goldenRatio *
          ((a : ℝ) + 2 * (b : ℝ) + 1 - (b : ℝ) * Real.goldenRatio ^ 2) =
        ((a : ℝ) + 1) * Real.goldenRatio - (b : ℝ) := by
    calc
      _ = (a : ℝ) * Real.goldenRatio + 2 * (b : ℝ) * Real.goldenRatio +
          Real.goldenRatio - (b : ℝ) * Real.goldenRatio ^ 3 := by ring
      _ = _ := by rw [hcube]; ring
  have hright_identity :
      Real.goldenRatio *
          (((b : ℝ) + 1) * Real.goldenRatio ^ 2 -
            ((a : ℝ) + 2 * (b : ℝ) + 1)) =
        (b : ℝ) + 1 - ((a : ℝ) - 1) * Real.goldenRatio := by
    calc
      _ = (b : ℝ) * Real.goldenRatio ^ 3 + Real.goldenRatio ^ 3 -
          (a : ℝ) * Real.goldenRatio - 2 * (b : ℝ) * Real.goldenRatio -
          Real.goldenRatio := by ring
      _ = _ := by rw [hcube]; ring
  rw [Int.floor_eq_iff, fiberSupportLower, fiberSupportUpper, Int.floor_le_iff,
    Int.le_floor, hcast]
  rw [le_div_iff₀ hsqpos, div_lt_iff₀ hsqpos]
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · have hdiff :
          0 < ((b : ℝ) + 1) * Real.goldenRatio ^ 2 -
            ((a : ℝ) + 2 * (b : ℝ) + 1) := sub_pos.mpr hright
      have hscaled := mul_pos hpos hdiff
      rw [hright_identity] at hscaled
      linarith
    · have hdiff :
          0 ≤ (a : ℝ) + 2 * (b : ℝ) + 1 - (b : ℝ) * Real.goldenRatio ^ 2 :=
        sub_nonneg.mpr hleft
      have hscaled := mul_nonneg hpos.le hdiff
      rw [hleft_identity] at hscaled
      linarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · have htarget :
          0 ≤ ((a : ℝ) + 1) * Real.goldenRatio - (b : ℝ) :=
        sub_nonneg.mpr hupper
      rw [← hleft_identity] at htarget
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hpos).mp htarget)
    · have htarget :
          0 < (b : ℝ) + 1 - ((a : ℝ) - 1) * Real.goldenRatio :=
        sub_pos.mpr hlower
      rw [← hright_identity] at htarget
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hpos).mp htarget)

private theorem fiberB_fiberIndex_iff {a b : ℤ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    fiberB (fiberIndex a b) = b ↔
      fiberSupportLower a ≤ b ∧ b ≤ fiberSupportUpper a := by
  rw [(golden_fiber_coordinates (fiberIndex a b) (fiberIndex_pos ha hb)).2.1]
  exact quotient_floor_parameter_iff ha hb

private theorem fiberSupportLower_nonneg {a : ℤ} (ha : 1 ≤ a) :
    0 ≤ fiberSupportLower a := by
  rw [fiberSupportLower, Int.floor_nonneg]
  exact mul_nonneg (by exact_mod_cast (sub_nonneg.mpr ha))
    (le_trans (by norm_num) Real.one_lt_goldenRatio.le)

private theorem fiberB_nonneg_of_mem {a : ℤ} (ha : 1 ≤ a) {v : ℕ}
    (hv : v ∈ goldenFiber a) : 0 ≤ fiberB v := by
  have hvpos : 1 ≤ v := by
    by_contra h
    have hvzero : v = 0 := by omega
    subst v
    change fiberA 0 = a at hv
    rw [fiberA_zero] at hv
    omega
  rw [(golden_fiber_coordinates v hvpos).2.1, Int.floor_nonneg]
  positivity

private theorem fiberIndex_eq_of_mem {a : ℤ} (ha : 1 ≤ a) {v : ℕ}
    (hv : v ∈ goldenFiber a) : fiberIndex a (fiberB v) = v := by
  have hb := fiberB_nonneg_of_mem ha hv
  apply Int.ofNat_inj.mp
  rw [fiberIndex_cast ha hb]
  change fiberA v = a at hv
  rw [← hv]
  exact fiber_linear_identity v

private theorem goldenFiber_eq_image_Icc (a : ℤ) (ha : 1 ≤ a) :
    goldenFiber a =
      fiberIndex a '' Set.Icc (fiberSupportLower a) (fiberSupportUpper a) := by
  ext v
  constructor
  · intro hv
    have hb := fiberB_nonneg_of_mem ha hv
    have hvindex := fiberIndex_eq_of_mem ha hv
    refine ⟨fiberB v, ?_, hvindex⟩
    exact (fiberB_fiberIndex_iff ha hb).mp (by rw [hvindex])
  · rintro ⟨b, hb, rfl⟩
    have hbnonneg : 0 ≤ b := (fiberSupportLower_nonneg ha).trans hb.1
    have hB := (fiberB_fiberIndex_iff ha hbnonneg).mpr hb
    change fiberA (fiberIndex a b) = a
    have hlinear := fiber_linear_identity (fiberIndex a b)
    rw [hB, fiberIndex_cast ha hbnonneg] at hlinear
    omega

private theorem fiberIndex_injOn_Icc {a : ℤ} (ha : 1 ≤ a) :
    Set.InjOn (fiberIndex a)
      (Set.Icc (fiberSupportLower a) (fiberSupportUpper a)) := by
  intro b hb c hc hbc
  have hbnonneg : 0 ≤ b := (fiberSupportLower_nonneg ha).trans hb.1
  have hcnonneg : 0 ≤ c := (fiberSupportLower_nonneg ha).trans hc.1
  have hbcint := congrArg Int.ofNat hbc
  change (fiberIndex a b : ℤ) = (fiberIndex a c : ℤ) at hbcint
  rw [fiberIndex_cast ha hbnonneg, fiberIndex_cast ha hcnonneg] at hbcint
  omega

private theorem fiber_support_width (a : ℤ) :
    fiberSupportUpper a - fiberSupportLower a = 3 ∨
      fiberSupportUpper a - fiberSupportLower a = 4 := by
  have hsq := Real.goldenRatio_sq
  have hthree : (3 : ℝ) < 2 * Real.goldenRatio := by
    nlinarith [Real.one_lt_goldenRatio]
  have hfour : 2 * Real.goldenRatio < (4 : ℝ) := by
    linarith [Real.goldenRatio_lt_two]
  have hlower_le :
      (fiberSupportLower a : ℝ) ≤ ((a : ℝ) - 1) * Real.goldenRatio := by
    exact Int.floor_le _
  have hlower_succ :
      ((a : ℝ) - 1) * Real.goldenRatio < (fiberSupportLower a : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have harg :
      ((a : ℝ) + 1) * Real.goldenRatio =
        ((a : ℝ) - 1) * Real.goldenRatio + 2 * Real.goldenRatio := by
    ring
  have hlower_bound : fiberSupportLower a + 3 ≤ fiberSupportUpper a := by
    change fiberSupportLower a + 3 ≤ ⌊((a : ℝ) + 1) * Real.goldenRatio⌋
    rw [Int.le_floor]
    norm_num only [Int.cast_add, Int.cast_ofNat]
    rw [harg]
    linarith
  have hupper_bound : fiberSupportUpper a < fiberSupportLower a + 5 := by
    change ⌊((a : ℝ) + 1) * Real.goldenRatio⌋ < fiberSupportLower a + 5
    rw [Int.floor_lt]
    norm_num only [Int.cast_add, Int.cast_ofNat]
    rw [harg]
    linarith
  omega

private theorem ncard_Icc_int (l u : ℤ) :
    (Set.Icc l u).ncard = (u + 1 - l).toNat := by
  have hset : Set.Icc l u = (Finset.Icc l u : Set ℤ) := by
    ext x
    simp
  rw [hset, Set.ncard_coe_finset, Int.card_Icc]

/-- Every positive first-coordinate fiber is finite. -/
theorem golden_fiber_finite (a : ℤ) (ha : 1 ≤ a) :
    (goldenFiber a).Finite := by
  rw [goldenFiber_eq_image_Icc a ha]
  exact (Set.finite_Icc (fiberSupportLower a) (fiberSupportUpper a)).image _

/-- A positive first-coordinate fiber has exactly one of the two capacities four and five. -/
theorem golden_fiber_capacity_pair (a : ℤ) (ha : 1 ≤ a) :
    (goldenFiber a).ncard ∈ ({4, 5} : Set ℕ) := by
  rw [goldenFiber_eq_image_Icc a ha]
  rw [(fiberIndex_injOn_Icc ha).ncard_image]
  rw [ncard_Icc_int]
  rcases fiber_support_width a with hwidth | hwidth
  · left
    have : fiberSupportUpper a + 1 - fiberSupportLower a = 4 := by omega
    rw [this]
    rfl
  · right
    have : fiberSupportUpper a + 1 - fiberSupportLower a = 5 := by omega
    rw [this]
    rfl

private noncomputable def dualParameterLower (b : ℤ) : ℤ :=
  max 1 ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉

private noncomputable def dualParameterUpper (b : ℤ) : ℤ :=
  ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ - 1

private noncomputable def dualParameterIndex (n : ℤ) : ℕ :=
  (n - 1).toNat

private theorem fiberB_zero : fiberB 0 = 0 := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) := by
    rw [Int.floor_eq_iff]
    norm_num only [Int.cast_one]
    exact ⟨Real.one_lt_goldenRatio.le, Real.goldenRatio_lt_two⟩
  rw [fiberB, goldenShift]
  norm_num [hfloor]

private theorem fiberB_eq_floor_all (v : ℕ) :
    fiberB v = ⌊((v : ℝ) + 1) / Real.goldenRatio ^ 2⌋ := by
  by_cases hv : v = 0
  · subst v
    rw [fiberB_zero]
    symm
    rw [Int.floor_eq_iff]
    norm_num only [Nat.cast_zero, zero_add, Int.cast_zero]
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  · exact (golden_fiber_coordinates v (by omega)).2.1

private theorem dualParameterIndex_cast {n : ℤ} (hn : 1 ≤ n) :
    (dualParameterIndex n : ℤ) = n - 1 := by
  change Int.ofNat ((n - 1).toNat) = n - 1
  exact Int.toNat_of_nonneg (by omega)

private theorem goldenDualFiber_eq_image_Icc (b : ℤ) :
    goldenDualFiber b =
      dualParameterIndex '' Set.Icc (dualParameterLower b) (dualParameterUpper b) := by
  have hsqpos : 0 < Real.goldenRatio ^ 2 := by positivity
  ext v
  constructor
  · intro hv
    change fiberB v = b at hv
    rw [fiberB_eq_floor_all, Int.floor_eq_iff] at hv
    let n : ℤ := (v : ℤ) + 1
    have hnreal : (n : ℝ) = (v : ℝ) + 1 := by simp [n]
    have hlower : dualParameterLower b ≤ n := by
      rw [dualParameterLower, max_le_iff]
      constructor
      · simp [n]
      · rw [Int.ceil_le, hnreal]
        exact (le_div_iff₀ hsqpos).mp hv.1
    have hupper : n ≤ dualParameterUpper b := by
      rw [dualParameterUpper]
      have hlt : n < ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ := by
        rw [Int.lt_ceil, hnreal]
        exact (div_lt_iff₀ hsqpos).mp hv.2
      omega
    refine ⟨n, ⟨hlower, hupper⟩, ?_⟩
    rw [dualParameterIndex]
    have hnsub : n - 1 = (v : ℤ) := by simp [n]
    rw [hnsub, Int.toNat_natCast]
  · rintro ⟨n, hn, rfl⟩
    have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn.1
    have hnreal : ((dualParameterIndex n : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have hncast := dualParameterIndex_cast hn1
      exact_mod_cast (show (dualParameterIndex n : ℤ) + 1 = n by omega)
    change fiberB (dualParameterIndex n) = b
    rw [fiberB_eq_floor_all, Int.floor_eq_iff, hnreal]
    constructor
    · rw [le_div_iff₀ hsqpos, ← Int.ceil_le]
      exact (le_max_right 1 _).trans hn.1
    · rw [div_lt_iff₀ hsqpos, ← Int.lt_ceil]
      change n < ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉
      have hnupper := hn.2
      change n ≤ ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ - 1 at hnupper
      omega

private theorem dualParameterIndex_injOn_Icc (b : ℤ) :
    Set.InjOn dualParameterIndex
      (Set.Icc (dualParameterLower b) (dualParameterUpper b)) := by
  intro m hm n hn hmn
  have hm1 : 1 ≤ m := (le_max_left 1 _).trans hm.1
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn.1
  have hmnint := congrArg Int.ofNat hmn
  change (dualParameterIndex m : ℤ) = (dualParameterIndex n : ℤ) at hmnint
  rw [dualParameterIndex_cast hm1, dualParameterIndex_cast hn1] at hmnint
  omega

private theorem dual_ceil_width (b : ℤ) :
    ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ -
          ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉ = 2 ∨
      ⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ -
          ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉ = 3 := by
  let x : ℝ := (b : ℝ) * Real.goldenRatio ^ 2
  let y : ℝ := ((b : ℝ) + 1) * Real.goldenRatio ^ 2
  have harg : y = x + Real.goldenRatio ^ 2 := by
    simp [x, y]
    ring
  have htwo : (2 : ℝ) < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hthree : Real.goldenRatio ^ 2 < (3 : ℝ) := by
    rw [Real.goldenRatio_sq]
    linarith [Real.goldenRatio_lt_two]
  have hceilx_lt : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hx_le : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have hlower : ⌈x⌉ + 2 ≤ ⌈y⌉ := by
    have hreal : ((⌈x⌉ + 1 : ℤ) : ℝ) < y := by
      norm_num only [Int.cast_add, Int.cast_one]
      rw [harg]
      linarith
    have hint : ⌈x⌉ + 1 < ⌈y⌉ := (Int.lt_ceil).mpr hreal
    omega
  have hupper : ⌈y⌉ ≤ ⌈x⌉ + 3 := by
    rw [Int.ceil_le]
    norm_num only [Int.cast_add, Int.cast_ofNat]
    rw [harg]
    linarith
  change ⌈y⌉ - ⌈x⌉ = 2 ∨ ⌈y⌉ - ⌈x⌉ = 3
  omega

/-- A nonnegative second-coordinate fiber has exactly one of the two capacities two and three. -/
theorem golden_dual_fiber_capacity_pair (b : ℤ) (hb : 0 ≤ b) :
    (goldenDualFiber b).ncard ∈ ({2, 3} : Set ℕ) := by
  rw [goldenDualFiber_eq_image_Icc b]
  rw [(dualParameterIndex_injOn_Icc b).ncard_image]
  rw [ncard_Icc_int]
  by_cases hbzero : b = 0
  · subst b
    rcases golden_power_floor_ceil_pairs with ⟨_, _, _, hceil⟩
    have hlower : dualParameterLower 0 = 1 := by norm_num [dualParameterLower]
    have hupper : dualParameterUpper 0 = 2 := by
      simp only [dualParameterUpper, Int.cast_zero, zero_add, one_mul]
      rw [hceil]
      rfl
    left
    rw [hlower, hupper]
    rfl
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    have hxpos : 0 < (b : ℝ) * Real.goldenRatio ^ 2 := by positivity
    have hlower :
        dualParameterLower b = ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉ := by
      rw [dualParameterLower]
      apply max_eq_right
      rw [Int.le_ceil_iff]
      norm_num only [Int.cast_one, Int.cast_sub, Int.cast_zero]
      simpa using hxpos
    rw [dualParameterUpper, hlower]
    rcases dual_ceil_width b with hwidth | hwidth
    · left
      have :
          (⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ - 1) + 1 -
              ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉ = 2 := by
        omega
      rw [this]
      rfl
    · right
      have :
          (⌈((b : ℝ) + 1) * Real.goldenRatio ^ 2⌉ - 1) + 1 -
              ⌈(b : ℝ) * Real.goldenRatio ^ 2⌉ = 3 := by
        omega
      rw [this]
      rfl

/-- The second-coordinate support of an `a`-fiber is the stated closed integer interval. -/
theorem golden_fiber_b_support_eq_Icc (a : ℤ) (ha : 1 ≤ a) :
    fiberB '' goldenFiber a =
      Set.Icc (fiberSupportLower a) (fiberSupportUpper a) := by
  ext b
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hbnonneg := fiberB_nonneg_of_mem ha hv
    have hvindex := fiberIndex_eq_of_mem ha hv
    exact (fiberB_fiberIndex_iff ha hbnonneg).mp (by rw [hvindex])
  · intro hb
    have hbnonneg : 0 ≤ b := (fiberSupportLower_nonneg ha).trans hb.1
    have hB := (fiberB_fiberIndex_iff ha hbnonneg).mpr hb
    refine ⟨fiberIndex a b, ?_, hB⟩
    rw [goldenFiber_eq_image_Icc a ha]
    exact ⟨b, hb, rfl⟩

/-- The second coordinates occurring in a positive first-coordinate fiber form an interval. -/
theorem golden_fiber_b_support_ordConnected (a : ℤ) (ha : 1 ≤ a) :
    Set.OrdConnected (fiberB '' goldenFiber a) := by
  rw [golden_fiber_b_support_eq_Icc a ha]
  exact Set.ordConnected_Icc

example : (goldenFiber 1).ncard ∈ ({4, 5} : Set ℕ) := by
  exact golden_fiber_capacity_pair 1 (by norm_num)

#print axioms golden_fiber_capacity_pair

end D5.S1.Deficit.Beatty.FiberCapacityPair
