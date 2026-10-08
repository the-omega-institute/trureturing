/- GID: D5/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Quartic cell perturbations of the Robin price coordinate generate positive integer pulse sources. -/

import D5.S3.Analytic.Interpolation.ArtificialSourceCellEstimates
import D5.S1.Words.Mechanical.FloorFractShift
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.MellinWeightedVariation
open D5.S3.Analytic.Interpolation.ArtificialSourceCellEstimates

namespace D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract

local notation "c" => (1 / 128 : ℝ)
local notation "q" => (fun x : ℝ => (x * Real.log x)⁻¹)
local notation "k" => weight

/-- Conditions on the start of the half-line. -/
def Admissible (δ A : ℝ) : Prop :=
  (∀ a ∈ Ici A, 1 ≤ Real.log a ∧ epsilon a ≤ 1 ∧ 1 ≤ width δ a ∧ width δ a ≤ a) ∧
    AntitoneOn epsilon (Ici A)

/-- Consecutive cells in the adaptive grid. -/
def grid (δ A : ℝ) : ℕ → ℝ
  | 0 => A
  | j + 1 => grid δ A j + width δ (grid δ A j)

/-- The last grid point not exceeding x, with a finite search bound. -/
def cellIndex (δ A x : ℝ) : ℕ :=
  Nat.findGreatest (fun j => grid δ A j ≤ x) ⌊x - A⌋₊

/-- The assembled negative bump, extended by zero below the initial point. -/
def bump (δ A x : ℝ) : ℝ :=
  if A ≤ x then cellBump δ (grid δ A (cellIndex δ A x)) x else 0

/-- The perturbed price coordinate. -/
def coordinate (δ A x : ℝ) : ℝ := x - deriv (bump δ A) x / k x

/-- The integer-valued pulse source. -/
def source (δ A x : ℝ) : ℤ := ⌊coordinate δ A x⌋

/-- Its tail in the same Robin price coordinate. -/
def tail (δ A x : ℝ) : ℝ :=
  ∫ v in Ioi x, ((source δ A v : ℝ) - v) * k v

private theorem admissible_gt_one {δ A : ℝ} (hA : Admissible δ A) : 1 < A := by
  by_contra h
  have := (hA.1 1 (le_of_not_gt h)).1
  norm_num at this

private theorem grid_bounds {δ A : ℝ} (hA : Admissible δ A) (j : ℕ) :
    A + (j : ℝ) ≤ grid δ A j := by
  induction j with
  | zero => simp [grid]
  | succ j ih =>
    have hAj : A ≤ grid δ A j := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hw := (hA.1 _ hAj).2.2.1
    simp only [grid, Nat.cast_add, Nat.cast_one]
    linarith

private theorem grid_strictMono {δ A : ℝ} (hA : Admissible δ A) :
    StrictMono (grid δ A) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hAj : A ≤ grid δ A j := by
    linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  have hw := (hA.1 _ hAj).2.2.1
  simp only [grid]
  linarith

private theorem grid_index_bound {δ A x : ℝ} (hA : Admissible δ A)
    {j : ℕ} (hj : grid δ A j ≤ x) : j ≤ ⌊x - A⌋₊ := by
  have hg := grid_bounds hA j
  have hAx : A ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) j]
  apply (Nat.le_floor_iff (sub_nonneg.mpr hAx)).2
  linarith

private theorem cellIndex_spec {δ A x : ℝ} (hA : Admissible δ A) (hx : A ≤ x) :
    x ∈ Ico (grid δ A (cellIndex δ A x)) (grid δ A (cellIndex δ A x + 1)) := by
  constructor
  · exact Nat.findGreatest_spec (P := fun j => grid δ A j ≤ x)
      (m := 0) (Nat.zero_le _) (by simpa [grid] using hx)
  · by_contra h
    have hle := le_of_not_gt h
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _)
      (grid_index_bound hA hle) hle

private theorem cellIndex_eq {δ A x : ℝ} (hA : Admissible δ A) (j : ℕ)
    (hx : x ∈ Ico (grid δ A j) (grid δ A (j + 1))) : cellIndex δ A x = j := by
  apply Nat.findGreatest_eq_iff.2
  refine ⟨grid_index_bound hA hx.1, fun _ => hx.1, ?_⟩
  intro n hjn hn hnx
  have hgn := (grid_strictMono hA).monotone (Nat.succ_le_iff.2 hjn)
  exact (not_le.mpr hx.2) (hgn.trans hnx)

private theorem bump_on_cell {δ A x : ℝ} (hA : Admissible δ A) (j : ℕ)
    (hx : x ∈ Icc (grid δ A j) (grid δ A (j + 1))) :
    bump δ A x = cellBump δ (grid δ A j) x := by
  have hAj : A ≤ grid δ A j := by
    linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  rw [bump, if_pos (hAj.trans hx.1)]
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · rw [cellIndex_eq hA j ⟨hx.1, hlt⟩]
  · have hstep := (grid_strictMono hA) (Nat.lt_succ_self (j + 1))
    rw [cellIndex_eq hA (j + 1) ⟨le_rfl, hstep⟩]
    have hw := (hA.1 _ hAj).2.2.1
    have hw0 : width δ (grid δ A j) ≠ 0 := by linarith
    simp [cellBump, eta, grid, hw0]

local notation "etaOne" => (fun s : ℝ => 2 * s * (1 - s) * (1 - 2 * s))
local notation "etaTwo" => (fun s : ℝ => 2 - 12 * s + 12 * s ^ 2)
local notation "kernelSlope" => (fun x : ℝ =>
  -(2 * (Real.log x) ^ 2 + 3 * Real.log x + 2) / (x ^ 3 * (Real.log x) ^ 3))
local notation "cellSlope" => (fun δ a x : ℝ =>
  -(amplitude δ a / width δ a) * etaOne ((x - a) / width δ a))
local notation "cellSecond" => (fun δ a x : ℝ =>
  -(amplitude δ a / (width δ a) ^ 2) * etaTwo ((x - a) / width δ a))
local notation "rightSlope" => (fun δ A x : ℝ =>
  1 - (cellSecond δ (grid δ A (cellIndex δ A x)) x * k x -
    cellSlope δ (grid δ A (cellIndex δ A x)) x * kernelSlope x) / (k x) ^ 2)

private theorem admissible_exists {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₀ : ℝ, ∀ A ≥ A₀, Admissible δ A := by
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    Real.tendsto_log_atTop
  have heps := epsilon_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hwidth := width_eventually_bounds hδ
  have hev : ∀ᶠ a : ℝ in atTop,
      1 < a ∧ 1 ≤ Real.log a ∧ epsilon a ≤ 1 ∧ 1 ≤ width δ a ∧
        width δ a ≤ a ∧ 4 ≤ (Real.log a) ^ (1 / 4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), heps, hwidth,
      hu.eventually (eventually_ge_atTop (4 : ℝ))] with a ha he hw hu
    exact ⟨ha, hw.1, he.le, hw.2.1, hw.2.2, hu⟩
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 hev
  refine ⟨A₀, ?_⟩
  intro A hA
  have hdata : ∀ a ∈ Ici A, 1 < a ∧ 1 ≤ Real.log a ∧ epsilon a ≤ 1 ∧
      1 ≤ width δ a ∧ width δ a ≤ a ∧ 4 ≤ (Real.log a) ^ (1 / 4 : ℝ) :=
    fun a ha => hA₀ a (hA.trans ha)
  refine ⟨fun a ha => ⟨(hdata a ha).2.1, (hdata a ha).2.2.1,
    (hdata a ha).2.2.2.1, (hdata a ha).2.2.2.2.1⟩, ?_⟩
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici A)
  · intro a ha
    exact (epsilon_hasDerivAt (hdata a ha).1).continuousAt.continuousWithinAt
  · intro a ha
    exact (epsilon_hasDerivAt (hdata a (interior_subset ha)).1).hasDerivWithinAt
  · intro a ha
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact div_nonneg (Real.exp_pos _).le (by linarith [(hdata a (interior_subset ha)).1])
    · linarith [(hdata a (interior_subset ha)).2.2.2.2.2]

private theorem bump_hasDerivAt {δ A x : ℝ} (hA : Admissible δ A) (hx : A ≤ x) :
    HasDerivAt (bump δ A) (cellSlope δ (grid δ A (cellIndex δ A x)) x) x := by
  let j := cellIndex δ A x
  have hcell : x ∈ Ico (grid δ A j) (grid δ A (j + 1)) := cellIndex_spec hA hx
  have hAj : A ≤ grid δ A j := by
    linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  have hw : 0 < width δ (grid δ A j) := by linarith [(hA.1 _ hAj).2.2.1]
  have hpoint := bump_on_cell hA j (Ico_subset_Icc_self hcell)
  have hright : HasDerivWithinAt (bump δ A)
      (cellSlope δ (grid δ A j) x) (Ici x) x := by
    apply ((cell_derivatives hw).1.hasDerivWithinAt).congr_of_eventuallyEq _ hpoint
    filter_upwards [Icc_mem_nhdsGE_of_mem hcell] with y hy
    exact bump_on_cell hA j hy
  have hleft : HasDerivWithinAt (bump δ A)
      (cellSlope δ (grid δ A j) x) (Iic x) x := by
    rcases eq_or_lt_of_le hcell.1 with heq | hlt
    · have hzero : cellSlope δ (grid δ A j) x = 0 := by rw [← heq]; simp
      rw [hzero]
      by_cases hj : j = 0
      · have hxA : x = A := by simpa [hj, grid] using heq.symm
        rw [hxA]
        apply (hasDerivAt_const A (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          rcases lt_or_eq_of_le (show y ≤ A from hy) with hlt | rfl
          · simp [bump, not_le.mpr hlt]
          · simpa [hj, hxA, grid, cellBump, eta] using hpoint
        · simpa [hj, hxA, grid, cellBump, eta] using hpoint
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hAn : A ≤ grid δ A n := by
          linarith [grid_bounds hA n, Nat.cast_nonneg (α := ℝ) n]
        have hwn : 0 < width δ (grid δ A n) := by linarith [(hA.1 _ hAn).2.2.1]
        have hend : x = grid δ A (n + 1) := by simpa [hn] using heq.symm
        have hslope : cellSlope δ (grid δ A n) x = 0 := by
          rw [hend, grid]
          simp [hwn.ne']
        have hxn : x ∈ Ioc (grid δ A n) (grid δ A (n + 1)) := by
          rw [hend]
          exact ⟨(grid_strictMono hA) (Nat.lt_succ_self n), le_rfl⟩
        apply (((cell_derivatives hwn).1.congr_deriv hslope).hasDerivWithinAt).congr_of_eventuallyEq
          _ (bump_on_cell hA n (Ioc_subset_Icc_self hxn))
        filter_upwards [Icc_mem_nhdsLE_of_mem hxn] with y hy
        exact bump_on_cell hA n hy
    · apply ((cell_derivatives hw).1.hasDerivWithinAt).congr_of_eventuallyEq _ hpoint
      filter_upwards [Icc_mem_nhdsLE_of_mem ⟨hlt, hcell.2.le⟩] with y hy
      exact bump_on_cell hA j hy
  have hd := hright.union hleft
  rw [Ici_union_Iic] at hd
  exact hd.hasDerivAt (by simp)

private theorem bump_deriv_on_cell {δ A x : ℝ} (hA : Admissible δ A) (j : ℕ)
    (hx : x ∈ Icc (grid δ A j) (grid δ A (j + 1))) :
    deriv (bump δ A) x = cellSlope δ (grid δ A j) x := by
  have hAj : A ≤ grid δ A j := by
    linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  rw [(bump_hasDerivAt hA (hAj.trans hx.1)).deriv]
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · rw [cellIndex_eq hA j ⟨hx.1, hlt⟩]
  · rw [cellIndex_eq hA (j + 1) ⟨le_rfl, (grid_strictMono hA) (Nat.lt_succ_self _)⟩]
    have hw : width δ (grid δ A j) ≠ 0 := by linarith [(hA.1 _ hAj).2.2.1]
    simp [grid, hw]

private theorem bump_deriv_continuous {δ A : ℝ} (hA : Admissible δ A) :
    ContinuousOn (deriv (bump δ A)) (Ici A) := by
  intro x hx
  let j := cellIndex δ A x
  have hcell : x ∈ Ico (grid δ A j) (grid δ A (j + 1)) := cellIndex_spec hA hx
  have hAj : A ≤ grid δ A j := by
    linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  have hw : 0 < width δ (grid δ A j) := by linarith [(hA.1 _ hAj).2.2.1]
  have hright : ContinuousWithinAt (deriv (bump δ A)) (Ici x) x := by
    apply ((cell_derivatives hw).2.continuousAt.continuousWithinAt).congr_of_eventuallyEq
      _ (bump_deriv_on_cell hA j (Ico_subset_Icc_self hcell))
    filter_upwards [Icc_mem_nhdsGE_of_mem hcell] with y hy
    exact bump_deriv_on_cell hA j hy
  by_cases hxA : x = A
  · simpa only [hxA] using hright
  have hleft : ContinuousWithinAt (deriv (bump δ A)) (Iic x) x := by
    rcases eq_or_lt_of_le hcell.1 with heq | hlt
    · have hj : j ≠ 0 := by
        intro hj
        apply hxA
        simpa [hj, grid] using heq.symm
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hAn : A ≤ grid δ A n := by
        linarith [grid_bounds hA n, Nat.cast_nonneg (α := ℝ) n]
      have hwn : 0 < width δ (grid δ A n) := by linarith [(hA.1 _ hAn).2.2.1]
      have hxn : x ∈ Ioc (grid δ A n) (grid δ A (n + 1)) := by
        have hend : x = grid δ A (n + 1) := by simpa [hn] using heq.symm
        rw [hend]
        exact ⟨(grid_strictMono hA) (Nat.lt_succ_self n), le_rfl⟩
      apply ((cell_derivatives hwn).2.continuousAt.continuousWithinAt).congr_of_eventuallyEq
        _ (bump_deriv_on_cell hA n (Ioc_subset_Icc_self hxn))
      filter_upwards [Icc_mem_nhdsLE_of_mem hxn] with y hy
      exact bump_deriv_on_cell hA n hy
    · apply ((cell_derivatives hw).2.continuousAt.continuousWithinAt).congr_of_eventuallyEq
        _ (bump_deriv_on_cell hA j (Ico_subset_Icc_self hcell))
      filter_upwards [Icc_mem_nhdsLE_of_mem ⟨hlt, hcell.2.le⟩] with y hy
      exact bump_deriv_on_cell hA j hy
  have hc := hright.union hleft
  rw [Ici_union_Iic] at hc
  exact (hc.continuousAt (by simp)).continuousWithinAt

private theorem coordinate_continuous {δ A : ℝ} (hA : Admissible δ A) :
    ContinuousOn (coordinate δ A) (Ici A) := by
  apply continuousOn_id.sub
  apply (bump_deriv_continuous hA).div
  · intro x hx
    exact (kernel_hasDerivAt ((admissible_gt_one hA).trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx1 := (admissible_gt_one hA).trans_le hx
    have hx0 : 0 < x := by linarith
    have hk : 0 < k x := by unfold weight; positivity [Real.log_pos hx1]
    exact hk.ne'

private theorem coordinate_right_deriv {δ A x : ℝ} (hA : Admissible δ A) (hx : A ≤ x) :
    HasDerivWithinAt (coordinate δ A) (rightSlope δ A x) (Ici x) x ∧
      |rightSlope δ A x - 1| ≤ epsilon x ∧ |rightSlope δ A x - 1| ≤ 1 / 2 := by
  let j := cellIndex δ A x
  let a := grid δ A j
  have hcell : x ∈ Ico a (grid δ A (j + 1)) := cellIndex_spec hA hx
  have hAa : A ≤ a := by linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  have ha : 1 < a := (admissible_gt_one hA).trans_le hAa
  have hdata := hA.1 a hAa
  have hw : 0 < width δ a := by linarith [hdata.2.2.1]
  have hxcc : x ∈ Icc a (a + width δ a) := by
    simpa only [grid] using Ico_subset_Icc_self hcell
  have hx0 : 0 < x := by linarith [hcell.1]
  have hk : 0 < k x := by
    unfold weight
    positivity [Real.log_pos (ha.trans_le hcell.1)]
  have hd := (hasDerivAt_id x).sub
    ((cell_derivatives hw).2.fun_div (kernel_hasDerivAt (ha.trans_le hcell.1)) hk.ne')
  change HasDerivAt (fun y : ℝ => y - cellSlope δ a y / k y) (rightSlope δ A x) x at hd
  have hpoint : coordinate δ A x = x - cellSlope δ a x / k x := by
    rw [coordinate, bump_deriv_on_cell hA j (Ico_subset_Icc_self hcell)]
  have hest := (cell_estimates ha hdata.1 hw hdata.2.2.2 hxcc).2
  rw [hd.deriv] at hest
  have heps := epsilon_cell_comparison ha hdata.1
    (show x ∈ Icc a (2 * a) from ⟨hcell.1, by linarith [hxcc.2, hdata.2.2.2]⟩)
  have hexpos : 0 ≤ epsilon x := by unfold epsilon; positivity [Real.log_pos (ha.trans_le hcell.1)]
  refine ⟨?_, ?_, ?_⟩
  · apply hd.hasDerivWithinAt.congr_of_eventuallyEq _ hpoint
    filter_upwards [Icc_mem_nhdsGE_of_mem hcell] with y hy
    rw [coordinate, bump_deriv_on_cell hA j hy]
  · dsimp only at hest ⊢
    nlinarith
  · dsimp only at hest ⊢
    nlinarith [hdata.2.1]

private theorem coordinate_increment_bound {δ A a b C : ℝ} (hA : Admissible δ A)
    (ha : A ≤ a) (hab : a ≤ b)
    (hbound : ∀ x ∈ Ico a b, |rightSlope δ A x - 1| ≤ C) :
    |coordinate δ A b - coordinate δ A a - (b - a)| ≤ C * (b - a) := by
  have hsub : Icc a b ⊆ Ici A := fun x hx => ha.trans hx.1
  have hc := ((coordinate_continuous hA).mono hsub).sub continuousOn_id
  have hd : ∀ x ∈ Ico a b, HasDerivWithinAt (fun y : ℝ => coordinate δ A y - y)
      (rightSlope δ A x - 1) (Ici x) x := by
    intro x hx
    exact (coordinate_right_deriv hA (ha.trans hx.1)).1.sub
      (hasDerivAt_id x).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment hc hd
    (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx) b
    (right_mem_Icc.2 hab)
  have heq : coordinate δ A b - b - (coordinate δ A a - a) =
      coordinate δ A b - coordinate δ A a - (b - a) := by ring
  simpa only [Real.norm_eq_abs, Pi.sub_apply, id_eq, heq] using h

private theorem coordinate_increment {δ A a t : ℝ} (hA : Admissible δ A)
    (ha : A ≤ a) (ht : 0 ≤ t) :
    |coordinate δ A (a + t) - coordinate δ A a - t| ≤ epsilon a * t := by
  simpa only [add_sub_cancel_left] using coordinate_increment_bound hA ha
    (show a ≤ a + t by linarith) (fun x hx =>
      (coordinate_right_deriv hA (ha.trans hx.1)).2.1.trans
        (hA.2 ha (ha.trans hx.1) hx.1))

private theorem coordinate_strictMono {δ A : ℝ} (hA : Admissible δ A) :
    StrictMonoOn (coordinate δ A) (Ici A) := by
  intro a ha b hb hab
  have h := coordinate_increment_bound hA ha hab.le
    (fun x hx => (coordinate_right_deriv hA (ha.trans hx.1)).2.2)
  have hlow := (abs_le.1 h).1
  linarith

private theorem source_increment {δ A a t : ℝ} (hA : Admissible δ A)
    (ha : A ≤ a) (ht : 0 ≤ t) :
    |(source δ A (a + t) : ℝ) - (source δ A a : ℝ) - t| ≤ epsilon a * t + 1 := by
  let u := coordinate δ A a
  let v := coordinate δ A (a + t)
  have hfloor : ⌊v⌋ - ⌊u⌋ = ⌊Int.fract u + (v - u)⌋ := by
    convert D5.S1.Words.Mechanical.FloorFractShift.floor_add_sub_floor u (v - u) using 1
    congr 2
    ring
  have hsup := Int.floor_le (Int.fract u + (v - u))
  have hinf := Int.lt_floor_add_one (Int.fract u + (v - u))
  have hfrac0 := Int.fract_nonneg u
  have hfrac1 := Int.fract_lt_one u
  have hround : |(source δ A (a + t) : ℝ) - (source δ A a : ℝ) - (v - u)| ≤ 1 := by
    change |(⌊v⌋ : ℝ) - (⌊u⌋ : ℝ) - (v - u)| ≤ 1
    rw [← Int.cast_sub, hfloor]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hinc := coordinate_increment hA ha ht
  have heq : (source δ A (a + t) : ℝ) - (source δ A a : ℝ) - t =
      ((source δ A (a + t) : ℝ) - (source δ A a : ℝ) - (v - u)) + (v - u - t) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by dsimp [u, v] at *; linarith)

private theorem coordinate_global_bound {δ A x : ℝ} (hδ : 0 < δ)
    (hA : Admissible δ A) (hx : A ≤ x) :
    |coordinate δ A x - x| ≤ 4 * c * x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2) := by
  let j := cellIndex δ A x
  let a := grid δ A j
  have hcell := cellIndex_spec hA hx
  have hAa : A ≤ a := by linarith [grid_bounds hA j, Nat.cast_nonneg (α := ℝ) j]
  have ha : 1 < a := (admissible_gt_one hA).trans_le hAa
  have hdata := hA.1 a hAa
  have hw : 0 < width δ a := by linarith [hdata.2.2.1]
  have hxcell : x ∈ Icc a (a + width δ a) := by
    simpa only [grid] using Ico_subset_Icc_self hcell
  have hest := (cell_estimates ha hdata.1 hw hdata.2.2.2 hxcell).1
  have hlog : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hcell.1
  have hLa0 : 0 ≤ Real.log a := le_of_lt (Real.log_pos ha)
  have hx0 : 0 ≤ x := le_trans (by linarith : (0 : ℝ) ≤ a) hcell.1
  have hLx0 : 0 ≤ Real.log x := hLa0.trans hlog
  have hu : 0 ≤ (Real.log a) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hLa0 _
  have hexp : Real.exp (-(Real.log a) ^ (1 / 4 : ℝ) / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  calc
    |coordinate δ A x - x| = |cellSlope δ a x / k x| := by
      rw [coordinate, bump_deriv_on_cell hA j (Ico_subset_Icc_self hcell)]
      dsimp [a]
      rw [sub_sub_cancel_left, abs_neg]
    _ ≤ 4 * c * epsilon a * width δ a := hest
    _ = 4 * c * (a ^ (3 / 4 : ℝ) *
        Real.exp (-(Real.log a) ^ (1 / 4 : ℝ) / 2) * (Real.log a) ^ (δ + 1 / 2)) := by
      rw [mul_assoc (4 * c), epsilon_width_identity ha]
    _ ≤ 4 * c * x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2) := by
      calc
        _ ≤ 4 * c * (x ^ (3 / 4 : ℝ) * 1 * (Real.log x) ^ (δ + 1 / 2)) := by
          gcongr <;> first | positivity | exact hcell.1 | exact hLa0 | linarith
        _ = _ := by ring

private theorem source_global_bound {δ A x : ℝ} (hδ : 0 < δ)
    (hA : Admissible δ A) (hx : A ≤ x) :
    |(source δ A x : ℝ) - x| ≤
      4 * c * x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2) + 1 := by
  have hround : |(source δ A x : ℝ) - coordinate δ A x| ≤ 1 := by
    unfold source
    exact abs_le.2 ⟨by linarith [Int.lt_floor_add_one (coordinate δ A x)],
      by linarith [Int.floor_le (coordinate δ A x)]⟩
  have heq : (source δ A x : ℝ) - x =
      ((source δ A x : ℝ) - coordinate δ A x) + (coordinate δ A x - x) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith [coordinate_global_bound hδ hA hx])

private theorem bump_contDiffOn {δ A : ℝ} (hA : Admissible δ A) :
    ContDiffOn ℝ 1 (bump δ A) (Ici A) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici A)).2
  refine ⟨fun x hx => (bump_hasDerivAt hA hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply (bump_deriv_continuous hA).congr
  intro x hx
  exact (bump_hasDerivAt hA hx).differentiableAt.derivWithin (uniqueDiffOn_Ici A x hx)

private theorem coordinate_grid {δ A : ℝ} (hA : Admissible δ A) (j : ℕ) :
    coordinate δ A (grid δ A j) = grid δ A j := by
  rw [coordinate, bump_deriv_on_cell hA j
    ⟨le_rfl, (grid_strictMono hA).monotone (Nat.le_succ j)⟩]
  simp

private theorem source_nonnegative {δ A x : ℝ} (hA : Admissible δ A) (hx : A ≤ x) :
    0 ≤ source δ A x := by
  apply Int.floor_nonneg.2
  have hmono := (coordinate_strictMono hA).monotoneOn (show A ∈ Ici A from self_mem_Ici) hx hx
  have hstart : coordinate δ A A = A := by simpa [grid] using coordinate_grid hA 0
  rw [hstart] at hmono
  linarith [admissible_gt_one hA]

private theorem source_monotone {δ A : ℝ} (hA : Admissible δ A) :
    MonotoneOn (source δ A) (Ici A) := by
  intro x hx y hy hxy
  exact Int.floor_mono ((coordinate_strictMono hA).monotoneOn hx hy hxy)

private theorem source_right_limit {δ A x : ℝ} (hA : Admissible δ A) (hx : A ≤ x) :
    Tendsto (source δ A) (𝓝[≥] x) (pure (source δ A x)) := by
  apply (tendsto_floor_right_pure_floor (coordinate δ A x)).comp
  apply tendsto_nhdsWithin_iff.2
  refine ⟨((coordinate_continuous hA) x hx).mono (Ici_subset_Ici.mpr hx), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (coordinate_strictMono hA).monotoneOn hx (hx.trans hy) hy

private theorem source_left_limit {δ A x : ℝ} (hA : Admissible δ A) (hx : A < x)
    (n : ℤ) (hn : coordinate δ A x = n) :
    Tendsto (source δ A) (𝓝[<] x) (pure (n - 1)) := by
  apply (tendsto_floor_left_pure_sub_one n).comp
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · rw [← hn]
    exact ((coordinate_continuous hA) x hx.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hx))
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx), self_mem_nhdsWithin] with y hy hxy
    rw [← hn]
    exact (coordinate_strictMono hA) hy.le hx.le hxy

private theorem source_events_finite {δ A a b : ℝ} (hA : Admissible δ A)
    (ha : A ≤ a) :
    {x ∈ Icc a b | ∃ n : ℤ, coordinate δ A x = n}.Finite := by
  let E := {x ∈ Icc a b | ∃ n : ℤ, coordinate δ A x = n}
  have himage : source δ A '' E ⊆ Icc (source δ A a) (source δ A b) := by
    rintro n ⟨x, hx, rfl⟩
    exact ⟨source_monotone hA ha (ha.trans hx.1.1) hx.1.1,
      source_monotone hA (ha.trans hx.1.1) (ha.trans (hx.1.1.trans hx.1.2)) hx.1.2⟩
  apply ((Set.finite_Icc _ _).subset himage).of_finite_image
  intro x hx y hy heq
  obtain ⟨m, hm⟩ := hx.2
  obtain ⟨n, hn⟩ := hy.2
  have hmn : m = n := by simpa only [source, hm, hn, Int.floor_intCast] using heq
  apply (coordinate_strictMono hA).injOn (ha.trans hx.1.1) (ha.trans hy.1.1)
  rw [hm, hn, hmn]

private theorem logarithm_power_bound (r : ℝ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ r ≤ x ^ (1 / 8 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop r
    (by norm_num : (0 : ℝ) < 1 / 8)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _),
    abs_of_nonneg (Real.rpow_nonneg (Real.log_pos hx1).le _)] using hx

private theorem source_pnt_bound {δ A : ℝ} (hδ : 0 < δ) (hA : Admissible δ A)
    (c₀ : ℝ) :
    Asymptotics.IsBigO atTop (fun x => (source δ A x : ℝ) - x)
      (fun x => x * Real.exp (-c₀ * Real.sqrt (Real.log x))) := by
  have hs : Tendsto (fun L : ℝ => Real.sqrt L / L) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.sqrt_eq_rpow, show -(1 / 2 : ℝ) = 1 / 2 - 1 by ring,
      Real.rpow_sub hL, Real.rpow_one]
  have hs₀ : Tendsto (fun L : ℝ => c₀ * (Real.sqrt L / L)) atTop (𝓝 0) := by
    simpa using hs.const_mul c₀
  have hsmall := (hs₀.comp Real.tendsto_log_atTop).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  apply Asymptotics.IsBigO.of_bound (4 * c + 1)
  filter_upwards [hsmall, logarithm_power_bound (δ + 1 / 2),
    eventually_ge_atTop A, eventually_gt_atTop (1 : ℝ)] with x hsmall hlog hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hsmall' : c₀ * Real.sqrt (Real.log x) ≤ Real.log x / 8 := by
    dsimp only [Function.comp_def] at hsmall
    have heq : c₀ * (Real.sqrt (Real.log x) / Real.log x) =
        (c₀ * Real.sqrt (Real.log x)) / Real.log x := by ring
    rw [heq] at hsmall
    linarith [(div_lt_iff₀ hL).1 hsmall]
  have hmajor : x ^ (7 / 8 : ℝ) ≤ x * Real.exp (-c₀ * Real.sqrt (Real.log x)) := by
    calc
      x ^ (7 / 8 : ℝ) = x * Real.exp (-Real.log x / 8) := by
        rw [Real.rpow_def_of_pos hx0]
        conv_rhs => lhs; rw [← Real.exp_log hx0]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hx0.le
  have hp : x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2) ≤ x ^ (7 / 8 : ℝ) := by
    calc
      _ ≤ x ^ (3 / 4 : ℝ) * x ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hone : 1 ≤ x ^ (7 / 8 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
  have hbound := source_global_bound hδ hA hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hx0 (Real.exp_pos _))]
  nlinarith

private theorem kernel_bound {x : ℝ} (hx : 1 < x) (hL : 1 ≤ Real.log x) :
    0 < k x ∧ k x ≤ 2 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  refine ⟨by unfold weight; positivity, ?_⟩
  unfold weight
  apply (div_le_div_iff₀ (by positivity : 0 < x ^ 2 * (Real.log x) ^ 2)
    (by positivity : 0 < x ^ 2)).2
  nlinarith [mul_nonneg (sq_nonneg x)
    (show 0 ≤ 2 * (Real.log x) ^ 2 - (Real.log x + 1) by nlinarith)]

private theorem bump_deriv_integrable {δ A : ℝ} (hδ : 0 < δ) (hA : Admissible δ A) :
    IntegrableOn (deriv (bump δ A)) (Ici A) := by
  have ho : Asymptotics.IsBigO atTop (deriv (bump δ A))
      (fun x : ℝ => x ^ (-9 / 8 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (8 * c)
    filter_upwards [logarithm_power_bound (δ + 1 / 2), eventually_ge_atTop A] with x hlog hx
    have hx1 := (admissible_gt_one hA).trans_le hx
    have hx0 : 0 < x := by linarith
    have hk := kernel_bound hx1 (hA.1 x hx).1
    have hcoord : deriv (bump δ A) x = -(coordinate δ A x - x) * k x := by
      unfold coordinate
      field_simp [hk.1.ne']
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
      hcoord, abs_mul, abs_neg, abs_of_pos hk.1]
    have hp : x ^ (3 / 4 : ℝ) * x ^ (1 / 8 : ℝ) * (2 / x ^ 2) =
        2 * x ^ (-9 / 8 : ℝ) := by
      have hinv : (x ^ 2)⁻¹ = x ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hx0.le, Real.rpow_two]
      simp only [div_eq_mul_inv]
      rw [hinv]
      calc
        _ = 2 * ((x ^ (3 / 4 : ℝ) * x ^ (1 / 8 : ℝ)) * x ^ (-2 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
    calc
      _ ≤ (4 * c * x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2)) * (2 / x ^ 2) :=
        mul_le_mul (coordinate_global_bound hδ hA hx) hk.2 hk.1.le (by positivity [Real.log_pos hx1])
      _ ≤ (4 * c * x ^ (3 / 4 : ℝ) * x ^ (1 / 8 : ℝ)) * (2 / x ^ 2) := by gcongr
      _ = _ := by linear_combination 4 * c * hp
  exact ((bump_deriv_continuous hA).locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho (integrableAtFilter_rpow_atTop_iff.2 (by norm_num))

private theorem price_hasDerivAt {x : ℝ} (hx : 1 < x) : HasDerivAt q (-k x) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')).inv
    (mul_ne_zero hx0.ne' hL.ne')
  convert! hd using 1 <;> first
  | rfl
  | (unfold weight; field_simp; ring)

private theorem price_tendsto_zero : Tendsto q atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact inv_nonneg.mpr (mul_nonneg (by linarith) (Real.log_pos hx).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hL
    apply inv_anti₀ (by linarith : (0 : ℝ) < x)
    nlinarith

private theorem kernel_tail {x : ℝ} (hx : 1 < x) :
    IntegrableOn k (Ioi x) ∧ (∫ y in Ioi x, k y) = q x := by
  have hd : ∀ y ∈ Ici x, HasDerivAt q (-k y) y :=
    fun y hy => price_hasDerivAt (hx.trans_le hy)
  have hn : ∀ y ∈ Ioi x, -k y ≤ 0 := by
    intro y hy
    have hy1 := hx.trans hy
    have hy0 : 0 < y := by linarith
    unfold weight
    positivity [Real.log_pos hy1]
  have hi := integrableOn_Ioi_deriv_of_nonpos' hd hn price_tendsto_zero
  have hv := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi price_tendsto_zero
  refine ⟨by simpa only [neg_neg] using hi.neg, ?_⟩
  rw [integral_neg] at hv
  linarith

private theorem bump_tendsto_zero {δ A : ℝ} (hδ : 0 < δ) (hA : Admissible δ A) :
    Tendsto (bump δ A) atTop (𝓝 0) := by
  have hi := (bump_deriv_integrable hδ hA).mono_set Ioi_subset_Ici_self
  have ht := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (fun x hx => (bump_hasDerivAt hA hx.le).differentiableAt.hasDerivAt) hi
  have hg : Tendsto (grid δ A) atTop atTop :=
    tendsto_atTop_mono (grid_bounds hA)
      (tendsto_atTop_add_const_left atTop A tendsto_natCast_atTop_atTop)
  have hzero : (bump δ A ∘ grid δ A) = fun _ => (0 : ℝ) := by
    funext j
    rw [Function.comp_def, bump_on_cell hA j
      ⟨le_rfl, (grid_strictMono hA).monotone (Nat.le_succ j)⟩]
    simp [cellBump, eta]
  have heq : limUnder atTop (bump δ A) = 0 := by
    apply tendsto_nhds_unique (ht.comp hg)
    rw [hzero]
    exact tendsto_const_nhds
  rwa [heq] at ht

private theorem tail_contract {δ A x : ℝ} (hδ : 0 < δ) (hA : Admissible δ A) (hx : A ≤ x) :
    IntegrableOn (fun y => ((source δ A y : ℝ) - y) * k y) (Ioi x) ∧
      bump δ A x - q x ≤ tail δ A x ∧ tail δ A x ≤ bump δ A x := by
  have hx1 := (admissible_gt_one hA).trans_le hx
  have hk := kernel_tail hx1
  have hd := (bump_deriv_integrable hδ hA).mono_set
    (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hx))
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => (bump_hasDerivAt hA (hx.trans hy)).differentiableAt.hasDerivAt)
    hd (bump_tendsto_zero hδ hA)
  let R : ℝ → ℝ := fun y => ((source δ A y : ℝ) - coordinate δ A y) * k y
  have hc := (coordinate_continuous hA).mono
    (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hx))
  have hcm : AEStronglyMeasurable (coordinate δ A) (volume.restrict (Ioi x)) :=
    hc.aestronglyMeasurable measurableSet_Ioi
  have hsm : AEStronglyMeasurable (fun y => (source δ A y : ℝ))
      (volume.restrict (Ioi x)) :=
    (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp Int.measurable_floor).comp_aemeasurable
      (hc.aemeasurable measurableSet_Ioi)).aestronglyMeasurable
  have hkm : AEStronglyMeasurable k (volume.restrict (Ioi x)) := hk.1.aestronglyMeasurable
  have hrange : ∀ y ∈ Ioi x, -k y ≤ R y ∧ R y ≤ 0 ∧ |R y| ≤ k y := by
    intro y hy
    have hy1 := hx1.trans hy
    have hy0 : 0 < y := by linarith
    have hky : 0 ≤ k y := by unfold weight; positivity [Real.log_pos hy1]
    have hfloor : -1 ≤ (source δ A y : ℝ) - coordinate δ A y ∧
        (source δ A y : ℝ) - coordinate δ A y ≤ 0 := by
      unfold source
      constructor <;> linarith [Int.floor_le (coordinate δ A y),
        Int.lt_floor_add_one (coordinate δ A y)]
    have hl := mul_le_mul_of_nonneg_right hfloor.1 hky
    have hu := mul_nonpos_of_nonpos_of_nonneg hfloor.2 hky
    refine ⟨by simpa [R] using hl, hu, ?_⟩
    change |((source δ A y : ℝ) - coordinate δ A y) * k y| ≤ k y
    rw [abs_of_nonpos hu]
    linarith
  have hR : IntegrableOn R (Ioi x) := by
    apply hk.1.mono' ((hsm.sub hcm).mul hkm)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [Real.norm_eq_abs] using (hrange y hy).2.2
  have hid : ∀ y ∈ Ioi x,
      ((source δ A y : ℝ) - y) * k y = -deriv (bump δ A) y + R y := by
    intro y hy
    have hy1 := hx1.trans hy
    have hy0 : 0 < y := by linarith
    have hky : k y ≠ 0 := by unfold weight; positivity [Real.log_pos hy1]
    dsimp [R, coordinate]
    field_simp
    ring
  have hi : IntegrableOn (fun y => ((source δ A y : ℝ) - y) * k y) (Ioi x) :=
    (hd.neg.add hR).congr_fun (fun y hy => (hid y hy).symm) measurableSet_Ioi
  have heq : tail δ A x = bump δ A x + ∫ y in Ioi x, R y := by
    unfold tail
    rw [setIntegral_congr_fun measurableSet_Ioi hid, integral_add hd.neg hR, integral_neg]
    linarith
  have hlo := setIntegral_mono_on hk.1.neg hR measurableSet_Ioi (fun y hy => (hrange y hy).1)
  have hhi := setIntegral_mono_on hR (integrable_zero _ _ _) measurableSet_Ioi
    (fun y hy => (hrange y hy).2.1)
  rw [integral_neg, hk.2] at hlo
  simp only [integral_zero] at hhi
  exact ⟨hi, by linarith, by linarith⟩

private theorem source_between_events {δ A x : ℝ} (hA : Admissible δ A)
    (hx : A < x) (hn : ¬ ∃ n : ℤ, coordinate δ A x = n) :
    ∀ᶠ y in 𝓝 x, source δ A y = source δ A x := by
  have hc : ContinuousAt (coordinate δ A) x :=
    ((coordinate_continuous hA) x hx.le).continuousAt (Ici_mem_nhds hx)
  have hlo : (source δ A x : ℝ) < coordinate δ A x := by
    refine lt_of_le_of_ne (Int.floor_le _) ?_
    intro heq
    exact hn ⟨source δ A x, heq.symm⟩
  have hev := hc.eventually (Ioo_mem_nhds hlo (Int.lt_floor_add_one _))
  filter_upwards [hev] with y hy
  exact Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩

/-- The adaptive source satisfies the regularity, increment, asymptotic and tail contracts. -/
theorem result (δ : ℝ) (hδ : 0 < δ) :
    (∃ A₀ : ℝ, ∀ A ≥ A₀, Admissible δ A) ∧
    ∀ A : ℝ, Admissible δ A →
      ContDiffOn ℝ 1 (bump δ A) (Ici A) ∧
      ContinuousOn (coordinate δ A) (Ici A) ∧
      StrictMonoOn (coordinate δ A) (Ici A) ∧
      MonotoneOn (source δ A) (Ici A) ∧
      (∀ x ≥ A, 0 ≤ source δ A x ∧
        Tendsto (source δ A) (𝓝[≥] x) (pure (source δ A x))) ∧
      (∀ x > A, (∀ n : ℤ, coordinate δ A x = n →
        source δ A x = n ∧ Tendsto (source δ A) (𝓝[<] x) (pure (n - 1))) ∧
        ((¬ ∃ n : ℤ, coordinate δ A x = n) →
          ∀ᶠ y in 𝓝 x, source δ A y = source δ A x)) ∧
      (∀ a ≥ A, ∀ b : ℝ,
        {x ∈ Icc a b | ∃ n : ℤ, coordinate δ A x = n}.Finite) ∧
      (∀ a ≥ A, ∀ t ≥ 0,
        |(source δ A (a + t) : ℝ) - (source δ A a : ℝ) - t| ≤ epsilon a * t + 1) ∧
      (∀ x ≥ A, |(source δ A x : ℝ) - x| ≤
        4 * c * x ^ (3 / 4 : ℝ) * (Real.log x) ^ (δ + 1 / 2) + 1) ∧
      (∀ c₀ > 0, Asymptotics.IsBigO atTop (fun x => (source δ A x : ℝ) - x)
        (fun x => x * Real.exp (-c₀ * Real.sqrt (Real.log x)))) ∧
      (∀ x ≥ A,
        IntegrableOn (fun y => ((source δ A y : ℝ) - y) * k y) (Ioi x) ∧
        bump δ A x - q x ≤ tail δ A x ∧ tail δ A x ≤ bump δ A x) := by
  refine ⟨admissible_exists hδ, ?_⟩
  intro A hA
  refine ⟨bump_contDiffOn hA, coordinate_continuous hA, coordinate_strictMono hA,
    source_monotone hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => ⟨source_nonnegative hA hx, source_right_limit hA hx⟩
  · intro x hx
    refine ⟨?_, source_between_events hA hx⟩
    intro n hn
    exact ⟨by simp [source, hn], source_left_limit hA hx n hn⟩
  · exact fun a ha b => source_events_finite hA ha
  · exact fun a ha t ht => source_increment hA ha ht
  · exact fun x hx => source_global_bound hδ hA hx
  · exact fun c₀ _ => source_pnt_bound hδ hA c₀
  · exact fun x hx => tail_contract hδ hA hx

end D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract




