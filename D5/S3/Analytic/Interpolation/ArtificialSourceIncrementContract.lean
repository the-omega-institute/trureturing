/- GID: D5/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Quartic cell perturbations of the Robin price coordinate generate positive integer pulse sources. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S1.Words.Mechanical.FloorFractShift
import Mathlib.Analysis.Calculus.ContDiff.Basic
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

namespace D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract

local notation "c" => (1 / 128 : ℝ)
local notation "q" => (fun x : ℝ => (x * Real.log x)⁻¹)
local notation "k" => weight

/-- The quartic bump has a double zero at either endpoint. -/
def eta (s : ℝ) : ℝ := s ^ 2 * (1 - s) ^ 2

/-- The local increment budget. -/
def epsilon (a : ℝ) : ℝ := Real.log a * Real.exp (-(Real.log a) ^ (1 / 4 : ℝ))

/-- The cell width for a fixed positive logarithmic excess. -/
def width (δ a : ℝ) : ℝ :=
  a ^ (3 / 4 : ℝ) * Real.exp ((Real.log a) ^ (1 / 4 : ℝ) / 2) /
    Real.sqrt (Real.log a) * (Real.log a) ^ δ

/-- The height of the cell's negative bump. -/
def amplitude (δ a : ℝ) : ℝ := c * (Real.log a) ^ (2 * δ - 1) / Real.sqrt a

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

/-- Polynomial continuation of the bump in one cell. -/
def cellBump (δ a x : ℝ) : ℝ :=
  -amplitude δ a * eta ((x - a) / width δ a)

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

private theorem eta_derivatives (s : ℝ) :
    HasDerivAt eta (etaOne s) s ∧ HasDerivAt etaOne (etaTwo s) s := by
  constructor
  · convert ((hasDerivAt_id s).pow 2).mul
      (((hasDerivAt_const s 1).sub (hasDerivAt_id s)).pow 2) using 1 <;> first | rfl | (dsimp [eta]; ring)
  · convert ((((hasDerivAt_id s).const_mul 2).mul
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s))).mul
        ((hasDerivAt_const s 1).sub ((hasDerivAt_id s).const_mul 2))) using 1 <;> first | rfl | (dsimp; ring)

private theorem eta_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ eta s ∧ eta s ≤ 1 / 16 ∧ |etaOne s| ≤ 1 / 2 ∧ |etaTwo s| ≤ 2 := by
  have hp : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (by linarith [hs.2])
  have hpq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hfactor : |1 - 2 * s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨by unfold eta; positivity, ?_, ?_, ?_⟩
  · unfold eta
    nlinarith [sq_nonneg (s * (1 - s) - 1 / 4)]
  · dsimp only
    rw [show 2 * s * (1 - s) = 2 * (s * (1 - s)) by ring]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (s * (1 - s)))]
    nlinarith [mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * (s * (1 - s)))]
  · exact abs_le.mpr ⟨by nlinarith [sq_nonneg (s - 1 / 2)], by nlinarith⟩

private theorem kernel_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt k (kernelSlope x) x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hd := (hasDerivAt_scaleWeight hx0 (by norm_num : (0 : ℝ) < 1)
    (by simpa using hx)).fun_div (hasDerivAt_id x) hx0.ne'
  have hfun : (fun z : ℝ => scaleWeight z 1 / z) = k := by
    ext z
    rw [scaleWeight_eq]
    by_cases hz : z = 0
    · simp [hz, weight]
    · simp [hz]
  dsimp only [id] at hd
  rw [hfun] at hd
  convert! hd using 1 <;> first
  | rfl
  | (unfold scaleDerivative scaleWeight; norm_num; field_simp [hx0.ne', hl.ne'] <;> ring)

private theorem kernel_cell_bounds {a x : ℝ} (ha : 1 < a) (hLa : 1 ≤ Real.log a)
    (hx : x ∈ Icc a (2 * a)) :
    0 < k x ∧ (k x)⁻¹ ≤ 8 * a ^ 2 * Real.log a ∧
      |kernelSlope x| / k x ≤ 7 / a := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hL : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx.1
  have hLx : 1 ≤ Real.log x := hLa.trans hL
  have hl0 : 0 < Real.log x := by linarith
  have hupper : Real.log x ≤ 2 * Real.log a := by
    have h := Real.log_le_log hx0 hx.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at h
    have htwo : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hk : 0 < k x := by unfold weight; positivity
  refine ⟨hk, ?_, ?_⟩
  · have hsq : x ^ 2 ≤ 4 * a ^ 2 := by nlinarith [hx.2]
    have hnum : (Real.log x) ^ 2 / (Real.log x + 1) ≤ Real.log x := by
      apply (div_le_iff₀ (by positivity : 0 < Real.log x + 1)).2
      nlinarith
    calc
      (k x)⁻¹ = x ^ 2 * ((Real.log x) ^ 2 / (Real.log x + 1)) := by
        unfold weight
        field_simp
      _ ≤ x ^ 2 * Real.log x := mul_le_mul_of_nonneg_left hnum (sq_nonneg x)
      _ ≤ (4 * a ^ 2) * (2 * Real.log a) :=
        mul_le_mul hsq hupper hl0.le (by positivity)
      _ = _ := by ring
  · have hnum : 2 * (Real.log x) ^ 2 + 3 * Real.log x + 2 ≤
        7 * Real.log x * (Real.log x + 1) := by nlinarith
    calc
      |kernelSlope x| / k x =
          (2 * (Real.log x) ^ 2 + 3 * Real.log x + 2) /
            (x * Real.log x * (Real.log x + 1)) := by
        rw [abs_of_nonpos (by
          dsimp only
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
            (by positivity) : kernelSlope x ≤ 0)]
        unfold weight
        field_simp [hx0.ne', hl0.ne', (by positivity : Real.log x + 1 ≠ 0)]
        <;> ring
      _ ≤ (7 * Real.log x * (Real.log x + 1)) /
          (x * Real.log x * (Real.log x + 1)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = 7 / x := by field_simp
      _ ≤ 7 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hx.1

private theorem width_exp {δ a : ℝ} (ha : 1 < a) :
    width δ a = Real.exp ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a)) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  simp only [width, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha0,
    Real.rpow_def_of_pos hL, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private theorem amplitude_exp {δ a : ℝ} (ha : 1 < a) :
    amplitude δ a = c * Real.exp ((2 * δ - 1) * Real.log (Real.log a) - Real.log a / 2) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  simp only [amplitude, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha0,
    Real.rpow_def_of_pos hL, div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  congr 1
  ring

private theorem amplitude_width_cancellation {δ a : ℝ} (ha : 1 < a) :
    amplitude δ a / (width δ a) ^ 2 = c * epsilon a / (a ^ 2 * Real.log a) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  rw [width_exp ha, amplitude_exp ha]
  have hexp : (Real.exp ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a))) ^ 2 =
      Real.exp (2 * ((3 / 4 : ℝ) * Real.log a +
      (Real.log a) ^ (1 / 4 : ℝ) / 2 + (δ - 1 / 2) * Real.log (Real.log a))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hcancel : epsilon a / (a ^ 2 * Real.log a) =
      Real.exp (-(Real.log a) ^ (1 / 4 : ℝ) - 2 * Real.log a) := by
    rw [epsilon, Real.exp_sub, show (2 : ℝ) * Real.log a = (2 : ℕ) * Real.log a by norm_num,
      Real.exp_nat_mul, Real.exp_log ha0]
    field_simp
  rw [mul_div_assoc c (epsilon a) (a ^ 2 * Real.log a), hcancel]
  simp only [div_eq_mul_inv, mul_assoc, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  congr 1
  ring

private theorem cell_derivatives {δ a x : ℝ} (hw : 0 < width δ a) :
    HasDerivAt (cellBump δ a) (cellSlope δ a x) x ∧
      HasDerivAt (cellSlope δ a) (cellSecond δ a x) x := by
  have hc := ((hasDerivAt_id x).sub_const a).div_const (width δ a)
  constructor
  · convert ((eta_derivatives ((x - a) / width δ a)).1.comp x hc).const_mul
      (-amplitude δ a) using 1 <;> first | rfl | (dsimp [cellBump]; ring)
  · convert ((eta_derivatives ((x - a) / width δ a)).2.comp x hc).const_mul
      (-(amplitude δ a / width δ a)) using 1 <;> first | rfl | (dsimp; field_simp <;> ring)

private theorem cell_estimates {δ a x : ℝ} (ha : 1 < a) (hLa : 1 ≤ Real.log a)
    (hw : 0 < width δ a) (hwa : width δ a ≤ a)
    (hx : x ∈ Icc a (a + width δ a)) :
    |cellSlope δ a x / k x| ≤ 4 * c * epsilon a * width δ a ∧
      |deriv (fun y : ℝ => y - cellSlope δ a y / k y) x - 1| ≤
        44 * c * epsilon a := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < Real.log a := by linarith
  have heps : 0 < epsilon a := by unfold epsilon; positivity
  have hα : 0 ≤ amplitude δ a := by unfold amplitude; positivity
  have hs : (x - a) / width δ a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hw.le
    · apply (div_le_iff₀ hw).2
      linarith [hx.2]
  have hη := eta_bounds hs
  have hk := kernel_cell_bounds ha hLa ⟨hx.1, by linarith [hx.2]⟩
  have hx1 : 1 < x := ha.trans_le hx.1
  have hcancel := amplitude_width_cancellation (δ := δ) ha
  have hfirst : |cellSlope δ a x| ≤ amplitude δ a / (2 * width δ a) := by
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg hα hw.le)]
    calc
      _ ≤ (amplitude δ a / width δ a) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hη.2.2.1 (div_nonneg hα hw.le)
      _ = _ := by ring
  have hsecond : |cellSecond δ a x| ≤ 2 * amplitude δ a / (width δ a) ^ 2 := by
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg hα (sq_nonneg _))]
    calc
      _ ≤ (amplitude δ a / (width δ a) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hη.2.2.2 (div_nonneg hα (sq_nonneg _))
      _ = _ := by ring
  have hbase : (amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a) =
      c * epsilon a := by
    rw [hcancel]
    field_simp
  have hvalue : |cellSlope δ a x / k x| ≤ 4 * c * epsilon a * width δ a := by
    calc
      |cellSlope δ a x / k x| = |cellSlope δ a x| * (k x)⁻¹ := by
        rw [abs_div, abs_of_pos hk.1, div_eq_mul_inv]
      _ ≤ (amplitude δ a / (2 * width δ a)) * (8 * a ^ 2 * Real.log a) :=
        mul_le_mul hfirst hk.2.1 (inv_nonneg.mpr hk.1.le) (by positivity)
      _ = 4 * ((amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a)) *
          width δ a := by field_simp; ring
      _ = _ := by rw [hbase]; ring
  refine ⟨hvalue, ?_⟩
  have hd := (hasDerivAt_id x).sub
    ((cell_derivatives hw).2.fun_div (kernel_hasDerivAt hx1) hk.1.ne')
  change HasDerivAt (fun y : ℝ => y - cellSlope δ a y / k y) _ x at hd
  rw [hd.deriv]
  have heq : 1 - (cellSecond δ a x * k x - cellSlope δ a x * kernelSlope x) /
      (k x) ^ 2 - 1 =
      -(cellSecond δ a x / k x) + (cellSlope δ a x / k x) * (kernelSlope x / k x) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |cellSecond δ a x / k x| +
        |cellSlope δ a x / k x| * |kernelSlope x / k x| := by
      simpa only [abs_neg, abs_mul] using abs_add_le
        (-(cellSecond δ a x / k x))
        ((cellSlope δ a x / k x) * (kernelSlope x / k x))
    _ ≤ 16 * c * epsilon a + (4 * c * epsilon a * width δ a) * (7 / a) := by
      apply add_le_add
      · calc
          |cellSecond δ a x / k x| = |cellSecond δ a x| * (k x)⁻¹ := by
            rw [abs_div, abs_of_pos hk.1, div_eq_mul_inv]
          _ ≤ (2 * amplitude δ a / (width δ a) ^ 2) * (8 * a ^ 2 * Real.log a) :=
            mul_le_mul hsecond hk.2.1 (inv_nonneg.mpr hk.1.le) (by positivity)
          _ = 16 * ((amplitude δ a / (width δ a) ^ 2) * (a ^ 2 * Real.log a)) := by
            ring
          _ = _ := by rw [hbase]; ring
      · apply mul_le_mul hvalue
          (by simpa only [abs_div, abs_of_pos hk.1] using hk.2.2)
          (abs_nonneg _) (by positivity)
    _ ≤ 44 * c * epsilon a := by
      have hwa' : width δ a / a ≤ 1 := (div_le_one ha0).2 hwa
      have heq' : (4 * c * epsilon a * width δ a) * (7 / a) =
          28 * c * epsilon a * (width δ a / a) := by ring
      rw [heq']
      nlinarith [mul_le_mul_of_nonneg_left hwa'
        (by positivity : 0 ≤ 28 * c * epsilon a)]

private theorem epsilon_hasDerivAt {a : ℝ} (ha : 1 < a) :
    HasDerivAt epsilon (Real.exp (-(Real.log a) ^ (1 / 4 : ℝ)) / a *
      (1 - (Real.log a) ^ (1 / 4 : ℝ) / 4)) a := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < Real.log a := Real.log_pos ha
  have hlog := Real.hasDerivAt_log ha0.ne'
  have hu := (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ))
    (Or.inl hL.ne')).comp a hlog
  have hp : Real.log a * (Real.log a) ^ ((1 / 4 : ℝ) - 1) =
      (Real.log a) ^ (1 / 4 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (Real.log a)]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  convert! hlog.mul (hu.neg.exp) using 1 <;> first
  | rfl
  | (dsimp [epsilon]; field_simp; nlinarith [hp])

private theorem epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := by
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    Real.tendsto_log_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 1
    (by norm_num)).comp hu
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
  have hL : 0 < Real.log a := Real.log_pos ha
  dsimp [epsilon]
  rw [← Real.rpow_mul hL.le]
  norm_num

private theorem width_eventually_bounds {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in atTop, 1 ≤ Real.log a ∧ 1 ≤ width δ a ∧ width δ a ≤ a := by
  have hu : Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ) / L) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [show -(3 / 4 : ℝ) = 1 / 4 - 1 by ring, Real.rpow_sub hL, Real.rpow_one]
  have hlog : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall : Tendsto (fun L : ℝ =>
      L ^ (1 / 4 : ℝ) / L / 2 + (δ - 1 / 2) * (Real.log L / L)) atTop (𝓝 0) := by
    simpa using (hu.div_const 2).add (hlog.const_mul (δ - 1 / 2))
  have hev := (hsmall.comp Real.tendsto_log_atTop).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hev, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with a hsmall hL ha
  have hL0 : 0 < Real.log a := by linarith
  have hlogL : 0 ≤ Real.log (Real.log a) := Real.log_nonneg hL
  have hlogL' : Real.log (Real.log a) ≤ Real.log a - 1 :=
    Real.log_le_sub_one_of_pos hL0
  have hu0 : 0 ≤ (Real.log a) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hL0.le _
  refine ⟨hL, ?_, ?_⟩
  · rw [width_exp ha, Real.one_le_exp_iff]
    nlinarith [mul_nonneg hδ.le hlogL]
  · rw [width_exp ha]
    apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log (by linarith : 0 < a))
    have heq : (Real.log a) ^ (1 / 4 : ℝ) / Real.log a / 2 +
        (δ - 1 / 2) * (Real.log (Real.log a) / Real.log a) =
        ((Real.log a) ^ (1 / 4 : ℝ) / 2 +
          (δ - 1 / 2) * Real.log (Real.log a)) / Real.log a := by ring
    dsimp only [Function.comp_def] at hsmall
    rw [heq] at hsmall
    have h := (div_lt_iff₀ hL0).1 hsmall
    linarith

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
    unfold weight
    exact (by positivity [Real.log_pos ((admissible_gt_one hA).trans_le hx)] :
      (Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2) ≠ 0)

private theorem epsilon_cell_comparison {a x : ℝ} (ha : 1 < a)
    (hLa : 1 ≤ Real.log a) (hx : x ∈ Icc a (2 * a)) : epsilon a ≤ 2 * epsilon x := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hlog := Real.log_le_log ha0 hx.1
  have hL0 : 0 < Real.log a := by linarith
  have hroot : (Real.log x) ^ (1 / 4 : ℝ) - (Real.log a) ^ (1 / 4 : ℝ) ≤
      Real.log x - Real.log a := by
    have hd : ∀ L ∈ Icc (Real.log a) (Real.log x),
        HasDerivWithinAt (fun z : ℝ => z ^ (1 / 4 : ℝ))
          ((1 / 4 : ℝ) * L ^ ((1 / 4 : ℝ) - 1)) (Icc (Real.log a) (Real.log x)) L := by
      intro L hL
      exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hL0.trans_le hL.1)))).hasDerivWithinAt
    have hb : ∀ L ∈ Ico (Real.log a) (Real.log x),
        ‖(1 / 4 : ℝ) * L ^ ((1 / 4 : ℝ) - 1)‖ ≤ 1 := by
      intro L hL
      have hL1 : 1 ≤ L := hLa.trans hL.1
      have hr := Real.rpow_le_one_of_one_le_of_nonpos hL1
        (by norm_num : (1 / 4 : ℝ) - 1 ≤ 0)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (Real.log x)
      (right_mem_Icc.2 hlog)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, one_mul] using hm)
  have hlogdiff : Real.log x - Real.log a ≤ Real.log (2 : ℝ) := by
    have h := Real.log_le_log hx0 hx.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at h
    linarith
  have hfactor : Real.exp ((Real.log x) ^ (1 / 4 : ℝ) -
      (Real.log a) ^ (1 / 4 : ℝ)) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log (2 : ℝ)) := Real.exp_le_exp.mpr (hroot.trans hlogdiff)
      _ = _ := Real.exp_log (by norm_num)
  calc
    epsilon a = Real.log a * Real.exp ((Real.log x) ^ (1 / 4 : ℝ) -
        (Real.log a) ^ (1 / 4 : ℝ)) * Real.exp (-(Real.log x) ^ (1 / 4 : ℝ)) := by
      simp only [epsilon, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.log x * 2 * Real.exp (-(Real.log x) ^ (1 / 4 : ℝ)) := by
      gcongr
    _ = 2 * epsilon x := by unfold epsilon; ring

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
  simpa only [Real.norm_eq_abs, heq] using h

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

end D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract
