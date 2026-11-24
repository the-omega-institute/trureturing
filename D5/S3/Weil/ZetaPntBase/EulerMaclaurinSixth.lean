/- GID: D5/S3/Weil/ZetaPntBase/EulerMaclaurinSixth
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Signed sixth-derivative Euler–Maclaurin remainder on a uniform mesh. -/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A signed Euler–Maclaurin remainder on a uniform mesh

The kernel is the one-cell Bernoulli remainder from the Euler–Maclaurin
formula (DLMF 2.10.1). The one-cell proof uses an explicit antiderivative.
Adding the cells telescopes the endpoint corrections on the mesh.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth

/-- The sixth-derivative remainder kernel at offset `x` in a cell of width `h`. -/
noncomputable def kernel (h x : ℝ) : ℝ :=
  (x * (h - x)) ^ 2 * (h ^ 2 + 2 * (x * (h - x))) / 1440

/-- The signed kernel is nonnegative on the cell and is bounded by its midpoint value. -/
theorem kernel_bounds {h x : ℝ} (hx : 0 ≤ x) (hxh : x ≤ h) :
    0 ≤ kernel h x ∧ kernel h x ≤ h ^ 6 / 15360 := by
  let q : ℝ := x * (h - x)
  have hq0 : 0 ≤ q := mul_nonneg hx (sub_nonneg.mpr hxh)
  have hq : q ≤ h ^ 2 / 4 := by
    calc
      q ≤ q + (h - 2 * x) ^ 2 / 4 :=
        le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))
      _ = h ^ 2 / 4 := by
        dsimp [q]
        ring
  have hq2 : q ^ 2 ≤ (h ^ 2 / 4) ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul hq hq hq0 (div_nonneg (sq_nonneg h) (by norm_num)))
  have hfactor : 0 ≤ h ^ 2 + 2 * q :=
    add_nonneg (sq_nonneg h) (mul_nonneg (by norm_num) hq0)
  have hfactor_le : h ^ 2 + 2 * q ≤ h ^ 2 + 2 * (h ^ 2 / 4) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hq (by norm_num))
  change 0 ≤ q ^ 2 * (h ^ 2 + 2 * q) / 1440 ∧
    q ^ 2 * (h ^ 2 + 2 * q) / 1440 ≤ h ^ 6 / 15360
  refine ⟨div_nonneg (mul_nonneg (sq_nonneg q) hfactor) (by norm_num), ?_⟩
  calc
    _ ≤ (h ^ 2 / 4) ^ 2 * (h ^ 2 + 2 * (h ^ 2 / 4)) / 1440 :=
      div_le_div_of_nonneg_right (mul_le_mul hq2 hfactor_le hfactor (sq_nonneg _))
        (by norm_num)
    _ = _ := by ring

/-- The trapezoid minus the integral and its two endpoint corrections equals the
integral of the signed kernel against the sixth derivative. Here `f0, …, f6` are
successive derivatives on the cell. -/
theorem trapezoid_sub_integral_eq {a h : ℝ} {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (h0 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f0 (f1 x) x)
    (h1 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f3 (f4 x) x)
    (h4 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f4 (f5 x) x)
    (h5 : ∀ x ∈ Set.uIcc a (a + h), HasDerivAt f5 (f6 x) x)
    (h6 : ContinuousOn f6 (Set.uIcc a (a + h))) :
    h / 2 * (f0 a + f0 (a + h)) - (∫ x in a..(a + h), f0 x) -
        h ^ 2 / 12 * (f1 (a + h) - f1 a) + h ^ 4 / 720 * (f3 (a + h) - f3 a) =
      ∫ x in a..(a + h), kernel h (x - a) * f6 x := by
  let q (x : ℝ) : ℝ := (x - a) * (h - (x - a))
  let r (x : ℝ) : ℝ := h - 2 * (x - a)
  let k0 (x : ℝ) : ℝ := kernel h (x - a)
  let k1 (x : ℝ) : ℝ := q x * r x * (h ^ 2 + 3 * q x) / 720
  let k2 (x : ℝ) : ℝ := (h ^ 4 - 30 * (q x) ^ 2) / 720
  let k3 (x : ℝ) : ℝ := -(q x * r x) / 12
  let k4 (x : ℝ) : ℝ := (6 * q x - h ^ 2) / 12
  let k5 (x : ℝ) : ℝ := r x / 2
  have hq (x : ℝ) : HasDerivAt q (r x) x := by
    have hs := (hasDerivAt_id' x).sub_const a
    refine (hs.fun_mul (hs.const_sub h)).congr_deriv ?_
    dsimp [r] <;> ring
  have hr (x : ℝ) : HasDerivAt r (-2) x := by
    have hs := (hasDerivAt_id' x).sub_const a
    refine ((hs.const_mul 2).const_sub h).congr_deriv ?_
    norm_num
  have hk0 (x : ℝ) : HasDerivAt k0 (k1 x) x := by
    have dq := hq x
    have hd := ((dq.fun_pow 2).fun_mul ((dq.const_mul 2).const_add (h ^ 2))).div_const 1440
    refine hd.congr_deriv ?_
    simp only [k1, Nat.reduceSub, pow_one] <;> ring
  have hk1 (x : ℝ) : HasDerivAt k1 (k2 x) x := by
    have dq := hq x
    have hd := ((dq.fun_mul (hr x)).fun_mul
      ((dq.const_mul 3).const_add (h ^ 2))).div_const 720
    refine hd.congr_deriv ?_
    dsimp [k2, q, r] <;> ring
  have hk2 (x : ℝ) : HasDerivAt k2 (k3 x) x := by
    have hd := ((((hq x).fun_pow 2).const_mul 30).const_sub (h ^ 4)).div_const 720
    refine hd.congr_deriv ?_
    simp only [k3, Nat.reduceSub, pow_one] <;> ring
  have hk3 (x : ℝ) : HasDerivAt k3 (k4 x) x := by
    have hd := (((hq x).fun_mul (hr x)).neg).div_const 12
    refine hd.congr_deriv ?_
    dsimp [k4, q, r] <;> ring
  have hk4 (x : ℝ) : HasDerivAt k4 (k5 x) x := by
    have hd := (((hq x).const_mul 6).sub_const (h ^ 2)).div_const 12
    refine hd.congr_deriv ?_
    dsimp [k5] <;> ring
  have hk5 (x : ℝ) : HasDerivAt k5 (-1) x :=
    ((hr x).div_const 2).congr_deriv (by norm_num)
  -- Differentiation cancels five pairs of mixed terms.
  let G (x : ℝ) : ℝ :=
    k0 x * f5 x - k1 x * f4 x + k2 x * f3 x -
      k3 x * f2 x + k4 x * f1 x - k5 x * f0 x
  have hG (x : ℝ) (hx : x ∈ Set.uIcc a (a + h)) :
      HasDerivAt G (f0 x + kernel h (x - a) * f6 x) x := by
    have hd01 := ((hk0 x).fun_mul (h5 x hx)).fun_sub ((hk1 x).fun_mul (h4 x hx))
    have hd23 := (hd01.fun_add ((hk2 x).fun_mul (h3 x hx))).fun_sub
      ((hk3 x).fun_mul (h2 x hx))
    have hd := (hd23.fun_add ((hk4 x).fun_mul (h1 x hx))).fun_sub
      ((hk5 x).fun_mul (h0 x hx))
    change HasDerivAt G (f0 x + k0 x * f6 x) x
    exact hd.congr_deriv (by ring)
  have hleft : G a = -(h / 2) * f0 a - h ^ 2 / 12 * f1 a + h ^ 4 / 720 * f3 a := by
    simp only [G, k0, k1, k2, k3, k4, k5, q, r, kernel, sub_self] <;> ring
  have hright : G (a + h) =
      h / 2 * f0 (a + h) - h ^ 2 / 12 * f1 (a + h) + h ^ 4 / 720 * f3 (a + h) := by
    have hshift : a + h - a = h := by ring
    simp only [G, k0, k1, k2, k3, k4, k5, q, r, kernel, hshift, sub_self] <;> ring
  have hkContinuous : ContinuousOn k0 (Set.uIcc a (a + h)) :=
    HasDerivAt.continuousOn (fun x _ => hk0 x)
  have hi0 : IntervalIntegrable f0 volume a (a + h) :=
    (HasDerivAt.continuousOn h0).intervalIntegrable
  have hi6 : IntervalIntegrable (fun x => kernel h (x - a) * f6 x) volume a (a + h) :=
    (hkContinuous.mul h6).intervalIntegrable
  have hFTC : (∫ x in a..(a + h), f0 x + kernel h (x - a) * f6 x) = G (a + h) - G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hi0.add hi6)
  rw [intervalIntegral.integral_add hi0 hi6] at hFTC
  calc
    _ = G (a + h) - G a - (∫ x in a..(a + h), f0 x) := by
      rw [hleft, hright]
      ring
    _ = _ := by
      rw [← hFTC]
      ring

/-- The sum of the signed sixth-derivative remainders on the consecutive mesh cells. -/
noncomputable def meshRemainder (a h : ℝ) (n : ℕ) (f6 : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∫ x in (a + (i : ℝ) * h)..(a + ((i + 1 : ℕ) : ℝ) * h),
      kernel h (x - (a + (i : ℝ) * h)) * f6 x

private theorem mesh_node_succ (a h : ℝ) (i : ℕ) :
    a + ((i + 1 : ℕ) : ℝ) * h = a + (i : ℝ) * h + h := by
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The closed uniform mesh sum is the integral with endpoint corrections
plus the signed sixth-derivative remainder. There are `n` cells and `n + 1` nodes. -/
theorem mesh_sum_eq {a h : ℝ} {n : ℕ} {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (h0 : ∀ x, HasDerivAt f0 (f1 x) x)
    (h1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x, HasDerivAt f3 (f4 x) x)
    (h4 : ∀ x, HasDerivAt f4 (f5 x) x)
    (h5 : ∀ x, HasDerivAt f5 (f6 x) x)
    (h6 : Continuous f6) :
    h * (∑ i ∈ Finset.range (n + 1), f0 (a + (i : ℝ) * h)) =
      (∫ x in a..(a + (n : ℝ) * h), f0 x) +
        h / 2 * (f0 a + f0 (a + (n : ℝ) * h)) +
        h ^ 2 / 12 * (f1 (a + (n : ℝ) * h) - f1 a) -
        h ^ 4 / 720 * (f3 (a + (n : ℝ) * h) - f3 a) + meshRemainder a h n f6 := by
  let node (i : ℕ) : ℝ := a + (i : ℝ) * h
  let cell (i : ℕ) : ℝ :=
    ∫ x in (node i)..(node (i + 1)), kernel h (x - node i) * f6 x
  have hzero : node 0 = a := by simp [node]
  have hcell (i : ℕ) :
      h / 2 * (f0 (node i) + f0 (node (i + 1))) -
          (∫ x in (node i)..(node (i + 1)), f0 x) -
          h ^ 2 / 12 * (f1 (node (i + 1)) - f1 (node i)) +
          h ^ 4 / 720 * (f3 (node (i + 1)) - f3 (node i)) = cell i := by
    have hstep : node (i + 1) = node i + h := mesh_node_succ a h i
    dsimp only [cell]
    rw [hstep]
    exact trapezoid_sub_integral_eq
      (fun x _ => h0 x) (fun x _ => h1 x) (fun x _ => h2 x)
      (fun x _ => h3 x) (fun x _ => h4 x) (fun x _ => h5 x) h6.continuousOn
  have hcont : Continuous f0 := continuous_iff_continuousAt.mpr fun x => (h0 x).continuousAt
  unfold meshRemainder
  change h * (∑ i ∈ Finset.range (n + 1), f0 (node i)) =
    (∫ x in a..(node n), f0 x) + h / 2 * (f0 a + f0 (node n)) +
      h ^ 2 / 12 * (f1 (node n) - f1 a) - h ^ 4 / 720 * (f3 (node n) - f3 a) +
      ∑ i ∈ Finset.range n, cell i
  induction n with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, hzero,
      intervalIntegral.integral_same, sub_self]
    ring
  | succ n ih =>
    have hsplit :
        (∫ x in a..(node n), f0 x) + (∫ x in (node n)..(node (n + 1)), f0 x) =
          ∫ x in a..(node (n + 1)), f0 x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable a (node n)) (hcont.intervalIntegrable (node n) (node (n + 1)))
    rw [Finset.sum_range_succ (fun i => f0 (node i)) (n + 1), Finset.sum_range_succ cell n,
      mul_add, ih, ← hsplit, ← hcell n]
    ring

/-- On a mesh of nonnegative width, a nonnegative sixth derivative gives a
nonnegative remainder. -/
theorem meshRemainder_nonneg {a h : ℝ} {n : ℕ} {f6 : ℝ → ℝ}
    (hh : 0 ≤ h) (hf : ∀ x ∈ Set.Icc a (a + (n : ℝ) * h), 0 ≤ f6 x) :
    0 ≤ meshRemainder a h n f6 := by
  let node (i : ℕ) : ℝ := a + (i : ℝ) * h
  have hmono : Monotone node := by
    intro i j hij
    simpa only [node, add_comm a] using
      add_le_add_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh) a
  unfold meshRemainder
  change 0 ≤ ∑ i ∈ Finset.range n,
    ∫ x in (node i)..(node (i + 1)), kernel h (x - node i) * f6 x
  refine Finset.sum_nonneg fun i hi =>
    intervalIntegral.integral_nonneg (hmono (Nat.le_succ i)) (fun x hx => ?_)
  have hright : x ≤ node i + h := hx.2.trans_eq (mesh_node_succ a h i)
  have hleft : a ≤ node i := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh)
  have hi' : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  exact mul_nonneg (kernel_bounds (sub_nonneg.mpr hx.1) (sub_le_iff_le_add'.mpr hright)).1
    (hf x ⟨hleft.trans hx.1, hx.2.trans (hmono hi')⟩)

/-- The absolute remainder is bounded by the maximum cell kernel times the
integral of the absolute sixth derivative over the whole mesh. -/
theorem abs_meshRemainder_le {a h : ℝ} {n : ℕ} {f6 : ℝ → ℝ}
    (hh : 0 ≤ h) (hf : Continuous f6) :
    |meshRemainder a h n f6| ≤
      h ^ 6 / 15360 * (∫ x in a..(a + (n : ℝ) * h), |f6 x|) := by
  let node (i : ℕ) : ℝ := a + (i : ℝ) * h
  let integrand (i : ℕ) (x : ℝ) : ℝ := kernel h (x - node i) * f6 x
  let cell (i : ℕ) : ℝ := ∫ x in (node i)..(node (i + 1)), integrand i x
  have hcell (i : ℕ) :
      |cell i| ≤ h ^ 6 / 15360 * (∫ x in (node i)..(node (i + 1)), |f6 x|) := by
    have hstep : node (i + 1) = node i + h := mesh_node_succ a h i
    have hab : node i ≤ node (i + 1) := by
      rw [hstep]
      exact le_add_of_nonneg_right hh
    have hk : Continuous (fun x : ℝ => kernel h (x - node i)) := by
      let q (x : ℝ) : ℝ := (x - node i) * (h - (x - node i))
      have hs : Continuous (fun x : ℝ => x - node i) := continuous_id.sub continuous_const
      have hq : Continuous q := hs.mul (continuous_const.sub hs)
      change Continuous (fun x => q x ^ 2 * (h ^ 2 + 2 * q x) / 1440)
      exact ((hq.pow 2).mul (continuous_const.add (continuous_const.mul hq))).div_const _
    have hintegrand : Continuous (integrand i) := hk.mul hf
    have hmajorant : Continuous (fun x => (h ^ 6 / 15360) * |f6 x|) :=
      continuous_const.mul hf.abs
    calc
      |cell i| ≤ ∫ x in (node i)..(node (i + 1)), |integrand i x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in (node i)..(node (i + 1)), (h ^ 6 / 15360) * |f6 x| := by
        refine intervalIntegral.integral_mono_on hab (hintegrand.abs.intervalIntegrable _ _)
          (hmajorant.intervalIntegrable _ _) ?_
        intro x hx
        have hright : x ≤ node i + h := hx.2.trans_eq hstep
        have hbounds := kernel_bounds (sub_nonneg.mpr hx.1) (sub_le_iff_le_add'.mpr hright)
        change |kernel h (x - node i) * f6 x| ≤ (h ^ 6 / 15360) * |f6 x|
        rw [abs_mul, abs_of_nonneg hbounds.1]
        exact mul_le_mul_of_nonneg_right hbounds.2 (abs_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hzero : node 0 = a := by simp [node]
  have hintegral :
      (∑ i ∈ Finset.range n, ∫ x in (node i)..(node (i + 1)), |f6 x|) =
        ∫ x in a..(node n), |f6 x| := by
    simpa only [hzero] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := node) (n := n)
        (μ := volume) (f := fun x => |f6 x|)
        (fun i _ => hf.abs.intervalIntegrable (node i) (node (i + 1))))
  unfold meshRemainder
  change |∑ i ∈ Finset.range n, cell i| ≤ h ^ 6 / 15360 * (∫ x in a..(node n), |f6 x|)
  calc
    _ ≤ ∑ i ∈ Finset.range n, |cell i| := Finset.abs_sum_le_sum_abs cell _
    _ ≤ ∑ i ∈ Finset.range n, (h ^ 6 / 15360) * (∫ x in (node i)..(node (i + 1)), |f6 x|) :=
      Finset.sum_le_sum (fun i _ => hcell i)
    _ = _ := by rw [← Finset.mul_sum, hintegral]

end D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
