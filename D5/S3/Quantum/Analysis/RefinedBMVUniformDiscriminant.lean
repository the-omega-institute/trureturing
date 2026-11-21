/- GID: D5/S3/Quantum/Analysis/RefinedBMVUniformDiscriminant
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit polynomial for the scalar discriminant at every exponent. -/

import D5.S3.Quantum.Analysis.RefinedBMVUniformCorner
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Closed multiplication identities for the homogeneous sum on three variables. -/

open scoped BigOperators

noncomputable section

namespace RefinedBMV.DividedDifference

variable {R : Type*} [CommRing R]

def homogeneousTwo (p : ℕ) (x y : R) : R :=
  ∑ j ∈ Finset.range (p + 1), x ^ j * y ^ (p - j)

def homogeneousThree (p : ℕ) (a x y : R) : R :=
  ∑ i ∈ Finset.range (p + 1), a ^ i * homogeneousTwo (p - i) x y

private theorem homogeneousTwo_clear (p : ℕ) (x y : R) :
    (y - x) * homogeneousTwo p x y = y ^ (p + 1) - x ^ (p + 1) := by
  have h := geom_sum₂_mul x y (p + 1)
  change homogeneousTwo p x y * (x - y) = _ at h
  linear_combination -h

private theorem homogeneousTwo_diag (p : ℕ) (x : R) :
    homogeneousTwo p x x = (p + 1 : R) * x ^ p := by
  unfold homogeneousTwo
  calc
    _ = ∑ j ∈ Finset.range (p + 1), x ^ p := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    _ = _ := by simp

private theorem homogeneousThree_succ (p : ℕ) (a x y : R) :
    homogeneousThree (p + 1) a x y =
      a * homogeneousThree p a x y + homogeneousTwo (p + 1) x y := by
  unfold homogeneousThree
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Finset.mul_sum]
  apply congrArg (fun z : R => z + homogeneousTwo (p + 1) x y)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_add_right, pow_succ']
  ring

/-- The numerator of the second divided difference at three nodes. -/
theorem clear_distinct (p : ℕ) (a x y : R) :
    ((x - a) * (y - a) * (y - x)) * homogeneousThree p a x y =
      (y - x) * a ^ (p + 2) - (y - a) * x ^ (p + 2) + (x - a) * y ^ (p + 2) := by
  induction p with
  | zero => simp [homogeneousThree, homogeneousTwo]; ring
  | succ p ih =>
    calc
      _ = a * (((x - a) * (y - a) * (y - x)) * homogeneousThree p a x y) +
          (x - a) * (y - a) * ((y - x) * homogeneousTwo (p + 1) x y) := by
        rw [homogeneousThree_succ]
        ring
      _ = _ := by rw [ih, homogeneousTwo_clear]; simp only [pow_succ' _ (p + 2)]; ring

/-- The numerator when the lower two nodes in the expression coincide. -/
theorem clear_repeat_first (p : ℕ) (a y : R) :
    (y - a) ^ 2 * homogeneousThree p a a y =
      y ^ (p + 2) - (p + 2 : R) * a ^ (p + 1) * y + (p + 1 : R) * a ^ (p + 2) := by
  induction p with
  | zero => simp [homogeneousThree, homogeneousTwo]; ring
  | succ p ih =>
    calc
      _ = a * ((y - a) ^ 2 * homogeneousThree p a a y) +
          (y - a) * ((y - a) * homogeneousTwo (p + 1) a y) := by
        rw [homogeneousThree_succ]
        ring
      _ = _ := by
        rw [ih, homogeneousTwo_clear]
        push_cast
        simp only [pow_succ' _ (p + 2), pow_succ' a (p + 1)]
        ring

/-- The numerator when the last two nodes coincide. -/
theorem clear_repeat_last (p : ℕ) (a y : R) :
    (y - a) ^ 2 * homogeneousThree p a y y =
      a ^ (p + 2) - (p + 2 : R) * y ^ (p + 1) * a + (p + 1 : R) * y ^ (p + 2) := by
  induction p with
  | zero => simp [homogeneousThree, homogeneousTwo]; ring
  | succ p ih =>
    calc
      _ = a * ((y - a) ^ 2 * homogeneousThree p a y y) +
          (y - a) ^ 2 * homogeneousTwo (p + 1) y y := by
        rw [homogeneousThree_succ]
        ring
      _ = _ := by
        rw [ih, homogeneousTwo_diag]
        push_cast
        simp only [pow_succ' _ (p + 2), pow_succ' y (p + 1)]
        ring

section Defect

open DimThree (defect gaps gaps_length_eq_choose)

private theorem sum_range_list {S : Type*} [AddCommMonoid S] (n : ℕ) (f : ℕ → S) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

private theorem sum_flatten {S : Type*} [AddMonoid S] (l : List ℕ) (f : ℕ → List S) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The homogeneous sum is the sum over three gaps before subtracting the correction. -/
theorem defect_eq_homogeneous (p : ℕ) (a x y : R) :
    defect p a x y = homogeneousThree p (a ^ 3) (x ^ 3) (y ^ 3) -
      ((p + 2).choose 2 : R) * (a * x * y) ^ p := by
  rw [defect, gaps_length_eq_choose, gaps, List.map_flatMap, sum_flatten, sum_range_list]
  congr 1
  unfold homogeneousThree homogeneousTwo
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have h : p + 1 - i = p - i + 1 := by omega
  simp only [List.map_map, Function.comp_apply, h, sum_range_list, Finset.mul_sum, mul_assoc]

private theorem twice_choose (p : ℕ) :
    2 * ((p + 2).choose 2 : ℝ) = (p + 1 : ℝ) * (p + 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- The discriminant before the normalization at the smallest root. -/
def quartic (p : ℕ) (a x y : ℝ) : ℝ :=
  let q := defect p a a y * defect p x x y
  let w := defect p a x x * defect p a y y
  4 * q * w - (defect p a x y ^ 2 - q - w) ^ 2

def denominator (X Y : ℝ) : ℝ := (X - 1) * (Y - 1) * (Y - X)

/-- Denominator-cleared discriminant with the two p-th powers kept as variables. -/
def clearedQuartic {S : Type*} [CommRing S] (p X Y U V : S) : S :=
  let n := (p + 1) * (p + 2)
  let d := 2 * ((Y - X) - (Y - 1) * X^2 * U^3 + (X - 1) * Y^2 * V^3) -
    n * U * V * ((X - 1) * (Y - 1) * (Y - X))
  let f := 2 * (Y^2 * V^3 - (p + 2) * Y + p + 1) - n * V * (Y - 1)^2
  let g := 2 * (Y^2 * V^3 - (p + 2) * X * Y * U^3 + (p + 1) * X^2 * U^3) -
    n * U^2 * V * (Y - X)^2
  let r := 2 * (1 - (p + 2) * X * U^3 + (p + 1) * X^2 * U^3) -
    n * U^2 * (X - 1)^2
  let h := 2 * (1 - (p + 2) * Y * V^3 + (p + 1) * Y^2 * V^3) -
    n * V^2 * (Y - 1)^2
  let q := f * g * (X - 1)^2
  let w := r * h * (Y - X)^2
  4 * q * w - (d^2 - q - w)^2

private theorem power_cube (x : ℝ) (p : ℕ) :
    (x ^ 3) ^ p = (x ^ p) ^ 3 := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The polynomial certificate has the exact quartic sign on strictly ordered roots. -/
theorem clearedQuartic_eq (p : ℕ) (x y : ℝ) :
    clearedQuartic (p : ℝ) (x^3) (y^3) (x^p) (y^p) =
      16 * denominator (x^3) (y^3)^4 * quartic p 1 x y := by
  let X := x^3
  let Y := y^3
  let U := x^p
  let V := y^p
  let J := denominator X Y
  let n := (p + 1 : ℝ) * (p + 2 : ℝ)
  have hn := twice_choose p
  have px (z : ℝ) : (z^3)^(p+2) = (z^3)^2 * (z^p)^3 := by
    rw [pow_add, power_cube, mul_comm]
  have px' (z : ℝ) : (z^3)^(p+1) = (z^3) * (z^p)^3 := by
    rw [pow_succ', power_cube]
  have hd : 2 * J * defect p 1 x y =
      2 * ((Y - X) - (Y - 1) * X^2 * U^3 + (X - 1) * Y^2 * V^3) -
      n * U * V * J := by
    have h := clear_distinct p (1 : ℝ) X Y
    simp only [one_pow] at h
    rw [defect_eq_homogeneous]
    simp only [one_pow, one_mul, mul_pow]
    dsimp only [J, denominator, X, Y] at h ⊢
    rw [px, px] at h
    dsimp only [n, U, V]
    linear_combination 2 * h - ((x^3-1)*(y^3-1)*(y^3-x^3)*x^p*y^p) * hn
  have hf : 2 * (Y - 1)^2 * defect p 1 1 y =
      2 * (Y^2 * V^3 - (p + 2) * Y + p + 1) - n * V * (Y - 1)^2 := by
    have h := clear_repeat_first p (1 : ℝ) Y
    simp only [one_pow, mul_one] at h
    rw [defect_eq_homogeneous]
    simp only [one_pow, one_mul]
    dsimp only [Y] at h ⊢
    rw [px] at h
    dsimp only [n, V]
    linear_combination 2 * h - ((y^3-1)^2*y^p) * hn
  have hg : 2 * (Y - X)^2 * defect p x x y =
      2 * (Y^2 * V^3 - (p + 2) * X * Y * U^3 + (p + 1) * X^2 * U^3) -
        n * U^2 * V * (Y - X)^2 := by
    have h := clear_repeat_first p X Y
    rw [defect_eq_homogeneous]
    simp only [mul_pow]
    dsimp only [X, Y] at h ⊢
    rw [px, px, px'] at h
    dsimp only [n, U, V]
    linear_combination 2 * h - ((y^3-x^3)^2*(x^p)^2*y^p) * hn
  have hr (z : ℝ) : 2 * (z^3 - 1)^2 * defect p 1 z z =
      2 * (1 - (p + 2) * (z^3) * (z^p)^3 + (p + 1) * (z^3)^2 * (z^p)^3) -
        n * (z^p)^2 * (z^3 - 1)^2 := by
    have h := clear_repeat_last p (1 : ℝ) (z^3)
    simp only [one_pow, mul_one] at h
    rw [px, px'] at h
    rw [defect_eq_homogeneous]
    simp only [one_pow, one_mul, mul_pow]
    dsimp only [n]
    linear_combination 2 * h - ((z^3-1)^2*(z^p)^2) * hn
  change clearedQuartic (p : ℝ) X Y U V = 16 * J^4 * quartic p 1 x y
  unfold clearedQuartic quartic
  dsimp only
  dsimp only [X, Y, U, V, n, J, denominator] at hd hf hg hr ⊢
  rw [← hd, ← hf, ← hg, ← hr x, ← hr y]
  ring

end Defect

end RefinedBMV.DividedDifference
