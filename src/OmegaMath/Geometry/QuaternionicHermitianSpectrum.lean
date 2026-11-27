import OmegaBuild.Commands
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

The first three moments of a real spectrum with unit trace and unit second
moment bound the sum of its two largest entries. The estimate retains the
full range of simplex weights.
-/

open scoped BigOperators

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

/-- The cubic moment bound associated to a top-two sum and a tail of size `n`. -/
def topTwoCubic (n : ℕ) (x : ℝ) : ℝ :=
  3 * x / 2 - x ^ 3 / 2 - 3 * x * (1 - x) ^ 2 / (2 * n) + (1 - x) ^ 3 / (n : ℝ) ^ 2

/-- Simultaneous lower bounds on the repeated-index masses for a simplex with
at least four coordinates, including zero coordinates. -/
theorem simplex_moments {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hm : 4 ≤ Fintype.card ι) :
    let m : ℝ := Fintype.card ι
    1 / m ≤ (∑ i, w i ^ 2) ∧
      (3 * m - 2) / m ^ 2 ≤ ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
  classical
  let m : ℝ := Fintype.card ι
  have hm' : 4 ≤ m := by dsimp [m]; exact_mod_cast hm
  have hmp : 0 < m := by linarith
  have ha : 0 < 1 / m := one_div_pos.mpr hmp
  have ha' : 4 * (1 / m) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ hmp, one_mul]
    exact hm'
  have hw' (i : ι) : w i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
  rw [hs, one_pow, Finset.card_univ] at hcs
  refine ⟨(div_le_iff₀ hmp).mpr (by simpa [m, mul_comm] using hcs), ?_⟩
  let a : ℝ := 1 / m
  have ham : m * a = 1 := by dsimp [a]; field_simp
  have hterm (i : ι) : (3 * a ^ 2 - 2 * a ^ 3) +
        (6 * a - 6 * a ^ 2) * (w i - a) ≤ 3 * w i ^ 2 - 2 * w i ^ 3 := by
    have hcoef : 0 ≤ 3 - 4 * a - 2 * w i := by
      dsimp [a]
      linarith [hw' i]
    nlinarith only [mul_nonneg (sq_nonneg (w i - a)) hcoef]
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hs] at hlo
  change m * (3 * a ^ 2 - 2 * a ^ 3) +
    (6 * a - 6 * a ^ 2) * (1 - m * a) ≤ _ at hlo
  rw [ham, sub_self, mul_zero, add_zero] at hlo
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  convert hlo using 1
  dsimp [a]
  field_simp
  ring

/-- The difference between the top-two upper bound and the cubic moment is a sum
of squares times nonnegative factors. The tail may have repeated eigenvalues. -/
theorem topTwo_cubic_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ℝ) (u : ι → ℝ)
    (hab : b ≤ a) (hu : ∀ i, u i ≤ b)
    (h₁ : a + b + ∑ i, u i = 1) (h₂ : a ^ 2 + b ^ 2 + ∑ i, u i ^ 2 = 1) :
    a ^ 3 + b ^ 3 + ∑ i, u i ^ 3 ≤ topTwoCubic (Fintype.card ι) (a + b) := by
  classical
  let n : ℝ := Fintype.card ι
  let x := a + b
  let t := (1 - x) / n
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := ι)
  have hnt : n * t = 1 - x := by dsimp [t]; field_simp
  have hs : ∑ i, u i = n * t := by linarith only [h₁, hnt]
  have ht : t ≤ b := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hu i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [hs] at h
    exact (mul_le_mul_iff_right₀ hn).mp h
  have hsum : 0 ≤ ∑ i, (u i - t) ^ 2 * (3 * x / 2 - 2 * t - u i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (by dsimp [x]; linarith [hu i])
  have hexpand (y : ℝ) :
      (y - t) ^ 2 * (3 * x / 2 - 2 * t - y) =
        (3 * x / 2) * y ^ 2 - y ^ 3 +
          (3 * t ^ 2 - 3 * x * t) * y + (3 * x / 2 - 2 * t) * t ^ 2 := by ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs] at hsum
  have htail : ∑ i, u i ^ 2 = 1 - a ^ 2 - b ^ 2 := by linarith only [h₂]
  rw [htail] at hsum
  have hdiff :
      topTwoCubic (Fintype.card ι) x - (a ^ 3 + b ^ 3 + ∑ i, u i ^ 3) =
        (3 * x / 2) * (1 - a ^ 2 - b ^ 2) - (∑ i, u i ^ 3) +
          (3 * t ^ 2 - 3 * x * t) * (n * t) + n * ((3 * x / 2 - 2 * t) * t ^ 2) := by
    have hn' : (Fintype.card ι : ℝ) ≠ 0 := hn.ne'
    unfold topTwoCubic
    dsimp [t, n, x]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  nlinarith only [hsum]

/-- Five eigenvalues with the trace, norm and holonomy lower bounds cannot
have a top-two sum at least twice the orthogonal Rayleigh lower bound. -/
theorem five_point_moment_obstruction (a b : ℝ) (u : Fin 3 → ℝ) {c : ℝ}
    (hc : 9 / 16 < c) (hab : b ≤ a) (hu : ∀ i, u i ≤ b)
    (h₁ : a + b + ∑ i, u i = 1) (h₂ : a ^ 2 + b ^ 2 + ∑ i, u i ^ 2 = 1)
    (h₃ : (13 + 12 * c) / 25 ≤ a ^ 3 + b ^ 3 + ∑ i, u i ^ 3) :
    a + b < (2 + 8 * c) / 5 := by
  by_contra! h
  have hm := topTwo_cubic_bound a b u hab hu h₁ h₂
  rw [Fintype.card_fin] at hm
  let y := (2 + 8 * c) / 5
  let x := a + b
  have hy : 0 ≤ y - 1 := by dsimp [y]; linarith
  have hx : y - 1 ≤ x - 1 := by dsimp [x, y]; linarith
  have hf (z : ℝ) : topTwoCubic 3 z = 1 - 2 * (z - 1) ^ 2 - 10 / 9 * (z - 1) ^ 3 := by
    unfold topTwoCubic
    norm_num
    ring
  have hmon : topTwoCubic 3 x ≤ topTwoCubic 3 y := by
    rw [hf, hf]
    linarith [pow_le_pow_left₀ hy hx 2, pow_le_pow_left₀ hy hx 3]
  have hgap : 0 < (13 + 12 * c) / 25 - topTwoCubic 3 y := by
    rw [show (13 + 12 * c) / 25 - topTwoCubic 3 y =
      4 * c * (16 * c - 9) * (16 * c + 9) / 225 by rw [hf]; dsimp [y]; ring]
    have hc₀ : 0 < c := by linarith
    have hc₁ : 0 < 16 * c - 9 := by linarith
    have hc₂ : 0 < 16 * c + 9 := by linarith
    positivity
  change _ ≤ topTwoCubic 3 x at hm
  linarith only [h₃, hm, hmon, hgap]

end Omega.Geometry.HolonomySpectrum
