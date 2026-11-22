/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Box
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational exponential and radical enclosures for zero-centered profile certificates. -/

import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Floor

/-! Analytic input bounds for the rational arithmetic expression checker. -/

open Finset

namespace RefinedBMV.FourSpectrumLift

open D5.S0.Certificates.BoxCover.RationalIntervalExpression

private def expTaylorBounds (r : ℚ) (n : ℕ) : ℚ × ℚ :=
  let s := ∑ j ∈ range n, r ^ j / j.factorial
  let e := |r| ^ n * ((n + 1 : ℚ) / ((n.factorial : ℚ) * n))
  (max 0 (s-e), s+e)

private def expReductionBounds (x : ℚ) (m n : ℕ) : ℚ × ℚ :=
  let p := expTaylorBounds (x / m) n
  (p.1 ^ m, p.2 ^ m)

private theorem expReductionBounds_sound (x : ℚ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hx : |x / (m : ℚ)| ≤ 1) :
    ((expReductionBounds x m n).1 : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ ((expReductionBounds x m n).2 : ℝ) := by
  let r : ℝ := (x : ℝ) / m
  let s := ∑ j ∈ range n, r ^ j / (j.factorial : ℝ)
  let e := |r| ^ n * ((n + 1 : ℝ) / ((n.factorial : ℝ) * n))
  have hr : |r| ≤ 1 := by dsimp [r]; exact_mod_cast hx
  have ht : |Real.exp r - s| ≤ e := by
    simpa [s, e] using Real.exp_bound hr hn
  have hlo : max 0 (s-e) ≤ Real.exp r := by
    apply max_le (Real.exp_pos _).le
    linarith [(abs_le.mp ht).1]
  have hhi : Real.exp r ≤ s+e := by linarith [(abs_le.mp ht).2]
  have heq : Real.exp r ^ m = Real.exp (x : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [r]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [← heq]
  simp only [expReductionBounds, expTaylorBounds]
  push_cast
  exact ⟨pow_le_pow_left₀ (le_max_left _ _) hlo m,
    pow_le_pow_left₀ (Real.exp_pos _).le hhi m⟩

/-- The exact rational enclosure of the exponential of an interval, obtained from
two Taylor evaluations with range reduction. -/
def expBoxBounds (lo hi : ℚ) (m n : ℕ) : ℚ × ℚ :=
  ((expReductionBounds lo m n).1, (expReductionBounds hi m n).2)

private def roundDownAt (p : ℕ) (q : ℚ) : ℚ := (⌊q * 2^p⌋ : ℤ) / (2^p : ℚ)

private def roundUpAt (p : ℕ) (q : ℚ) : ℚ := -roundDownAt p (-q)

private theorem roundDownAt_le (p : ℕ) (q : ℚ) : roundDownAt p q ≤ q := by
  unfold roundDownAt
  exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

private theorem le_roundUpAt (p : ℕ) (q : ℚ) : q ≤ roundUpAt p q := by
  simpa only [roundUpAt, neg_neg] using neg_le_neg (roundDownAt_le p (-q))

private theorem roundDownAt_nonneg (p : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ roundDownAt p q := by
  have h : 0 ≤ ⌊q * (2 : ℚ)^p⌋ := Int.floor_nonneg.mpr (mul_nonneg hq (by positivity))
  unfold roundDownAt
  exact div_nonneg (by exact_mod_cast h) (by positivity)

/-- Directed rounding on a dyadic grid keeps intermediate rationals small. -/
def roundDown (q : ℚ) : ℚ := roundDownAt 128 q

def roundUp (q : ℚ) : ℚ := -roundDown (-q)

theorem roundDown_le (q : ℚ) : roundDown q ≤ q := roundDownAt_le 128 q

theorem le_roundUp (q : ℚ) : q ≤ roundUp q := le_roundUpAt 128 q

private def roundedSquares (round : ℚ → ℚ) (q : ℚ) : ℕ → ℚ
  | 0 => round q
  | k + 1 => round ((roundedSquares round q k)^2)

private theorem roundedSquares_encloses (l u : ℚ) (hl : 0 ≤ l) (hu : 0 ≤ u) (k : ℕ) :
    0 ≤ roundedSquares (roundDownAt 384) l k ∧
      roundedSquares (roundDownAt 384) l k ≤ l ^ (2^k : ℕ) ∧
      u ^ (2^k : ℕ) ≤ roundedSquares (roundUpAt 384) u k := by
  induction k with
  | zero =>
    simp only [roundedSquares, pow_zero, pow_one]
    exact ⟨roundDownAt_nonneg 384 hl, roundDownAt_le 384 l, le_roundUpAt 384 u⟩
  | succ k ih =>
    simp only [roundedSquares, pow_succ (2 : ℕ) k, pow_mul]
    exact ⟨roundDownAt_nonneg 384 (sq_nonneg _),
      (roundDownAt_le 384 _).trans (pow_le_pow_left₀ ih.1 ih.2.1 2),
      (pow_le_pow_left₀ (pow_nonneg hu _) ih.2.2 2).trans (le_roundUpAt 384 _)⟩

/-- Rounded rational bounds for the positive-gap exponential arguments. -/
def compactExpBounds (lo hi : ℚ) : ℚ × ℚ :=
  (roundDown (roundedSquares (roundDownAt 384) (expTaylorBounds (lo / 256) 14).1 8),
    roundUp (roundedSquares (roundUpAt 384) (expTaylorBounds (hi / 256) 14).2 8))

theorem compactExpBounds_sound {lo hi : ℚ} (hl : |lo| ≤ 256) (hu : |hi| ≤ 256)
    {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    ((compactExpBounds lo hi).1 : ℝ) ≤ Real.exp x ∧
      Real.exp x ≤ ((compactExpBounds lo hi).2 : ℝ) := by
  have hq (q : ℚ) (hq : |q| ≤ 256) : |q / 256| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 256)]
    linarith
  have hlo := (expReductionBounds_sound lo (m := 256) (n := 14)
    (by decide) (by decide) (hq lo hl)).1
  have hhi := (expReductionBounds_sound hi (m := 256) (n := 14)
    (by decide) (by decide) (hq hi hu)).2
  have hbase : 0 ≤ (expTaylorBounds (hi / 256) 14).2 := by
    have hs := (expReductionBounds_sound (hi / 256) (m := 1) (n := 14)
      (by decide) (by decide) (by simpa using hq hi hu)).2
    have hs' := (Rat.cast_nonneg (K := ℝ)).mp ((Real.exp_pos _).le.trans hs)
    simpa only [expReductionBounds, Nat.cast_one, div_one, pow_one] using hs'
  obtain ⟨_, hroundLo, hroundHi⟩ :=
    roundedSquares_encloses (expTaylorBounds (lo / 256) 14).1 (expTaylorBounds (hi / 256) 14).2
      (le_max_left _ _) hbase 8
  have hl' : (compactExpBounds lo hi).1 ≤ (expReductionBounds lo 256 14).1 :=
    (roundDown_le _).trans hroundLo
  have hu' : (expReductionBounds hi 256 14).2 ≤ (compactExpBounds lo hi).2 :=
    hroundHi.trans (le_roundUp _)
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hl').trans (hlo.trans (Real.exp_le_exp.mpr hx.1)),
    (Real.exp_le_exp.mpr hx.2).trans (hhi.trans ((Rat.cast_le (K := ℝ)).mpr hu'))⟩

/-- If the checker encloses an arithmetic expression over the computed exponential
intervals, the enclosure holds for the expression evaluated at the actual reals. -/
theorem checked_expression_of_exp_boxes {k m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (box : Fin k → ℚ × ℚ) (x : Fin k → ℝ)
    (hx : ∀ i, ((box i).1 : ℝ) ≤ x i ∧ x i ≤ ((box i).2 : ℝ))
    (hlo : ∀ i, |(box i).1 / (m : ℚ)| ≤ 1) (hhi : ∀ i, |(box i).2 / (m : ℚ)| ≤ 1)
    (e : Expr k) (he : check (fun i ↦ expBoxBounds (box i).1 (box i).2 m n) e = true) :
    ((bounds e).1 : ℝ) ≤ value (fun i ↦ Real.exp (x i)) e ∧
      value (fun i ↦ Real.exp (x i)) e ≤ ((bounds e).2 : ℝ) := by
  refine checked_expression_encloses _ _ (fun i ↦ ?_) e he
  exact ⟨(expReductionBounds_sound _ hm hn (hlo i)).1.trans (Real.exp_le_exp.mpr (hx i).1),
    (Real.exp_le_exp.mpr (hx i).2).trans (expReductionBounds_sound _ hm hn (hhi i)).2⟩

/-- Rational square comparisons suffice to enclose the positive radical over
a rational input interval. The lower bound also certifies a nonnegative radicand. -/
theorem sqrt_box_of_square_bounds {a b l u : ℚ}
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hla : l^2 ≤ a) (hbu : b ≤ u^2)
    {x : ℝ} (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) :
    (l : ℝ) ≤ √x ∧ √x ≤ (u : ℝ) := by
  have hl' : 0 ≤ (l : ℝ) := by exact_mod_cast hl
  have hu' : 0 ≤ (u : ℝ) := by exact_mod_cast hu
  have hla' : (l : ℝ)^2 ≤ (a : ℝ) := by exact_mod_cast hla
  have hbu' : (b : ℝ) ≤ (u : ℝ)^2 := by exact_mod_cast hbu
  have hx0 := (sq_nonneg (l : ℝ)).trans (hla'.trans hx.1)
  exact ⟨(Real.le_sqrt hl' hx0).mpr (hla'.trans hx.1),
    (Real.sqrt_le_iff).mpr ⟨hu', hx.2.trans hbu'⟩⟩

#print axioms checked_expression_of_exp_boxes
#print axioms sqrt_box_of_square_bounds

end RefinedBMV.FourSpectrumLift
