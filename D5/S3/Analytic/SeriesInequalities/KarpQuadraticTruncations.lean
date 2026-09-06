/- GID: D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations
   mirror-E: none(waiver:general-parameter-inequalities)
   anchors: []
   utility: none
   digest: Karp-Zhang quadratic truncations have nonnegative Turan coefficients. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
The targets are the two truncations registered as r2 and r3 in issue #5969,
from Karp and Zhang, DOI 10.1007/s13540-023-00238-0. They do not assert the
full series conjectures. Both shift parameters below are real, not integer.

Library search (2026-09-07): D5 searches for Karp, Pochhammer, log-convex,
log-concave and coefficient nonnegativity found no matching theorem. The two
Pochhammer modules concern Chebyshev expansion and root intervals. Pinned
Mathlib v4.33.0 supplies ascPochhammer_succ_eval, ascPochhammer_pos,
Polynomial.coeff_mul and coeff_C_mul_X_pow; it has no matching Turan theorem.
The log-convex Gamma and convex descending-Pochhammer lemmas have different
conclusions. Loogle's ascPochhammer search likewise found no matching result;
installed third-party Lean sources had no candidate.

Utility is none: these are symbolic inequalities over all real parameters,
not bounded enumeration, a checker, a numerical reduction, or a certified
parameter instance. The mixed (3,6) identity is an active escape witness for
r2; the exact real-shift coefficient identities provide the witness for r3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Polynomial

namespace D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations

/-- Conjecture 1 at r = 3 with only indices 1 and 2 retained. -/
def r2Polynomial (c1 c2 t : Real) : Real[X] :=
  C (c1 / (Nat.factorial 2 : Real) * (ascPochhammer Real 3).eval t) * X +
    C (c2 / (Nat.factorial 5 : Real) * (ascPochhammer Real 6).eval t) * X ^ 2

/-- Conjecture 2 with indices 0, 1 and 2 retained. -/
def r3Polynomial (h0 h1 h2 t : Real) : Real[X] :=
  C h0 + C (h1 * t) * X + C (h2 * t * (t + 3) / 2) * X ^ 2

private def quadratic (z : Real) (f g : Real -> Real) (t : Real) : Real[X] :=
  C z + C (f t) * X + C (g t) * X ^ 2

private theorem quadratic_turan_coeff_nonneg
    (z : Real) (f g : Real -> Real) (mu alpha beta : Real)
    (h1 : 0 <= z * (f (mu + alpha) + f (mu + beta) - f mu - f (mu + alpha + beta)))
    (h2 : 0 <= f (mu + alpha) * f (mu + beta) - f mu * f (mu + alpha + beta) +
      z * (g (mu + alpha) + g (mu + beta) - g mu - g (mu + alpha + beta)))
    (h3 : 0 <= f (mu + alpha) * g (mu + beta) + g (mu + alpha) * f (mu + beta) -
      f mu * g (mu + alpha + beta) - g mu * f (mu + alpha + beta))
    (h4 : 0 <= g (mu + alpha) * g (mu + beta) - g mu * g (mu + alpha + beta))
    (m : Nat) :
    0 <= (quadratic z f g (mu + alpha) * quadratic z f g (mu + beta) -
      quadratic z f g mu * quadratic z f g (mu + alpha + beta)).coeff m := by
  have expansion : quadratic z f g (mu + alpha) * quadratic z f g (mu + beta) -
      quadratic z f g mu * quadratic z f g (mu + alpha + beta) =
      C (z * (f (mu + alpha) + f (mu + beta) - f mu - f (mu + alpha + beta))) * X ^ 1 +
      C (f (mu + alpha) * f (mu + beta) - f mu * f (mu + alpha + beta) +
        z * (g (mu + alpha) + g (mu + beta) - g mu - g (mu + alpha + beta))) * X ^ 2 +
      C (f (mu + alpha) * g (mu + beta) + g (mu + alpha) * f (mu + beta) -
        f mu * g (mu + alpha + beta) - g mu * f (mu + alpha + beta)) * X ^ 3 +
      C (g (mu + alpha) * g (mu + beta) - g mu * g (mu + alpha + beta)) * X ^ 4 := by
    simp only [quadratic, map_add, map_sub, map_mul]
    ring
  rw [expansion]
  simp only [coeff_add, coeff_C_mul_X_pow]
  split_ifs <;> positivity

private theorem pochhammer_turan_nonneg (n : Nat) (mu alpha beta : Real)
    (hmu : 0 < mu) (ha : 0 <= alpha) (hb : 0 <= beta) :
    0 <= (ascPochhammer Real n).eval (mu + alpha) *
      (ascPochhammer Real n).eval (mu + beta) -
      (ascPochhammer Real n).eval mu * (ascPochhammer Real n).eval (mu + alpha + beta) := by
  apply sub_nonneg.mpr
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [ascPochhammer_succ_eval]
    calc
      (ascPochhammer Real n).eval mu * (mu + n) *
          ((ascPochhammer Real n).eval (mu + alpha + beta) * (mu + alpha + beta + n)) =
          ((ascPochhammer Real n).eval mu * (ascPochhammer Real n).eval (mu + alpha + beta)) *
            ((mu + n) * (mu + alpha + beta + n)) := by ring
      _ <= ((ascPochhammer Real n).eval (mu + alpha) *
          (ascPochhammer Real n).eval (mu + beta)) *
            ((mu + alpha + n) * (mu + beta + n)) := by
        apply mul_le_mul ih
        · nlinarith [mul_nonneg ha hb]
        · positivity
        · exact mul_nonneg (ascPochhammer_pos n _ (by positivity)).le
            (ascPochhammer_pos n _ (by positivity)).le
      _ = _ := by ring

-- Here v = alpha + beta, w = alpha * beta, d = (alpha - beta)^2.
-- In these nonnegative coordinates the mixed (3,6) difference has 44 positive terms.
private def mixedPositivePart (u v w d : Real) : Real :=
  18 * u ^ 5 +
  u ^ 4 * (3 * d + 45 * v + 6 * w + 120) +
  u ^ 3 * (6 * d * v + 48 * d + 12 * v * w + 240 * v + 186 * w + 300) +
  u ^ 2 * (3 * d ^ 2 + 27 * d * v + 21 * d * w + 158 * d +
    99 * v * w + 450 * v + 28 * w ^ 2 + 676 * w + 358) +
  u * (6 * d ^ 2 + 3 * d * v * w + 38 * d * v + 51 * d * w + 178 * d +
    4 * v * w ^ 2 + 196 * v * w + 358 * v + 98 * w ^ 2 + 806 * w + 212) +
  2 * d ^ 2 + 3 * d * v * w + 14 * d * v + d * w ^ 2 + 27 * d * w + 58 * d +
  7 * v * w ^ 2 + 103 * v * w + 106 * v + w ^ 3 + 76 * w ^ 2 + 295 * w + 60

private theorem mixed_pochhammer_identity (mu alpha beta : Real) :
    (ascPochhammer Real 3).eval (mu + alpha) * (ascPochhammer Real 6).eval (mu + beta) +
      (ascPochhammer Real 6).eval (mu + alpha) * (ascPochhammer Real 3).eval (mu + beta) -
      (ascPochhammer Real 3).eval mu * (ascPochhammer Real 6).eval (mu + alpha + beta) -
      (ascPochhammer Real 6).eval mu * (ascPochhammer Real 3).eval (mu + alpha + beta) =
      alpha * beta * (alpha + beta + 2 * mu + 8) *
        mixedPositivePart mu (alpha + beta) (alpha * beta) ((alpha - beta) ^ 2) := by
  norm_num [ascPochhammer_succ_eval, ascPochhammer_zero, mixedPositivePart]
  ring

private theorem mixed_pochhammer_nonneg (mu alpha beta : Real)
    (hmu : 0 < mu) (ha : 0 <= alpha) (hb : 0 <= beta) :
    0 <= (ascPochhammer Real 3).eval (mu + alpha) * (ascPochhammer Real 6).eval (mu + beta) +
      (ascPochhammer Real 6).eval (mu + alpha) * (ascPochhammer Real 3).eval (mu + beta) -
      (ascPochhammer Real 3).eval mu * (ascPochhammer Real 6).eval (mu + alpha + beta) -
      (ascPochhammer Real 6).eval mu * (ascPochhammer Real 3).eval (mu + alpha + beta) := by
  rw [mixed_pochhammer_identity]
  unfold mixedPositivePart
  positivity

/-- All coefficients of the two-term r = 3 Turan difference are nonnegative. -/
theorem r2_coeff_nonneg (c1 c2 mu alpha beta : Real)
    (hc1 : 0 <= c1) (hc2 : 0 <= c2) (hmu : 0 < mu)
    (ha : 0 <= alpha) (hb : 0 <= beta) (m : Nat) :
    0 <= (r2Polynomial c1 c2 (mu + alpha) * r2Polynomial c1 c2 (mu + beta) -
      r2Polynomial c1 c2 mu * r2Polynomial c1 c2 (mu + alpha + beta)).coeff m := by
  let f := fun t : Real => c1 / (Nat.factorial 2 : Real) * (ascPochhammer Real 3).eval t
  let g := fun t : Real => c2 / (Nat.factorial 5 : Real) * (ascPochhammer Real 6).eval t
  suffices h : 0 <= (quadratic 0 f g (mu + alpha) * quadratic 0 f g (mu + beta) -
      quadratic 0 f g mu * quadratic 0 f g (mu + alpha + beta)).coeff m by
    simpa only [quadratic, map_zero, zero_add, f, g, r2Polynomial] using h
  apply quadratic_turan_coeff_nonneg
  · simp
  · convert! mul_nonneg (sq_nonneg (c1 / (Nat.factorial 2 : Real)))
      (pochhammer_turan_nonneg 3 mu alpha beta hmu ha hb) using 1
    ring
  · convert! mul_nonneg
      (show 0 <= c1 / (Nat.factorial 2 : Real) * (c2 / (Nat.factorial 5 : Real)) by positivity)
      (mixed_pochhammer_nonneg mu alpha beta hmu ha hb) using 1
    ring
  · convert! mul_nonneg (sq_nonneg (c2 / (Nat.factorial 5 : Real)))
      (pochhammer_turan_nonneg 6 mu alpha beta hmu ha hb) using 1
    ring

/-- The three-term truncation has nonnegative coefficients for arbitrary real shifts. -/
theorem r3_coeff_nonneg (h0 h1 h2 mu alpha beta : Real)
    (_hh0 : 0 <= h0) (hh1 : 0 <= h1) (hh2 : 0 <= h2) (hlc : h0 * h2 <= h1 ^ 2)
    (hmu : 0 < mu) (ha : 0 <= alpha) (hb : 0 <= beta) (m : Nat) :
    0 <= (r3Polynomial h0 h1 h2 (mu + alpha) * r3Polynomial h0 h1 h2 (mu + beta) -
      r3Polynomial h0 h1 h2 mu * r3Polynomial h0 h1 h2 (mu + alpha + beta)).coeff m := by
  let f := fun t : Real => h1 * t
  let g := fun t : Real => h2 * t * (t + 3) / 2
  suffices h : 0 <= (quadratic h0 f g (mu + alpha) * quadratic h0 f g (mu + beta) -
      quadratic h0 f g mu * quadratic h0 f g (mu + alpha + beta)).coeff m by
    exact h
  apply quadratic_turan_coeff_nonneg
  · dsimp [f]
    ring_nf
    exact le_rfl
  · convert! mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hlc) using 1
    ring
  · have h : 0 <= h1 * h2 * alpha * beta * (alpha + beta + 2 * mu + 6) / 2 := by
      positivity
    convert h using 1
    ring
  · have h : 0 <= h2 ^ 2 * alpha * beta *
        (alpha * beta + 2 * alpha * mu + 3 * alpha + 2 * beta * mu + 3 * beta +
          2 * mu ^ 2 + 6 * mu + 9) / 4 := by positivity
    convert h using 1
    ring

#print axioms r2_coeff_nonneg
#print axioms r3_coeff_nonneg

end D5.S3.Analytic.SeriesInequalities.KarpQuadraticTruncations
