/- GID: D5/S3/Analytic/TailIntegerRootPrediction
   generality: I
   mirror-B: D5/B/S3/Analytic/TailIntegerRootPrediction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The row-eight and row-ten tail polynomials have exactly the predicted integer roots. -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/- Duplicate and library-search audit (2026-09-05):
   * Exact and spelling-variant D5 searches covered tail polynomials, integer
     roots, principal-part coefficients, and the values 83 and 41.
   * Digestion, digest, git-history, generalized theorem-shape, and in-flight
     searches found no existing theorem for either predicted tail root.
   * Pinned Mathlib supplies `Nat.choose_zero_right` and
     `Nat.choose_one_right`; it has no theorem for these source coefficients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.TailIntegerRootPrediction

/-- The two-term specialization of
`T_a(b) = sum_j P_j(a) * choose (b + j - 1) (j - 1)`. -/
def twoTermTail (first second : ℚ) (b : ℕ) : ℚ :=
  first * (Nat.choose b 0 : ℚ) + second * (Nat.choose (b + 1) 1 : ℚ)

/-- The roots predicted from the displayed principal parts are exact and
unique among natural-number arguments: row eight vanishes only at `83`, and
row ten vanishes only at `41`. -/
theorem tail_integer_roots_are_exact :
    (∀ b : ℕ, twoTermTail 42 (-1 / 2) b = 0 ↔ b = 83) ∧
      (∀ b : ℕ, twoTermTail 336 (-8) b = 0 ↔ b = 41) := by
  constructor
  · intro b
    constructor
    · intro h
      norm_num [twoTermTail] at h
      push_cast at h
      have hb : (b : ℚ) = 83 := by linarith
      exact_mod_cast hb
    · intro h
      subst b
      norm_num [twoTermTail]
  · intro b
    constructor
    · intro h
      norm_num [twoTermTail] at h
      push_cast at h
      have hb : (b : ℚ) = 41 := by linarith
      exact_mod_cast hb
    · intro h
      subst b
      norm_num [twoTermTail]

#print axioms tail_integer_roots_are_exact

end D5.S3.Analytic.TailIntegerRootPrediction
