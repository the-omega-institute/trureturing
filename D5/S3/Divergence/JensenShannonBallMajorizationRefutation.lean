/- GID: D5/S3/Divergence/JensenShannonBallMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/JensenShannonBallMajorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim; result=D5/S3/Divergence/JensenShannonBallMajorizationRefutation.result; claim=D5/S3/Divergence/JensenShannonBallMajorizationRefutation.claim
   digest: A three-point Jensen--Shannon ball has no majorization-minimizer. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

/-!
For natural logarithms, a Jensen--Shannon sublevel set need not have a point majorized by
all its members. The square-root metric has the same balls after rescaling the radius.
Majorization uses descending partial sums, including equality of the total sums.
-/

noncomputable section
open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

namespace D5.S3.Divergence.JensenShannonBallMajorizationRefutation

/-- Nonnegative finite probability vectors, including boundary points. -/
def IsProbVec {d : ℕ} (q : Fin d → ℝ) : Prop :=
  D5.S3.TotalVariation.CycleSingleCutMinimax.Probability q

/-- Equation (2.3): `Majorizes x y` means that `y` is majorized by `x`. -/
def Majorizes {d : ℕ} (x y : Fin d → ℝ) : Prop := moreMixed y x

/-- Jensen--Shannon divergence with natural logarithms and the `0 log 0 = 0` convention.
If just one coordinate is zero its weighted logarithm vanishes; if both are zero both
summands vanish, since real division and the real logarithm are totalized at zero. -/
def jensenShannon {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (p i * Real.log (2 * p i / (p i + q i)) +
    q i * Real.log (2 * q i / (p i + q i)))

/-- Equation (3.1), restricted to its majorization-minimum clause. -/
def IsMajorizationMinimizer {d : ℕ} (B : Set (Fin d → ℝ)) (r : Fin d → ℝ) : Prop :=
  r ∈ B ∧ ∀ q ∈ B, Majorizes q r

/-- The Jensen--Shannon clause of Question 1, with a positive divergence threshold. -/
def claim : Prop :=
  ∀ (d : ℕ) (p : Fin d → ℝ), IsProbVec p → ∀ t : ℝ, 0 < t →
    ∃ r, IsMajorizationMinimizer {q | IsProbVec q ∧ jensenShannon p q ≤ t} r

private def term (c x : ℝ) : ℝ :=
  (c * Real.log (2 * c / (c + x)) + x * Real.log (2 * x / (c + x))) / 2

private lemma support_gap {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    term c x - term c y - Real.log (2 * y / (c + y)) / 2 * (x - y) =
      -(c * Real.log ((c + x) / (c + y)) +
        x * Real.log (y * (c + x) / (x * (c + y)))) / 2 := by
  have hcx : c + x ≠ 0 := ne_of_gt (add_pos hc hx)
  have hcy : c + y ≠ 0 := ne_of_gt (add_pos hc hy)
  have first : Real.log (2 * c / (c + x)) - Real.log (2 * c / (c + y)) =
      -Real.log ((c + x) / (c + y)) := by
    rw [Real.log_div (by positivity) hcx, Real.log_div (by positivity) hcy,
      Real.log_div hcx hcy]
    ring
  have second : Real.log (2 * x / (c + x)) - Real.log (2 * y / (c + y)) =
      -Real.log (y * (c + x) / (x * (c + y))) := by
    rw [Real.log_div (by positivity) hcx, Real.log_div (by positivity) hcy,
      Real.log_div (mul_ne_zero hy.ne.symm hcx) (mul_ne_zero hx.ne.symm hcy),
      Real.log_mul two_ne_zero hx.ne.symm, Real.log_mul two_ne_zero hy.ne.symm,
      Real.log_mul hy.ne.symm hcx, Real.log_mul hx.ne.symm hcy]
    ring
  dsimp only [term]
  linear_combination c / 2 * first + x / 2 * second

private lemma supporting_line_pos {c x y : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hy : 0 < y) :
    term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) ≤ term c x ∧
    (term c x = term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) → x = y) := by
  have hu : 0 < (c + x) / (c + y) := div_pos (add_pos hc hx) (add_pos hc hy)
  have hv : 0 < y * (c + x) / (x * (c + y)) := by positivity
  have boundc := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hc.le
  have boundx := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hv) hx.le
  have cancel : c * ((c + x) / (c + y) - 1) +
      x * (y * (c + x) / (x * (c + y)) - 1) = 0 := by
    field_simp
    <;> ring
  have gap := support_gap hc hx hy
  constructor
  · linarith
  · intro heq
    by_contra hne
    have hu_ne : (c + x) / (c + y) ≠ 1 := by
      intro h
      have := (div_eq_one_iff_eq (ne_of_gt (add_pos hc hy))).mp h
      exact hne (by linarith)
    have strictc := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hu hu_ne) hc
    linarith

end D5.S3.Divergence.JensenShannonBallMajorizationRefutation
