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

set_option linter.style.longLine false

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
    ring
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

private lemma supporting_line {c x y : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (hy : 0 < y) :
    term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) ≤ term c x ∧
    (term c x = term c y + Real.log (2 * y / (c + y)) / 2 * (x - y) → x = y) := by
  rcases hx.eq_or_lt with hzero | hpos
  · subst x
    have ratio : 2 * c / (c + 0) = 2 := by field_simp; ring
    have logc : Real.log (2 * c / (c + y)) =
        Real.log 2 - Real.log ((c + y) / c) := by
      rw [Real.log_div (by positivity) (ne_of_gt (add_pos hc hy)),
        Real.log_mul two_ne_zero hc.ne.symm,
        Real.log_div (ne_of_gt (add_pos hc hy)) hc.ne.symm]
      ring
    have gap : term c 0 - term c y - Real.log (2 * y / (c + y)) / 2 * (0 - y) =
        c / 2 * Real.log ((c + y) / c) := by
      unfold term
      rw [ratio, logc]
      ring
    have positive : 0 < c / 2 * Real.log ((c + y) / c) :=
      mul_pos (by positivity) (Real.log_pos ((one_lt_div hc).mpr (by linarith)))
    constructor
    · linarith
    · intro heq
      linarith
  · exact supporting_line_pos hc hpos hy

private def p : Fin 3 → ℝ := ![2/3, 4/15, 1/15]
private def a : Fin 3 → ℝ := ![1/2, 2/5, 1/10]
private def b : Fin 3 → ℝ := ![8/15, 1/3, 2/15]

private lemma probability_data : IsProbVec p ∧ IsProbVec a ∧ IsProbVec b := by
  norm_num [IsProbVec, D5.S3.TotalVariation.CycleSingleCutMinimax.Probability,
    p, a, b, Fin.sum_univ_succ, Fin.forall_fin_succ]

private lemma js_three (q : Fin 3 → ℝ) :
    jensenShannon p q = term (2/3) (q 0) + term (4/15) (q 1) + term (1/15) (q 2) := by
  norm_num [jensenShannon, Fin.sum_univ_succ, p, term]
  ring

private lemma term_nonneg_eq {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    0 ≤ term c x ∧ (term c x = 0 → x = c) := by
  have ratio : 2 * c / (c + c) = 1 := by field_simp; ring
  have hs := supporting_line hc hx hc
  simpa only [term, ratio, Real.log_one, mul_zero, add_zero, zero_div, zero_mul,
    zero_add] using hs

private lemma radius_pos : 0 < jensenShannon p a := by
  have h0 := term_nonneg_eq (c := (2/3:ℝ)) (x := (1/2:ℝ)) (by norm_num) (by norm_num)
  have h1 := term_nonneg_eq (c := (4/15:ℝ)) (x := (2/5:ℝ)) (by norm_num) (by norm_num)
  have h2 := term_nonneg_eq (c := (1/15:ℝ)) (x := (1/10:ℝ)) (by norm_num) (by norm_num)
  have strict : 0 < term (2/3) (1/2) := by
    rcases h0.1.eq_or_lt with heq | hlt
    · exact False.elim (by have := h0.2 heq.symm; norm_num at this)
    · exact hlt
  rw [js_three]
  change 0 < term (2/3) (1/2) + term (4/15) (2/5) + term (1/15) (1/10)
  linarith [h1.1, h2.1]

private lemma majorized_bounds {r : Fin 3 → ℝ} (h : Majorizes a r) :
    ∀ i, 1/10 ≤ r i ∧ r i ≤ 1/2 := by
  have h1 := h.1 1 (by decide)
  have h2 := h.1 2 (by decide)
  have h3 := h.2
  norm_num [a, prefixSum, desc, List.ofFn_succ, List.mergeSort] at h1 h2 h3
  by_cases h01 : r 1 ≤ r 0 <;> by_cases h02 : r 2 ≤ r 0 <;> by_cases h12 : r 2 ≤ r 1 <;>
    norm_num [List.merge, h01, h02, h12] at h1 h2 h3 <;>
    norm_num [Fin.forall_fin_succ] <;> (repeat' constructor) <;> linarith

private lemma unique_candidate {r : Fin 3 → ℝ} (hr : IsProbVec r)
    (hm : Majorizes a r) (hball : jensenShannon p r ≤ jensenShannon p a) : r = a := by
  have bounds := majorized_bounds hm
  have h0 := supporting_line (c := (2/3:ℝ)) (x := r 0) (y := (1/2:ℝ))
    (by norm_num) (hr.1 0) (by norm_num)
  have h1 := supporting_line (c := (4/15:ℝ)) (x := r 1) (y := (2/5:ℝ))
    (by norm_num) (hr.1 1) (by norm_num)
  have h2 := supporting_line (c := (1/15:ℝ)) (x := r 2) (y := (1/10:ℝ))
    (by norm_num) (hr.1 2) (by norm_num)
  norm_num at h0 h1 h2
  have total : r 0 + r 1 + r 2 = 1 := by
    simpa [IsProbVec, D5.S3.TotalVariation.CycleSingleCutMinimax.Probability,
      Fin.sum_univ_succ, add_assoc] using hr.2
  have logdiff : Real.log (6/7:ℝ) - Real.log (6/5:ℝ) = Real.log (5/7:ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have tangent : 0 ≤ Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) +
      Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) +
      Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) := by
    have sign := mul_nonneg_of_nonpos_of_nonpos
      (Real.log_neg (by norm_num : (0:ℝ) < 5/7) (by norm_num)).le
      (sub_nonpos.mpr (bounds 0).2)
    have tangent_eq : Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) +
        Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) +
        Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) =
        Real.log (5/7:ℝ) / 2 * (r 0 - 1/2) := by
      linear_combination Real.log (6/5:ℝ) / 2 * total + (r 0 - 1/2) / 2 * logdiff
    rw [tangent_eq]
    linarith
  rw [js_three, js_three] at hball
  change term (2/3) (r 0) + term (4/15) (r 1) + term (1/15) (r 2) ≤
    term (2/3) (1/2) + term (4/15) (2/5) + term (1/15) (1/10) at hball
  have equal0 : term (2/3) (r 0) = term (2/3) (1/2) +
      Real.log (6/7:ℝ) / 2 * (r 0 - 1/2) := by linarith [h0.1, h1.1, h2.1]
  have equal1 : term (4/15) (r 1) = term (4/15) (2/5) +
      Real.log (6/5:ℝ) / 2 * (r 1 - 2/5) := by linarith [h0.1, h1.1, h2.1]
  have equal2 : term (1/15) (r 2) = term (1/15) (1/10) +
      Real.log (6/5:ℝ) / 2 * (r 2 - 1/10) := by linarith [h0.1, h1.1, h2.1]
  funext i
  fin_cases i
  · exact h0.2 equal0
  · exact h1.2 equal1
  · exact h2.2 equal2

end D5.S3.Divergence.JensenShannonBallMajorizationRefutation
