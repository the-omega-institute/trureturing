/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickQuadratic
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Direct quadratic-perspective Jensen inequality for finite matrix effects. -/

import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Finite matrix sum-of-squares inequalities for the quadratic compact perspective. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

/-- The bounded-perspective generator, with finite limits at both endpoints. -/
def starGenerator (u : ℝ) : ℝ := (u - 1) ^ 2 / (u + 1)

/-- Its closed scalar perspective, including the zero-mass corner. -/
def starPerspective (p q : ℝ) : ℝ := (p - q) ^ 2 / (p + q)

theorem star_perspective_compact (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    (1 - x) * starGenerator (x / (1 - x)) = (2 * x - 1) ^ 2 := by
  unfold starGenerator
  have h : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hden : x / (1 - x) + 1 ≠ 0 := by
    have : 0 < x / (1 - x) := div_pos hx (sub_pos.mpr hx1)
    linarith
  field_simp
  ring

private theorem square_variance_identity (E : k → Matrix n n ℂ) (r : k → ℝ)
    (hsum : ∑ i, E i = 1) :
    let M := ∑ i, r i • E i
    ∑ i, ((r i • (1 : Matrix n n ℂ) - M) * E i *
      (r i • (1 : Matrix n n ℂ) - M)) = (∑ i, (r i) ^ 2 • E i) - M * M := by
  classical
  dsimp only
  let M := ∑ i, r i • E i
  change (∑ i, (r i • (1 : Matrix n n ℂ) - M) * E i *
    (r i • (1 : Matrix n n ℂ) - M)) = (∑ i, (r i) ^ 2 • E i) - M * M
  have term (i : k) :
      (r i • (1 : Matrix n n ℂ) - M) * E i * (r i • (1 : Matrix n n ℂ) - M) =
      (r i) ^ 2 • E i - r i • E i * M - M * (r i • E i) + M * E i * M := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, smul_add, smul_smul, pow_two]
    abel
  simp_rw [term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
  change (∑ i, (r i) ^ 2 • E i) - M * M - M * M + M * 1 * M = _
  rw [Matrix.mul_one]
  abel

/-- Finite Kadison inequality for a scalar observable and positive matrix
effects, proved by the actual matrix sum of squares. -/
theorem square_jensen (E : k → Matrix n n ℂ) (r : k → ℝ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : ∑ i, E i = 1) :
    (∑ i, r i • E i) * (∑ i, r i • E i) ≤ ∑ i, (r i) ^ 2 • E i := by
  classical
  let M := ∑ i, r i • E i
  have hM : M.IsHermitian := by
    apply isSelfAdjoint_sum
    intro i _
    exact (hE i).isHermitian.smul (IsSelfAdjoint.all (r i))
  have hp : (∑ i, (r i • (1 : Matrix n n ℂ) - M) * E i *
      (r i • (1 : Matrix n n ℂ) - M)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    have hX : (r i • (1 : Matrix n n ℂ) - M).IsHermitian :=
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (r i))).sub hM
    simpa only [hX.eq] using (hE i).conjTranspose_mul_mul_same (r i • (1 : Matrix n n ℂ) - M)
  apply Matrix.le_iff.mpr
  exact square_variance_identity E r hsum ▸ hp

/-- The same inequality on an actual support corner. The missing effect is
completed by `1 - ∑ E` with scalar value zero. -/
theorem square_jensen_subunital (E : k → Matrix n n ℂ) (r : k → ℝ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : ∑ i, E i ≤ 1) :
    (∑ i, r i • E i) * (∑ i, r i • E i) ≤ ∑ i, (r i) ^ 2 • E i := by
  classical
  let F : Option k → Matrix n n ℂ := fun j =>
    match j with
    | none => 1 - ∑ i, E i
    | some i => E i
  let s : Option k → ℝ := fun j =>
    match j with
    | none => 0
    | some i => r i
  have hF : ∀ j, (F j).PosSemidef := by
    intro j
    cases j with
    | none => exact (sub_nonneg.mpr hsum).posSemidef
    | some i => exact hE i
  have hsumF : ∑ j, F j = 1 := by simp [F]
  simpa [F, s] using square_jensen F s hF hsumF

/-- The compact perspective `(2x-1)^2` obeys matrix Jensen without any
operator-convex-function hypothesis. Endpoint labels `x=0,1` are allowed. -/
theorem compact_quadratic_jensen (E : k → Matrix n n ℂ) (x : k → ℝ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : ∑ i, E i = 1) :
    ((2 : ℝ) • (∑ i, x i • E i) - 1) * ((2 : ℝ) • (∑ i, x i • E i) - 1) ≤
      ∑ i, (2 * x i - 1) ^ 2 • E i := by
  have hM : (∑ i, (2 * x i - 1) • E i) = (2 : ℝ) • (∑ i, x i • E i) - 1 := by
    simp only [sub_smul, mul_smul, one_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hsum]
  simpa only [hM] using square_jensen E (fun i => 2 * x i - 1) hE hsum

/-- Positive trace weights preserve the quadratic-perspective lower bound. -/
theorem compact_quadratic_trace_bound (S : Matrix n n ℂ) (hS : S.PosSemidef)
    (E : k → Matrix n n ℂ) (x : k → ℝ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : ∑ i, E i = 1) :
    (Matrix.trace (S * (((2 : ℝ) • (∑ i, x i • E i) - 1) *
      ((2 : ℝ) • (∑ i, x i • E i) - 1)))).re ≤
      ∑ i, (2 * x i - 1) ^ 2 * (Matrix.trace (S * E i)).re := by
  let T := ((2 : ℝ) • (∑ i, x i • E i) - 1) *
    ((2 : ℝ) • (∑ i, x i • E i) - 1)
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hS
    (Matrix.le_iff.mp (compact_quadratic_jensen E x hE hsum))
  change 0 ≤ (Matrix.trace (S * ((∑ i, (2 * x i - 1) ^ 2 • E i) - T))).re at h
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  have he : (Matrix.trace (S * (∑ i, (2 * x i - 1) ^ 2 • E i))).re =
      ∑ i, (2 * x i - 1) ^ 2 * (Matrix.trace (S * E i)).re := by
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he] at h
  exact sub_nonneg.mp h

end D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
