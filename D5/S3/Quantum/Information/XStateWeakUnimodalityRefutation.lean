/- GID: D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/XStateWeakUnimodalityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.claim; result=D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result; claim=D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.claim
   digest: The X-state conditional-entropy function f1 of Eq. (A1) is not weakly unimodal. -/

/-
proof_shape: h2, h4, wParam, r1, r2, f1, ArgsNonneg, WeaklyUnimodal:
  definition (Shannon entropies in bits through the frozen shannonEntropy, Eq. (A1) with r_{1,2}
  and w, nonnegativity of every Shannon argument, and the Appendix definition of weak
  unimodality with its minimum form)
proof_shape: claim: definition (published unimodality hypothesis, arXiv:1702.03728, Section 2
  and Appendix, for f1 on [0, 1])
proof_shape: result: bind-only (as local steps: nonnegativity of the Shannon arguments on
  [0, 1] by quadratic bounds, square roots bracketed by rationals, Real.negMulLog bracketed
  through monotonicity of Real.log, logarithms of rationals bounded by
  Real.abs_log_sub_add_sum_range_le and Real.log_two_near_10, and evaluation at
  x = 0, 27/50, 177/200, 1)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12783; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Entropy/MaxEntropy.shannonEntropy
    sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
-/

import D5.S3.Entropy.MaxEntropy
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.XStateWeakUnimodalityRefutation

open D5.S3.Entropy.MaxEntropy (shannonEntropy)

/-!
M. A. Yurischev, *Extremal properties of conditional entropy and quantum discord for XXZ,
symmetric quantum states*, Quantum Inf. Process. 16 (2017) 249, arXiv:1702.03728, writes the
conditional entropy of a two-qubit X state through
`f₁(x) = -h₂((1 + p₂x)/2, (1 - p₂x)/2) + h₄((1 + p₂x ± √r₁)/4, (1 - p₂x ± √r₂)/4)` on
`x ∈ [0, 1]`, Eq. (A1), with `r_{1,2} = (p₁ ± p₅x)² + 4w²(1 - x²)` and
`w = (|p₃ + p₄| + |p₃ - p₄|)/4`, and supposes that `f₁` is weakly unimodal on `[0, 1]` for every
choice of `p₁, …, p₅` with nonnegative Shannon arguments. For
`p = (-2466, -1107, 187, -163, 1138)/2500` one has
`f₁(0) > f₁(27/50) < f₁(177/200) > f₁(1)`, which no weakly unimodal function admits.
-/

/-- `h₂(a, b) = -a log₂ a - b log₂ b`: the Shannon entropy of `(a, b)`, in bits. -/
noncomputable def h2 (a b : ℝ) : ℝ := shannonEntropy ![a, b] / Real.log 2

/-- `h₄(a, b, c, d) = -a log₂ a - b log₂ b - c log₂ c - d log₂ d`, in bits. -/
noncomputable def h4 (a b c d : ℝ) : ℝ := shannonEntropy ![a, b, c, d] / Real.log 2

/-- `w = (|p₃ + p₄| + |p₃ - p₄|)/4`. -/
noncomputable def wParam (p₃ p₄ : ℝ) : ℝ := (|p₃ + p₄| + |p₃ - p₄|) / 4

/-- `r₁ = (p₁ + p₅x)² + 4w²(1 - x²)`. -/
noncomputable def r1 (x p₁ p₃ p₄ p₅ : ℝ) : ℝ :=
  (p₁ + p₅ * x) ^ 2 + 4 * wParam p₃ p₄ ^ 2 * (1 - x ^ 2)

/-- `r₂ = (p₁ - p₅x)² + 4w²(1 - x²)`. -/
noncomputable def r2 (x p₁ p₃ p₄ p₅ : ℝ) : ℝ :=
  (p₁ - p₅ * x) ^ 2 + 4 * wParam p₃ p₄ ^ 2 * (1 - x ^ 2)

/-- Eq. (A1). -/
noncomputable def f1 (x p₁ p₂ p₃ p₄ p₅ : ℝ) : ℝ :=
  -h2 ((1 + p₂ * x) / 2) ((1 - p₂ * x) / 2) +
    h4 ((1 + p₂ * x + √(r1 x p₁ p₃ p₄ p₅)) / 4) ((1 + p₂ * x - √(r1 x p₁ p₃ p₄ p₅)) / 4)
      ((1 - p₂ * x + √(r2 x p₁ p₃ p₄ p₅)) / 4) ((1 - p₂ * x - √(r2 x p₁ p₃ p₄ p₅)) / 4)

/-- Every argument of the Shannon functions in Eq. (A1) is nonnegative at `x`. -/
def ArgsNonneg (x p₁ p₂ p₃ p₄ p₅ : ℝ) : Prop :=
  0 ≤ (1 + p₂ * x) / 2 ∧ 0 ≤ (1 - p₂ * x) / 2 ∧
    0 ≤ (1 + p₂ * x + √(r1 x p₁ p₃ p₄ p₅)) / 4 ∧ 0 ≤ (1 + p₂ * x - √(r1 x p₁ p₃ p₄ p₅)) / 4 ∧
      0 ≤ (1 - p₂ * x + √(r2 x p₁ p₃ p₄ p₅)) / 4 ∧ 0 ≤ (1 - p₂ * x - √(r2 x p₁ p₃ p₄ p₅)) / 4

/-- Weak unimodality on `[a, b]` (Appendix): for some `x_m ∈ [a, b]`, `f` is weakly increasing
for `x ≤ x_m` and weakly decreasing for `x ≥ x_m`, or, in the analogous form for the minimum,
weakly decreasing and then weakly increasing. -/
def WeaklyUnimodal (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ xm ∈ Set.Icc a b,
    (MonotoneOn f (Set.Icc a xm) ∧ AntitoneOn f (Set.Icc xm b)) ∨
      (AntitoneOn f (Set.Icc a xm) ∧ MonotoneOn f (Set.Icc xm b))

/-- The unimodality hypothesis: for all `p₁, …, p₅` whose Shannon arguments in Eq. (A1) are
nonnegative on `[0, 1]`, `f₁` is weakly unimodal on `[0, 1]`. -/
def claim : Prop :=
  ∀ p₁ p₂ p₃ p₄ p₅ : ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, ArgsNonneg x p₁ p₂ p₃ p₄ p₅) →
    WeaklyUnimodal (fun x => f1 x p₁ p₂ p₃ p₄ p₅) 0 1

set_option maxHeartbeats 2000000 in
-- Thirty-one rational logarithm bounds and four evaluations are checked in this declaration.
/-- The hypothesis fails at `p = (-2466, -1107, 187, -163, 1138)/2500`. -/
theorem result : ¬ claim := by
  intro h
  have nmlB : ∀ t l u A B : ℝ, 0 < l → l ≤ t → t ≤ u → u ≤ 1 → A ≤ Real.log l →
      Real.log u ≤ B → l * -B ≤ Real.negMulLog t ∧ Real.negMulLog t ≤ u * -A := by
    intro t l u A B hl hlt htu hu hA hB
    have ht : 0 < t := lt_of_lt_of_le hl hlt
    have h1 : Real.log l ≤ Real.log t := Real.log_le_log hl hlt
    have h2 : Real.log t ≤ Real.log u := Real.log_le_log ht htu
    have h3 : Real.log t ≤ 0 := Real.log_nonpos ht.le (htu.trans hu)
    rw [Real.negMulLog]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hlt) (neg_nonneg.2 h3),
        mul_nonneg hl.le (by linarith : 0 ≤ B - Real.log t)]
    · nlinarith [mul_nonneg (sub_nonneg.2 htu) (neg_nonneg.2 h3),
        mul_nonneg (by linarith : (0 : ℝ) ≤ u) (by linarith : 0 ≤ Real.log t - A)]
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have e : ∀ x a b c d g : ℝ, f1 x a b c d g * Real.log 2 =
      Real.negMulLog ((1 + b * x + √(r1 x a c d g)) / 4) +
        Real.negMulLog ((1 + b * x - √(r1 x a c d g)) / 4) +
        Real.negMulLog ((1 - b * x + √(r2 x a c d g)) / 4) +
        Real.negMulLog ((1 - b * x - √(r2 x a c d g)) / 4) -
        (Real.negMulLog ((1 + b * x) / 2) + Real.negMulLog ((1 - b * x) / 2)) := by
    intro x a b c d g
    simp only [f1, h2, h4, shannonEntropy, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hw : wParam (187/2500) (-163/2500) = 187/5000 := by
    rw [wParam, abs_of_pos (by norm_num : (0 : ℝ) < 187/2500 + -163/2500),
      abs_of_pos (by norm_num : (0 : ℝ) < 187/2500 - -163/2500)]
    norm_num
  have hadm : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ArgsNonneg x (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) := by
    rintro x ⟨hx0, hx1⟩
    unfold ArgsNonneg
    have hx : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
    have hq1 : 0 ≤ 1 + -1107/2500 * x := by linarith
    have hq2 : 0 ≤ 1 - -1107/2500 * x := by linarith
    have hs1 : √(r1 x (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤ 1 + -1107/2500 * x := by
      rw [Real.sqrt_le_left hq1, r1, hw]
      nlinarith [sq_nonneg (1 - x), sq_nonneg x]
    have hs2 : √(r2 x (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤ 1 - -1107/2500 * x := by
      rw [Real.sqrt_le_left hq2, r2, hw]
      nlinarith [sq_nonneg (1 - x), sq_nonneg x]
    have h0 := Real.sqrt_nonneg (r1 x (-1233/1250) (187/2500) (-163/2500) (569/1250))
    have h0' := Real.sqrt_nonneg (r2 x (-1233/1250) (187/2500) (-163/2500) (569/1250))
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have c0 : (-698545723773/1000000000000 : ℝ) ≤ Real.log (24865400317/50000000000 : ℝ) ∧ Real.log
      (24865400317/50000000000 : ℝ) ≤ (-698545703773/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(134599683/25000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 134599683/25000000000 = 24865400317/25000000000 by norm_num] at h
    have hs : Real.log (24865400317/50000000000 : ℝ) = Real.log (24865400317/25000000000 : ℝ) - 1 *
        Real.log 2 := by
      rw [show (24865400317/25000000000 : ℝ) = (24865400317/50000000000 : ℝ) * 2 ^ 1 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c1 : (-698545723771/1000000000000 : ℝ) ≤ Real.log (497308006341/1000000000000 : ℝ) ∧ Real.log
      (497308006341/1000000000000 : ℝ) ≤ (-698545703771/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(2691993659/500000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 2691993659/500000000000 = 497308006341/500000000000 by norm_num] at h
    have hs : Real.log (497308006341/1000000000000 : ℝ) = Real.log
        (497308006341/500000000000 : ℝ) - 1 * Real.log 2 := by
      rw [show (497308006341/500000000000 : ℝ) =
          (497308006341/1000000000000 : ℝ) * 2 ^ 1 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c2 : (-59174732327/10000000000 : ℝ) ≤ Real.log (2691993659/1000000000000 : ℝ) ∧ Real.log
      (2691993659/1000000000000 : ℝ) ≤ (-59174732127/10000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(1214256341/3906250000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 1214256341/3906250000 = 2691993659/3906250000 by norm_num] at h
    have hs : Real.log (2691993659/1000000000000 : ℝ) = Real.log (2691993659/3906250000 : ℝ) - 8 *
        Real.log 2 := by
      rw [show (2691993659/3906250000 : ℝ) = (2691993659/1000000000000 : ℝ) * 2 ^ 8 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c3 : (-5917473232329/1000000000000 : ℝ) ≤ Real.log (134599683/50000000000 : ℝ) ∧ Real.log
      (134599683/50000000000 : ℝ) ≤ (-5917473212329/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(60712817/195312500 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 60712817/195312500 = 134599683/195312500 by norm_num] at h
    have hs : Real.log (134599683/50000000000 : ℝ) = Real.log (134599683/195312500 : ℝ) - 8 *
        Real.log 2 := by
      rw [show (134599683/195312500 : ℝ) = (134599683/50000000000 : ℝ) * 2 ^ 8 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c4 : (-4332169941/6250000000 : ℝ) ≤ Real.log (1/2 : ℝ) ∧ Real.log (1/2 : ℝ) ≤
      (-541521227/781250000 : ℝ) := by
    rw [one_div, Real.log_inv]
    have h2 := Real.log_two_near_10
    rw [abs_le] at h2
    constructor <;> linarith only [h2.1, h2.2]
  have c5 : (-978065684777/1000000000000 : ℝ) ≤ Real.log (94009443791/250000000000 : ℝ) ∧ Real.log
      (94009443791/250000000000 : ℝ) ≤ (-978065664777/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(30990556209/125000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 30990556209/125000000000 = 94009443791/125000000000 by norm_num] at h
    have hs : Real.log (94009443791/250000000000 : ℝ) = Real.log
        (94009443791/125000000000 : ℝ) - 1 * Real.log 2 := by
      rw [show (94009443791/125000000000 : ℝ) = (94009443791/250000000000 : ℝ) * 2 ^ 1 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c6 : (-489032842387/500000000000 : ℝ) ≤ Real.log (75207555033/200000000000 : ℝ) ∧ Real.log
      (75207555033/200000000000 : ℝ) ≤ (-489032832387/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(24792444967/100000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 24792444967/100000000000 = 75207555033/100000000000 by norm_num] at h
    have hs : Real.log (75207555033/200000000000 : ℝ) = Real.log
        (75207555033/100000000000 : ℝ) - 1 * Real.log 2 := by
      rw [show (75207555033/100000000000 : ℝ) = (75207555033/200000000000 : ℝ) * 2 ^ 1 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c7 : (-2712368506313/500000000000 : ℝ) ≤ Real.log (881244967/200000000000 : ℝ) ∧ Real.log
      (881244967/200000000000 : ℝ) ≤ (-2712368496313/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-99994967/781250000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-99994967/781250000) = 881244967/781250000 by norm_num] at h
    have hs : Real.log (881244967/200000000000 : ℝ) = Real.log (881244967/781250000 : ℝ) - 8 *
        Real.log 2 := by
      rw [show (881244967/781250000 : ℝ) = (881244967/200000000000 : ℝ) * 2 ^ 8 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c8 : (-5424737012399/1000000000000 : ℝ) ≤ Real.log (1101556209/250000000000 : ℝ) ∧ Real.log
      (1101556209/250000000000 : ℝ) ≤ (-5424736992399/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-124993709/976562500 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-124993709/976562500) = 1101556209/976562500 by norm_num] at h
    have hs : Real.log (1101556209/250000000000 : ℝ) = Real.log (1101556209/976562500 : ℝ) - 8 *
        Real.log 2 := by
      rw [show (1101556209/976562500 : ℝ) = (1101556209/250000000000 : ℝ) * 2 ^ 8 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c9 : (-48089179901/100000000000 : ℝ) ≤ Real.log (15455795339/25000000000 : ℝ) ∧ Real.log
      (15455795339/25000000000 : ℝ) ≤ (-48089177901/100000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-2955795339/12500000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-2955795339/12500000000) = 15455795339/12500000000 by norm_num] at h
    have hs : Real.log (15455795339/25000000000 : ℝ) = Real.log (15455795339/12500000000 : ℝ) - 1 *
        Real.log 2 := by
      rw [show (15455795339/12500000000 : ℝ) = (15455795339/25000000000 : ℝ) * 2 ^ 1 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c10 : (-15027868719/31250000000 : ℝ) ≤ Real.log (618231813561/1000000000000 : ℝ) ∧ Real.log
      (618231813561/1000000000000 : ℝ) ≤ (-7513934047/15625000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-118231813561/500000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-118231813561/500000000000) = 618231813561/500000000000 by norm_num] at h
    have hs : Real.log (618231813561/1000000000000 : ℝ) = Real.log
        (618231813561/500000000000 : ℝ) - 1 * Real.log 2 := by
      rw [show (618231813561/500000000000 : ℝ) =
          (618231813561/1000000000000 : ℝ) * 2 ^ 1 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c11 : (-3313478513213/500000000000 : ℝ) ≤ Real.log (1324186439/1000000000000 : ℝ) ∧ Real.log
      (1324186439/1000000000000 : ℝ) ≤ (-3313478503213/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(628938561/1953125000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 628938561/1953125000 = 1324186439/1953125000 by norm_num] at h
    have hs : Real.log (1324186439/1000000000000 : ℝ) = Real.log (1324186439/1953125000 : ℝ) - 9 *
        Real.log 2 := by
      rw [show (1324186439/1953125000 : ℝ) = (1324186439/1000000000000 : ℝ) * 2 ^ 9 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c12 : (-6626957025671/1000000000000 : ℝ) ≤ Real.log (33104661/25000000000 : ℝ) ∧ Real.log
      (33104661/25000000000 : ℝ) ≤ (-6626957005671/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(15723464/48828125 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 15723464/48828125 = 33104661/48828125 by norm_num] at h
    have hs : Real.log (33104661/25000000000 : ℝ) = Real.log (33104661/48828125 : ℝ) - 9 *
        Real.log 2 := by
      rw [show (33104661/48828125 : ℝ) = (33104661/25000000000 : ℝ) * 2 ^ 9 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c13 : (-483208148641/500000000000 : ℝ) ≤ Real.log (95111/250000 : ℝ) ∧ Real.log
      (95111/250000 : ℝ) ≤ (-483208138641/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(29889/125000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 29889/125000 = 95111/125000 by norm_num] at h
    have hs : Real.log (95111/250000 : ℝ) = Real.log (95111/125000 : ℝ) - 1 * Real.log 2 := by
      rw [show (95111/125000 : ℝ) = (95111/250000 : ℝ) * 2 ^ 1 by norm_num, Real.log_mul
          (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c14 : (-239376098259/500000000000 : ℝ) ≤ Real.log (154889/250000 : ℝ) ∧ Real.log
      (154889/250000 : ℝ) ≤ (-239376088259/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-29889/125000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-29889/125000) = 154889/125000 by norm_num] at h
    have hs : Real.log (154889/250000 : ℝ) = Real.log (154889/125000 : ℝ) - 1 * Real.log 2 := by
      rw [show (154889/125000 : ℝ) = (154889/250000 : ℝ) * 2 ^ 1 by norm_num, Real.log_mul
          (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c15 : (-121006777403/100000000000 : ℝ) ≤ Real.log (59635414613/200000000000 : ℝ) ∧ Real.log
      (59635414613/200000000000 : ℝ) ≤ (-121006775403/100000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-9635414613/50000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-9635414613/50000000000) = 59635414613/50000000000 by norm_num] at h
    have hs : Real.log (59635414613/200000000000 : ℝ) = Real.log (59635414613/50000000000 : ℝ) - 2 *
        Real.log 2 := by
      rw [show (59635414613/50000000000 : ℝ) = (59635414613/200000000000 : ℝ) * 2 ^ 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c16 : (-1210067774027/1000000000000 : ℝ) ≤ Real.log (149088536533/500000000000 : ℝ) ∧
      Real.log (149088536533/500000000000 : ℝ) ≤ (-1210067754027/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-24088536533/125000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-24088536533/125000000000) = 149088536533/125000000000 by norm_num] at h
    have hs : Real.log (149088536533/500000000000 : ℝ) = Real.log
        (149088536533/125000000000 : ℝ) - 2 * Real.log 2 := by
      rw [show (149088536533/125000000000 : ℝ) =
          (149088536533/500000000000 : ℝ) * 2 ^ 2 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c17 : (-5135530904063/1000000000000 : ℝ) ≤ Real.log (2941963467/500000000000 : ℝ) ∧ Real.log
      (2941963467/500000000000 : ℝ) ≤ (-5135530884063/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(964286533/3906250000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 964286533/3906250000 = 2941963467/3906250000 by norm_num] at h
    have hs : Real.log (2941963467/500000000000 : ℝ) = Real.log (2941963467/3906250000 : ℝ) - 7 *
        Real.log 2 := by
      rw [show (2941963467/3906250000 : ℝ) = (2941963467/500000000000 : ℝ) * 2 ^ 7 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c18 : (-5135530903893/1000000000000 : ℝ) ≤ Real.log (1176785387/200000000000 : ℝ) ∧ Real.log
      (1176785387/200000000000 : ℝ) ≤ (-5135530883893/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(385714613/1562500000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 385714613/1562500000 = 1176785387/1562500000 by norm_num] at h
    have hs : Real.log (1176785387/200000000000 : ℝ) = Real.log (1176785387/1562500000 : ℝ) - 7 *
        Real.log 2 := by
      rw [show (1176785387/1562500000 : ℝ) = (1176785387/200000000000 : ℝ) * 2 ^ 7 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c19 : (-90820032843/250000000000 : ℝ) ≤ Real.log (695391612161/1000000000000 : ℝ) ∧ Real.log
      (695391612161/1000000000000 : ℝ) ≤ (-90820027843/250000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(304608387839/1000000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 304608387839/1000000000000 = 695391612161/1000000000000 by norm_num] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [abs_le] at h
    constructor <;> norm_num at h ⊢ <;> linarith only [h.1, h.2]
  have c20 : (-363280131371/1000000000000 : ℝ) ≤ Real.log (347695806081/500000000000 : ℝ) ∧ Real.log
      (347695806081/500000000000 : ℝ) ≤ (-363280111371/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(152304193919/500000000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 152304193919/500000000000 = 347695806081/500000000000 by norm_num] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [abs_le] at h
    constructor <;> norm_num at h ⊢ <;> linarith only [h.1, h.2]
  have c21 : (-7510352989361/1000000000000 : ℝ) ≤ Real.log (273693919/500000000000 : ℝ) ∧ Real.log
      (273693919/500000000000 : ℝ) ≤ (-7510352969361/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-29553294/244140625 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-29553294/244140625) = 273693919/244140625 by norm_num] at h
    have hs : Real.log (273693919/500000000000 : ℝ) = Real.log (273693919/244140625 : ℝ) - 11 *
        Real.log 2 := by
      rw [show (273693919/244140625 : ℝ) = (273693919/500000000000 : ℝ) * 2 ^ 11 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c22 : (-3755176493767/500000000000 : ℝ) ≤ Real.log (547387839/1000000000000 : ℝ) ∧ Real.log
      (547387839/1000000000000 : ℝ) ≤ (-3755176483767/500000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-59106589/488281250 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-59106589/488281250) = 547387839/488281250 by norm_num] at h
    have hs : Real.log (547387839/1000000000000 : ℝ) = Real.log (547387839/488281250 : ℝ) - 11 *
        Real.log 2 := by
      rw [show (547387839/488281250 : ℝ) = (547387839/1000000000000 : ℝ) * 2 ^ 11 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c23 : (-119052694981/100000000000 : ℝ) ≤ Real.log (304061/1000000 : ℝ) ∧ Real.log
      (304061/1000000 : ℝ) ≤ (-119052692981/100000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(-54061/250000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-54061/250000) = 304061/250000 by norm_num] at h
    have hs : Real.log (304061/1000000 : ℝ) = Real.log (304061/250000 : ℝ) - 2 * Real.log 2 := by
      rw [show (304061/250000 : ℝ) = (304061/1000000 : ℝ) * 2 ^ 2 by norm_num, Real.log_mul
          (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c24 : (-362493276167/1000000000000 : ℝ) ≤ Real.log (695939/1000000 : ℝ) ∧ Real.log
      (695939/1000000 : ℝ) ≤ (-362493256167/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(304061/1000000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 304061/1000000 = 695939/1000000 by norm_num] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [abs_le] at h
    constructor <;> norm_num at h ⊢ <;> linarith only [h.1, h.2]
  have c25 : (-1301585643193/1000000000000 : ℝ) ≤ Real.log (2721/10000 : ℝ) ∧ Real.log
      (2721/10000 : ℝ) ≤ (-1301585623193/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |(-221/2500 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-221/2500) = 2721/2500 by norm_num] at h
    have hs : Real.log (2721/10000 : ℝ) = Real.log (2721/2500 : ℝ) - 2 * Real.log 2 := by
      rw [show (2721/2500 : ℝ) = (2721/10000 : ℝ) * 2 ^ 2 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c26 : (-5035953112081/1000000000000 : ℝ) ≤ Real.log (13/2000 : ℝ) ∧ Real.log (13/2000 : ℝ) ≤
      (-5035953092081/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |(21/125 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 21/125 = 104/125 by norm_num] at h
    have hs : Real.log (13/2000 : ℝ) = Real.log (104/125 : ℝ) - 7 * Real.log 2 := by
      rw [show (104/125 : ℝ) = (13/2000 : ℝ) * 2 ^ 7 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c27 : (-326977465059/1000000000000 : ℝ) ≤ Real.log (7211/10000 : ℝ) ∧ Real.log
      (7211/10000 : ℝ) ≤ (-326977445059/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le
        (show |(2789/10000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 2789/10000 = 7211/10000 by norm_num] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [abs_le] at h
    constructor <;> norm_num at h ⊢ <;> linarith only [h.1, h.2]
  have c28 : (-2027932023327/250000000000 : ℝ) ≤ Real.log (3/10000 : ℝ) ∧ Real.log (3/10000 : ℝ) ≤
      (-2027932018327/250000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |(-143/625 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-143/625) = 768/625 by norm_num] at h
    have hs : Real.log (3/10000 : ℝ) = Real.log (768/625 : ℝ) - 12 * Real.log 2 := by
      rw [show (768/625 : ℝ) = (3/10000 : ℝ) * 2 ^ 12 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c29 : (-319494556909/250000000000 : ℝ) ≤ Real.log (1393/5000 : ℝ) ∧ Real.log (1393/5000 : ℝ)
      ≤ (-319494551909/250000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |(-143/1250 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - (-143/1250) = 1393/1250 by norm_num] at h
    have hs : Real.log (1393/5000 : ℝ) = Real.log (1393/1250 : ℝ) - 2 * Real.log 2 := by
      rw [show (1393/1250 : ℝ) = (1393/5000 : ℝ) * 2 ^ 2 by norm_num, Real.log_mul (by norm_num)
          (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h2 := Real.log_two_near_10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [hs]; rw [abs_le] at h h2
    constructor <;> norm_num at h h2 ⊢ <;> linarith only [h.1, h.2, h2.1, h2.2]
  have c30 : (-326561520513/1000000000000 : ℝ) ≤ Real.log (3607/5000 : ℝ) ∧ Real.log (3607/5000 : ℝ)
      ≤ (-326561500513/1000000000000 : ℝ) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |(1393/5000 : ℝ)| < 1 by norm_num [abs_lt]) 22
    rw [show (1 : ℝ) - 1393/5000 = 3607/5000 by norm_num] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    rw [abs_le] at h
    constructor <;> norm_num at h ⊢ <;> linarith only [h.1, h.2]
  have V0 : (33497152729/1000000000000 : ℝ) ≤ f1 (0) (-1233/1250) (-1107/2500) (187/2500)
      (-163/2500) (569/1250) * Real.log 2 ∧
      f1 (0) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) * Real.log 2 ≤
          (33497192747/1000000000000 : ℝ) := by
    have hr1 : r1 (0) (-1233/1250) (187/2500) (-163/2500) (569/1250) = (48929/50000 : ℝ) := by
      rw [r1, hw]; norm_num
    have hr2 : r2 (0) (-1233/1250) (187/2500) (-163/2500) (569/1250) = (48929/50000 : ℝ) := by
      rw [r2, hw]; norm_num
    have s1l : (989232025361087/1000000000000000 : ℝ) ≤ √(r1 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250)) := by
      rw [hr1]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s1h : √(r1 (0) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (15456750396267/15625000000000 : ℝ) := by
      rw [hr1]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have s2l : (989232025361087/1000000000000000 : ℝ) ≤ √(r2 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250)) := by
      rw [hr2]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s2h : √(r2 (0) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (15456750396267/15625000000000 : ℝ) := by
      rw [hr2]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have b0 := nmlB ((1 + -1107/2500 * 0 + √(r1 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (24865400317/50000000000 : ℝ) (497308006341/1000000000000 : ℝ)
        (-698545723773/1000000000000 : ℝ) (-698545703771/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1l]) (by linarith only [s1h]) (by norm_num) c0.1 c1.2
    have b1 := nmlB ((1 + -1107/2500 * 0 - √(r1 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (2691993659/1000000000000 : ℝ) (134599683/50000000000 : ℝ)
        (-59174732327/10000000000 : ℝ) (-5917473212329/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1h]) (by linarith only [s1l]) (by norm_num) c2.1 c3.2
    have b2 := nmlB ((1 - -1107/2500 * 0 + √(r2 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (24865400317/50000000000 : ℝ) (497308006341/1000000000000 : ℝ)
        (-698545723773/1000000000000 : ℝ) (-698545703771/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s2l]) (by linarith only [s2h]) (by norm_num) c0.1 c1.2
    have b3 := nmlB ((1 - -1107/2500 * 0 - √(r2 (0) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (2691993659/1000000000000 : ℝ) (134599683/50000000000 : ℝ)
        (-59174732327/10000000000 : ℝ) (-5917473212329/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s2h]) (by linarith only [s2l]) (by norm_num) c2.1 c3.2
    have b4 := nmlB ((1 + -1107/2500 * 0) / 2) (1/2 : ℝ) (1/2 : ℝ) (-4332169941/6250000000 : ℝ)
        (-541521227/781250000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c4.1 c4.2
    have b5 := nmlB ((1 - -1107/2500 * 0) / 2) (1/2 : ℝ) (1/2 : ℝ) (-4332169941/6250000000 : ℝ)
        (-541521227/781250000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c4.1 c4.2
    rw [e]
    constructor <;> linarith only [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1,
        b5.2]
  have V1 : (33489092997/1000000000000 : ℝ) ≤ f1 (27/50) (-1233/1250) (-1107/2500) (187/2500)
      (-163/2500) (569/1250) * Real.log 2 ∧
      f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) * Real.log 2 ≤
          (6697826603/200000000000 : ℝ) := by
    have hr1 : r1 (27/50) (-1233/1250) (187/2500) (-163/2500) (569/1250) =
        (345275023/625000000 : ℝ) := by
      rw [r1, hw]; norm_num
    have hr2 : r2 (27/50) (-1233/1250) (187/2500) (-163/2500) (569/1250) =
        (951437551/625000000 : ℝ) := by
      rw [r2, hw]; norm_num
    have s1l : (185815775164543/250000000000000 : ℝ) ≤ √(r1 (27/50) (-1233/1250) (187/2500)
        (-163/2500) (569/1250)) := by
      rw [hr1]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s1h : √(r1 (27/50) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (743263100658173/1000000000000000 : ℝ) := by
      rw [hr1]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have s2l : (616907627120949/500000000000000 : ℝ) ≤ √(r2 (27/50) (-1233/1250) (187/2500)
        (-163/2500) (569/1250)) := by
      rw [hr2]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s2h : √(r2 (27/50) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (1233815254241899/1000000000000000 : ℝ) := by
      rw [hr2]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have b0 := nmlB ((1 + -1107/2500 * (27/50) + √(r1 (27/50) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (94009443791/250000000000 : ℝ) (75207555033/200000000000 : ℝ)
        (-978065684777/1000000000000 : ℝ) (-489032832387/500000000000 : ℝ) (by norm_num)
      (by linarith only [s1l]) (by linarith only [s1h]) (by norm_num) c5.1 c6.2
    have b1 := nmlB ((1 + -1107/2500 * (27/50) - √(r1 (27/50) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (881244967/200000000000 : ℝ) (1101556209/250000000000 : ℝ)
        (-2712368506313/500000000000 : ℝ) (-5424736992399/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1h]) (by linarith only [s1l]) (by norm_num) c7.1 c8.2
    have b2 := nmlB ((1 - -1107/2500 * (27/50) + √(r2 (27/50) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (15455795339/25000000000 : ℝ) (618231813561/1000000000000 : ℝ)
        (-48089179901/100000000000 : ℝ) (-7513934047/15625000000 : ℝ) (by norm_num)
      (by linarith only [s2l]) (by linarith only [s2h]) (by norm_num) c9.1 c10.2
    have b3 := nmlB ((1 - -1107/2500 * (27/50) - √(r2 (27/50) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (1324186439/1000000000000 : ℝ) (33104661/25000000000 : ℝ)
        (-3313478513213/500000000000 : ℝ) (-6626957005671/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s2h]) (by linarith only [s2l]) (by norm_num) c11.1 c12.2
    have b4 := nmlB ((1 + -1107/2500 * (27/50)) / 2) (95111/250000 : ℝ) (95111/250000 : ℝ)
        (-483208148641/500000000000 : ℝ) (-483208138641/500000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c13.1 c13.2
    have b5 := nmlB ((1 - -1107/2500 * (27/50)) / 2) (154889/250000 : ℝ) (154889/250000 : ℝ)
        (-239376098259/500000000000 : ℝ) (-239376088259/500000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c14.1 c14.2
    rw [e]
    constructor <;> linarith only [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1,
        b5.2]
  have V2 : (33498544771/1000000000000 : ℝ) ≤ f1 (177/200) (-1233/1250) (-1107/2500) (187/2500)
      (-163/2500) (569/1250) * Real.log 2 ∧
      f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) * Real.log 2 ≤
          (3349858479/100000000000 : ℝ) := by
    have hr1 : r1 (177/200) (-1233/1250) (187/2500) (-163/2500) (569/1250) =
        (3417411331/10000000000 : ℝ) := by
      rw [r1, hw]; norm_num
    have hr2 : r2 (177/200) (-1233/1250) (187/2500) (-163/2500) (569/1250) =
        (19312339843/10000000000 : ℝ) := by
      rw [r2, hw]; norm_num
    have s1l : (584586292261459/1000000000000000 : ℝ) ≤ √(r1 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250)) := by
      rw [hr1]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s1h : √(r1 (177/200) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (29229314613073/50000000000000 : ℝ) := by
      rw [hr1]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have s2l : (694844224322977/500000000000000 : ℝ) ≤ √(r2 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250)) := by
      rw [hr2]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s2h : √(r2 (177/200) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤
        (277937689729191/200000000000000 : ℝ) := by
      rw [hr2]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have b0 := nmlB ((1 + -1107/2500 * (177/200) + √(r1 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250))) / 4) (59635414613/200000000000 : ℝ) (149088536533/500000000000 : ℝ)
        (-121006777403/100000000000 : ℝ) (-1210067754027/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1l]) (by linarith only [s1h]) (by norm_num) c15.1 c16.2
    have b1 := nmlB ((1 + -1107/2500 * (177/200) - √(r1 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250))) / 4) (2941963467/500000000000 : ℝ) (1176785387/200000000000 : ℝ)
        (-5135530904063/1000000000000 : ℝ) (-5135530883893/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1h]) (by linarith only [s1l]) (by norm_num) c17.1 c18.2
    have b2 := nmlB ((1 - -1107/2500 * (177/200) + √(r2 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250))) / 4) (695391612161/1000000000000 : ℝ)
        (347695806081/500000000000 : ℝ) (-90820032843/250000000000 : ℝ)
        (-363280111371/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s2l]) (by linarith only [s2h]) (by norm_num) c19.1 c20.2
    have b3 := nmlB ((1 - -1107/2500 * (177/200) - √(r2 (177/200) (-1233/1250) (187/2500)
        (-163/2500) (569/1250))) / 4) (273693919/500000000000 : ℝ) (547387839/1000000000000 : ℝ)
        (-7510352989361/1000000000000 : ℝ) (-3755176483767/500000000000 : ℝ) (by norm_num)
      (by linarith only [s2h]) (by linarith only [s2l]) (by norm_num) c21.1 c22.2
    have b4 := nmlB ((1 + -1107/2500 * (177/200)) / 2) (304061/1000000 : ℝ) (304061/1000000 : ℝ)
        (-119052694981/100000000000 : ℝ) (-119052692981/100000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c23.1 c23.2
    have b5 := nmlB ((1 - -1107/2500 * (177/200)) / 2) (695939/1000000 : ℝ) (695939/1000000 : ℝ)
        (-362493276167/1000000000000 : ℝ) (-362493256167/1000000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c24.1 c24.2
    rw [e]
    constructor <;> linarith only [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1,
        b5.2]
  have V3 : (6697176421/200000000000 : ℝ) ≤ f1 (1) (-1233/1250) (-1107/2500) (187/2500) (-163/2500)
      (569/1250) * Real.log 2 ∧
      f1 (1) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) * Real.log 2 ≤
          (16742961053/500000000000 : ℝ) := by
    have hr1 : r1 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250) = (110224/390625 : ℝ) := by
      rw [r1, hw]; norm_num
    have hr2 : r2 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250) = (811801/390625 : ℝ) := by
      rw [r2, hw]; norm_num
    have s1l : (332/625 : ℝ) ≤ √(r1 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250)) := by
      rw [hr1]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s1h : √(r1 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤ (332/625 : ℝ) := by
      rw [hr1]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have s2l : (901/625 : ℝ) ≤ √(r2 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250)) := by
      rw [hr2]; exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have s2h : √(r2 (1) (-1233/1250) (187/2500) (-163/2500) (569/1250)) ≤ (901/625 : ℝ) := by
      rw [hr2]; exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    have b0 := nmlB ((1 + -1107/2500 * 1 + √(r1 (1) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (2721/10000 : ℝ) (2721/10000 : ℝ) (-1301585643193/1000000000000 : ℝ)
        (-1301585623193/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1l]) (by linarith only [s1h]) (by norm_num) c25.1 c25.2
    have b1 := nmlB ((1 + -1107/2500 * 1 - √(r1 (1) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (13/2000 : ℝ) (13/2000 : ℝ) (-5035953112081/1000000000000 : ℝ)
        (-5035953092081/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s1h]) (by linarith only [s1l]) (by norm_num) c26.1 c26.2
    have b2 := nmlB ((1 - -1107/2500 * 1 + √(r2 (1) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (7211/10000 : ℝ) (7211/10000 : ℝ) (-326977465059/1000000000000 : ℝ)
        (-326977445059/1000000000000 : ℝ) (by norm_num)
      (by linarith only [s2l]) (by linarith only [s2h]) (by norm_num) c27.1 c27.2
    have b3 := nmlB ((1 - -1107/2500 * 1 - √(r2 (1) (-1233/1250) (187/2500) (-163/2500)
        (569/1250))) / 4) (3/10000 : ℝ) (3/10000 : ℝ) (-2027932023327/250000000000 : ℝ)
        (-2027932018327/250000000000 : ℝ) (by norm_num)
      (by linarith only [s2h]) (by linarith only [s2l]) (by norm_num) c28.1 c28.2
    have b4 := nmlB ((1 + -1107/2500 * 1) / 2) (1393/5000 : ℝ) (1393/5000 : ℝ)
        (-319494556909/250000000000 : ℝ) (-319494551909/250000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c29.1 c29.2
    have b5 := nmlB ((1 - -1107/2500 * 1) / 2) (3607/5000 : ℝ) (3607/5000 : ℝ)
        (-326561520513/1000000000000 : ℝ) (-326561500513/1000000000000 : ℝ) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) c30.1 c30.2
    rw [e]
    constructor <;> linarith only [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1,
        b5.2]
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have f01 : f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) <
      f1 0 (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.1 hc) hlog.le
    linarith only [this, V0.1, V1.2]
  have f21 : f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) <
      f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.1 hc) hlog.le
    linarith only [this, V2.1, V1.2]
  have f23 : f1 1 (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) <
      f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_right (not_lt.1 hc) hlog.le
    linarith only [this, V2.1, V3.2]
  obtain ⟨xm, hxm, hmode⟩ :=
    h (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) hadm
  rcases hmode with ⟨hmono, hanti⟩ | ⟨hanti, hmono⟩
  · by_cases hb : (27/50 : ℝ) ≤ xm
    · have : f1 0 (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) ≤
          f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) :=
        hmono (show (0 : ℝ) ∈ Set.Icc 0 xm from ⟨le_refl 0, hxm.1⟩)
          (show (27/50 : ℝ) ∈ Set.Icc 0 xm from ⟨by norm_num, hb⟩) (by norm_num)
      linarith
    · have : f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) ≤
          f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) :=
        hanti (show (27/50 : ℝ) ∈ Set.Icc xm 1 from ⟨by linarith, by norm_num⟩)
          (show (177/200 : ℝ) ∈ Set.Icc xm 1 from ⟨by linarith, by norm_num⟩) (by norm_num)
      linarith
  · by_cases hc : (177/200 : ℝ) ≤ xm
    · have : f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) ≤
          f1 (27/50) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) :=
        hanti (show (27/50 : ℝ) ∈ Set.Icc 0 xm from ⟨by norm_num, by linarith⟩)
          (show (177/200 : ℝ) ∈ Set.Icc 0 xm from ⟨by norm_num, hc⟩) (by norm_num)
      linarith
    · have : f1 (177/200) (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) ≤
          f1 1 (-1233/1250) (-1107/2500) (187/2500) (-163/2500) (569/1250) :=
        hmono (show (177/200 : ℝ) ∈ Set.Icc xm 1 from ⟨by linarith, by norm_num⟩)
          (show (1 : ℝ) ∈ Set.Icc xm 1 from ⟨hxm.2, le_refl 1⟩) (by norm_num)
      linarith

end D5.S3.Quantum.Information.XStateWeakUnimodalityRefutation
