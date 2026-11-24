/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactCenteredMomentCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Soundness of coefficientwise certificates for the centered grid moments. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

/-! # Integer certificates for centered grid moments -/

namespace RefinedBMV.PositiveCenter.CenteredMomentCertificate

open scoped BigOperators
open SmallCorner (momentHorner)
open private integerCoeffAdd integerCoeffMul integerCoeffScale integerCoeffSum
  scaledIntegers scaledIntegers_add scaledIntegers_mul scaledIntegers_scale
  coeffScale_scaledIntegers horner_add horner_mul horner_scale from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
open private compact_centered_moment_recurrence gridAverage gridAverage_const_mul
  gridAverage_pow_eq gridAverage_weighted_pow_eq from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

/-- Real evaluation of an ascending list of integer coefficients. -/
noncomputable def eval (h : ℝ) (xs : List ℤ) : ℝ :=
  momentHorner h (scaledIntegers 1 xs)

private theorem eval_nil (h : ℝ) : eval h [] = 0 := rfl

private theorem eval_cons (h : ℝ) (x : ℤ) (xs : List ℤ) :
    eval h (x :: xs) = (x : ℝ) + h * eval h xs := by
  simp [eval, scaledIntegers, momentHorner]

private theorem eval_add (h : ℝ) (xs ys : List ℤ) :
    eval h (integerCoeffAdd xs ys) = eval h xs + eval h ys := by
  simp only [eval, scaledIntegers_add, horner_add]

private theorem eval_mul (h : ℝ) (xs ys : List ℤ) :
    eval h (integerCoeffMul xs ys) = eval h xs * eval h ys := by
  simpa only [eval, mul_one, horner_mul] using
    congrArg (momentHorner h) (scaledIntegers_mul 1 1 xs ys)

private theorem eval_scale (h : ℝ) (c : ℤ) (xs : List ℤ) :
    eval h (integerCoeffScale c xs) = (c : ℝ) * eval h xs := by
  simp only [eval, scaledIntegers_scale, mul_one, horner_scale, Rat.cast_intCast]

private theorem eval_sum (h : ℝ) (f : ℕ → List ℤ) (n : ℕ) :
    eval h (integerCoeffSum f n) = ∑ j ∈ Finset.range n, eval h (f j) := by
  induction n with
  | zero => simp [integerCoeffSum, eval_nil]
  | succ n ih => rw [integerCoeffSum, eval_add, ih, Finset.sum_range_succ]

private theorem eval_shift (h : ℝ) (xs : List ℤ) (k : ℕ) :
    eval h (List.replicate k 0 ++ xs) = h ^ k * eval h xs := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, eval_cons, Int.cast_zero, zero_add,
      ih, pow_succ', mul_assoc]

private def affinePow (a b : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => integerCoeffMul [a, b] (affinePow a b n)

private theorem affinePow_eval (h : ℝ) (a b : ℤ) (n : ℕ) :
    eval h (affinePow a b n) = ((a : ℝ) + (b : ℝ) * h) ^ n := by
  induction n with
  | zero => simp [affinePow, eval_cons, eval_nil]
  | succ n ih =>
    rw [affinePow, eval_mul, ih, pow_succ']
    simp only [eval_cons, eval_nil, mul_zero, add_zero]
    rw [mul_comm h (b : ℝ)]

private def lowerTerm (rows : ℕ → List ℤ) (m j : ℕ) : List ℤ :=
  List.replicate (j + 1) 0 ++
    integerCoeffScale
      ((Nat.fast_choose (m + 2) (j + 3) : ℤ) * (-1) ^ (j + 1) * (2 ^ (j + 2) - 1))
      (rows (m - (j + 1)))

/-- The left side of the cross-multiplied moment recurrence, in ascending coefficients. -/
def rowLhs (rows : ℕ → List ℤ) (m : ℕ) : List ℤ :=
  integerCoeffMul [0, 9, 9, 2]
    (integerCoeffAdd (integerCoeffScale (Nat.fast_choose (m + 2) 2 : ℤ) (rows m))
      (integerCoeffSum (lowerTerm rows m) m))

/-- The right side of the recurrence, scaled by the table's common denominator. -/
def rowRhs (D : ℤ) (m : ℕ) : List ℤ :=
  integerCoeffScale D
    (integerCoeffAdd
      (integerCoeffAdd [3, 1] (integerCoeffMul [-3, -2] (affinePow 1 (-1) (m + 2))))
      (0 :: affinePow (-2) (-2) (m + 2)))

private def recurrenceWeight (h : ℝ) (m j : ℕ) : ℝ :=
  ((m + 2).choose (j + 3) : ℝ) * (-h) ^ (j + 1) * ((2 : ℝ) ^ (j + 2) - 1)

private def spacingFactor (h : ℝ) : ℝ := h * (3 + h) * (3 + 2 * h)

private def recurrenceRhs (h : ℝ) (m : ℕ) : ℝ :=
  (3 + h) - (3 + 2 * h) * (1 - h) ^ (m + 2) + h * (-2 - 2 * h) ^ (m + 2)

private theorem fast_choose_eq (n k : ℕ) : Nat.fast_choose n k = n.choose k :=
  congrFun (congrFun Nat.choose_eq_fast_choose.symm n) k

private theorem lowerTerm_eval (h : ℝ) (rows : ℕ → List ℤ) (m j : ℕ) :
    eval h (lowerTerm rows m j) =
      recurrenceWeight h m j * eval h (rows (m - (j + 1))) := by
  rw [lowerTerm, eval_shift, eval_scale, recurrenceWeight, neg_pow h (j + 1)]
  simp only [fast_choose_eq, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_natCast,
    Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  ring

private theorem rowLhs_eval (h : ℝ) (rows : ℕ → List ℤ) (m : ℕ) :
    eval h (rowLhs rows m) = spacingFactor h *
      (((m + 2).choose 2 : ℝ) * eval h (rows m) +
        ∑ j ∈ Finset.range m, recurrenceWeight h m j * eval h (rows (m - (j + 1)))) := by
  have hfactor : eval h [0, 9, 9, 2] = spacingFactor h := by
    norm_num [eval_cons, eval_nil, spacingFactor]
    ring
  simp only [rowLhs, eval_mul, hfactor, eval_add, eval_scale, fast_choose_eq,
    Int.cast_natCast, eval_sum, lowerTerm_eval]

private theorem rowRhs_eval (h : ℝ) (D : ℤ) (m : ℕ) :
    eval h (rowRhs D m) = (D : ℝ) * recurrenceRhs h m := by
  have h₁ : ((1 : ℝ) + (-1) * h) = 1 - h := by ring
  have h₂ : ((-2 : ℝ) + (-2) * h) = -2 - 2 * h := by ring
  simp only [rowRhs, eval_scale, eval_add, eval_mul, eval_cons, eval_nil, affinePow_eval,
    Int.cast_neg, Int.cast_zero, Int.cast_one, Int.cast_ofNat, mul_zero, add_zero, zero_add]
  rw [h₁, h₂]
  unfold recurrenceRhs
  ring

/-- Integer row identities determine the moments of the negated grid point at spacing 3/p. -/
theorem rows_eval {rows : ℕ → List ℤ} {D : ℤ} {K : ℕ}
    (hrows : ∀ m ≤ K, rowLhs rows m = rowRhs D m)
    {p : ℕ} (hp : 0 < p) (m : ℕ) (hm : m ≤ K) :
    let h := 3 / (p : ℝ)
    eval h (rows m) = (D : ℝ) * ((-1 : ℝ) ^ m * compactCenteredMomentPolynomial h m) := by
  let h : ℝ := 3 / (p : ℝ)
  let M (n : ℕ) := (-1 : ℝ) ^ n * compactCenteredMomentPolynomial h n
  let V (n : ℕ) := eval h (rows n)
  change V m = (D : ℝ) * M m
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hfactor : spacingFactor h ≠ 0 := by
    apply ne_of_gt
    unfold spacingFactor
    positivity
  induction m using Nat.strong_induction_on with
  | h m ih =>
    let C : ℝ := ((m + 2).choose 2 : ℝ)
    let S : ℝ := ∑ j ∈ Finset.range m, recurrenceWeight h m j * M (m - (j + 1))
    have hchoose : C ≠ 0 := by
      dsimp [C]
      exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ m + 2)).ne'
    have htail :
        (∑ j ∈ Finset.range m, recurrenceWeight h m j * V (m - (j + 1))) = (D : ℝ) * S := by
      unfold S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjm : j < m := Finset.mem_range.mp hj
      have hprev : m - (j + 1) < m := by omega
      rw [ih _ hprev (hprev.le.trans hm)]
      ring
    have hrow := congrArg (eval h) (hrows m hm)
    rw [rowLhs_eval, rowRhs_eval] at hrow
    change spacingFactor h *
      (C * V m + ∑ j ∈ Finset.range m, recurrenceWeight h m j * V (m - (j + 1))) =
        (D : ℝ) * recurrenceRhs h m at hrow
    rw [htail] at hrow
    have hrec : spacingFactor h * (C * M m + S) = recurrenceRhs h m :=
      compact_centered_moment_recurrence hp m
    have heq : spacingFactor h * (C * V m + (D : ℝ) * S) =
        spacingFactor h * (C * ((D : ℝ) * M m) + (D : ℝ) * S) := by
      calc
        _ = (D : ℝ) * recurrenceRhs h m := hrow
        _ = _ := by rw [← hrec]; ring
    exact mul_left_cancel₀ hchoose (add_right_cancel (mul_left_cancel₀ hfactor heq))

private def tiltedRow (rows : ℕ → List ℤ) : ℕ → ℕ → List ℤ
  | 0, n => rows n
  | j + 1, n => integerCoeffAdd
      (integerCoeffMul [2, 1] (tiltedRow rows j n)) (tiltedRow rows j (n + 1))

private theorem tiltedRow_eval {rows : ℕ → List ℤ} {D : ℤ} {K : ℕ}
    (hrows : ∀ m ≤ K, rowLhs rows m = rowRhs D m)
    {p : ℕ} (hp : 0 < p) (j n : ℕ) (hjn : j + n ≤ K) :
    let h := 3 / (p : ℝ)
    eval h (tiltedRow rows j n) =
      (D : ℝ) * gridAverage p (fun x ↦ (2 + h - x) ^ j * (-x) ^ n) := by
  intro h
  induction j generalizing n with
  | zero =>
    simp only [tiltedRow, pow_zero, one_mul]
    rw [show (fun x : ℝ ↦ (-x) ^ n) = (fun x ↦ (-1 : ℝ) ^ n * x ^ n) from
      funext fun x ↦ neg_pow x n, gridAverage_const_mul, gridAverage_pow_eq hp]
    exact rows_eval hrows hp n (by omega)
  | succ j ih =>
    rw [tiltedRow, eval_add, eval_mul, ih n (by omega), ih (n + 1) (by omega)]
    have haffine : eval h [2, 1] = 2 + h := by norm_num [eval_cons, eval_nil]
    have hpoint (x : ℝ) : (2 + h - x) ^ (j + 1) * (-x) ^ n =
        (2 + h) * ((2 + h - x) ^ j * (-x) ^ n) +
          (2 + h - x) ^ j * (-x) ^ (n + 1) := by
      rw [pow_succ (2 + h - x), pow_succ (-x)]
      ring
    have havg (f g : ℝ → ℝ) :
        gridAverage p (fun x ↦ f x + g x) = gridAverage p f + gridAverage p g := by
      simp only [gridAverage, mul_add, Finset.sum_add_distrib, add_div]
    simp_rw [haffine, hpoint, havg, gridAverage_const_mul]
    ring

/-- Convert a certified tilted row to the Taylor coefficient for powers of the grid point. -/
def tiltedCoefficients (rows : ℕ → List ℤ) (D : ℤ) (j n : ℕ) : List ℚ :=
  scaledIntegers ((-1 : ℚ) ^ n / ((D : ℚ) * (n.factorial : ℚ))) (tiltedRow rows j n)

/-- The integer affine-factor recurrence supplies the existing real Taylor coefficient. -/
theorem tiltedCoefficients_eval {rows : ℕ → List ℤ} {D : ℤ} {K : ℕ}
    (hrows : ∀ m ≤ K, rowLhs rows m = rowRhs D m) (hD : D ≠ 0)
    {p : ℕ} (hp : 0 < p) (j n : ℕ) (hjn : j + n ≤ K) :
    let h := 3 / (p : ℝ)
    momentHorner h (tiltedCoefficients rows D j n) =
      compactPositiveMomentCoefficient h j n / (n.factorial : ℝ) := by
  intro h
  have hs (d : ℚ) (xs : List ℤ) :
      momentHorner h (scaledIntegers d xs) = (d : ℝ) * eval h xs := by
    simpa only [mul_one, horner_scale, eval] using
      (congrArg (momentHorner h) (coeffScale_scaledIntegers d 1 xs)).symm
  have hpoint (x : ℝ) : (2 + h - x) ^ j * (-x) ^ n =
      (-1 : ℝ) ^ n * ((2 + h - x) ^ j * x ^ n) := by
    rw [neg_pow x n]
    ring
  have hmoment : gridAverage p (fun x ↦ (2 + h - x) ^ j * (-x) ^ n) =
      (-1 : ℝ) ^ n * compactPositiveMomentCoefficient h j n := by
    calc
      _ = gridAverage p (fun x ↦ (-1 : ℝ) ^ n * ((2 + h - x) ^ j * x ^ n)) :=
        congrArg (gridAverage p) (funext hpoint)
      _ = _ := by
        rw [gridAverage_const_mul]
        change (-1 : ℝ) ^ n *
          gridAverage p (fun x ↦ (2 + 3 / (p : ℝ) - x) ^ j * x ^ n) = _
        rw [gridAverage_weighted_pow_eq hp]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [tiltedCoefficients, hs, tiltedRow_eval hrows hp j n hjn, hmoment]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one]
  calc
    _ = (D : ℝ) * (((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * compactPositiveMomentCoefficient h j n) /
        ((D : ℝ) * (n.factorial : ℝ)) := by ring
    _ = _ := by
      rw [hsign, one_mul]
      field_simp [hDR, hfac] <;> ring

end RefinedBMV.PositiveCenter.CenteredMomentCertificate
