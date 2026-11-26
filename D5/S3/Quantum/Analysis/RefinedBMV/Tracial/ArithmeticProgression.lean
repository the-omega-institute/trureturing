/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/ArithmeticProgression
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/Tracial/ArithmeticProgression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The continuum four-cycle matching on four equally spaced logarithmic knots. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.ExponentialChain
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.SimplexExponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Strict continuum matching for four equally spaced logarithmic knots. -/

namespace RefinedBMV.Tracial
namespace ArithmeticProgression

open Set

/-! The coefficients of a polynomial are listed in ascending order. The
exponential-chain argument also permits repeated frequencies with polynomial factors. -/

private abbrev Table := List (ℤ × List ℤ)

private noncomputable def polyValue : ℕ → List ℤ → ℝ → ℝ
  | _, [], _ => 0
  | k, c :: cs, t => (c : ℝ) * t ^ k + polyValue (k + 1) cs t

private def scaleDerivative (k : ℕ) : List ℤ → List ℤ
  | [] => []
  | c :: cs => (c * (k + 1 : ℕ)) :: scaleDerivative (k + 1) cs

private theorem hasDerivAt_polyValue_succ (cs : List ℤ) (k : ℕ) (t : ℝ) :
    HasDerivAt (polyValue (k + 1) cs) (polyValue k (scaleDerivative k cs) t) t := by
  induction cs generalizing k with
  | nil => exact hasDerivAt_const t 0
  | cons c cs ih =>
    simpa only [Pi.add_def, polyValue, scaleDerivative, Int.cast_mul, Int.cast_natCast,
      Nat.add_sub_cancel, mul_assoc] using
      (((hasDerivAt_pow (k + 1) t).const_mul (c : ℝ)).add (ih (k + 1)))

private theorem hasDerivAt_polyValue (cs : List ℤ) (t : ℝ) :
    HasDerivAt (polyValue 0 cs) (polyValue 0 (scaleDerivative 0 cs.tail) t) t := by
  cases cs with
  | nil => exact hasDerivAt_const t 0
  | cons c cs =>
    simpa only [polyValue, pow_zero, mul_one, List.tail_cons] using
      (hasDerivAt_polyValue_succ cs 0 t).const_add (c : ℝ)

private def stepPoly (a : ℤ) (k : ℕ) : List ℤ → List ℤ
  | [] => []
  | c :: cs => (a * c + cs.headD 0 * (k + 1 : ℕ)) :: stepPoly a (k + 1) cs

private theorem polyValue_stepPoly (a : ℤ) (cs : List ℤ) (k : ℕ) (t : ℝ) :
    polyValue k (stepPoly a k cs) t =
      (a : ℝ) * polyValue k cs t + polyValue k (scaleDerivative k cs.tail) t := by
  induction cs generalizing k with
  | nil => simp [polyValue, stepPoly, scaleDerivative]
  | cons c cs ih =>
    rw [stepPoly, polyValue, ih (k + 1)]
    cases cs with
    | nil => simp [polyValue, scaleDerivative, mul_assoc]
    | cons b bs =>
      simp only [List.headD_cons, List.tail_cons, polyValue, scaleDerivative, Int.cast_add,
        Int.cast_mul, Int.cast_natCast]
      ring

private noncomputable def value : Table → ℝ → ℝ
  | [], _ => 0
  | (r, cs) :: rows, t => polyValue 0 cs t * Real.exp ((r : ℝ) * t) + value rows t

private def step (root : ℤ) (rows : Table) : Table :=
  rows.map fun (r, cs) => (r, stepPoly (r - root) 0 cs)

private def initial : Table → ℤ
  | [] => 0
  | (_, cs) :: rows => cs.headD 0 + initial rows

private theorem value_zero (rows : Table) : value rows 0 = (initial rows : ℝ) := by
  have hp (cs : List ℤ) (k : ℕ) : polyValue (k + 1) cs 0 = 0 := by
    induction cs generalizing k with
    | nil => rfl
    | cons c cs ih => simp [polyValue, ih (k + 1)]
  induction rows with
  | nil => simp [value, initial]
  | cons row rows ih =>
    obtain ⟨r, cs⟩ := row
    cases cs <;> simp [value, initial, polyValue, ih, hp]

private theorem hasDerivAt_integratingFactor (root : ℤ) (rows : Table) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-(root : ℝ) * s) * value rows s)
      (Real.exp (-(root : ℝ) * t) * value (step root rows) t) t := by
  induction rows with
  | nil =>
    simpa [value, step] using (hasDerivAt_const t (0 : ℝ))
  | cons row rows ih =>
    obtain ⟨r, cs⟩ := row
    let e (s : ℝ) := Real.exp ((r - root : ℤ) * s)
    have he (s : ℝ) :
        e s = Real.exp (-(root : ℝ) * s) * Real.exp ((r : ℝ) * s) := by
      dsimp only [e]
      rw [← Real.exp_add, Int.cast_sub]
      congr 1
      ring
    have hd : HasDerivAt e (((r : ℝ) - root) * e t) t := by
      simpa [e, Int.cast_sub, mul_comm] using
        (((hasDerivAt_id' t).const_mul ((r : ℝ) - root)).exp)
    have h := ((hasDerivAt_polyValue cs t).mul hd).add ih
    convert h using 1
    · ext s
      simp only [Pi.add_apply, Pi.mul_apply, value, he s]
      ring
    · simp only [step, List.map_cons, value, polyValue_stepPoly, Int.cast_sub, he t]
      ring

private def checks : List ℤ → Table → Bool
  | [], rows => rows.all fun row => row.2.all fun c => c == 0
  | root :: roots, rows => decide (0 ≤ initial rows) && checks roots (step root rows)

private def positiveJet : List ℤ → Table → Bool
  | [], _ => false
  | root :: roots, rows => decide (0 < initial rows) || positiveJet roots (step root rows)

private theorem value_eq_zero_of_check (rows : Table) (h : checks [] rows = true) (t : ℝ) :
    value rows t = 0 := by
  have hz (cs : List ℤ) (hcs : cs.all (· == 0) = true) (k : ℕ) :
      polyValue k cs t = 0 := by
    induction cs generalizing k with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hcs
      simp [polyValue, hcs.1, ih hcs.2]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨r, cs⟩
    simp only [checks, List.all_cons, Bool.and_eq_true] at h
    simp only [value, hz cs h.1 0, zero_mul, zero_add, ih h.2]

private theorem check_sound (roots : List ℤ) (rows : Table) (h : checks roots rows = true) :
    (∀ t ≥ 0, 0 ≤ value rows t) ∧
    (positiveJet roots rows = true → ∀ t > 0, 0 < value rows t) := by
  induction roots generalizing rows with
  | nil =>
    refine ⟨fun t _ => ?_, by simp [positiveJet]⟩
    rw [value_eq_zero_of_check rows h t]
  | cons root roots ih =>
    simp only [checks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hnonneg, hpos⟩ := ih _ h.2
    let f (s : ℝ) := Real.exp (-(root : ℝ) * s) * value rows s
    have hd := hasDerivAt_integratingFactor root rows
    have hcont (s : ℝ) : ContinuousAt f s := (hd s).continuousAt
    have hdiff (s : ℝ) : DifferentiableAt ℝ f s := (hd s).differentiableAt
    have hzero : 0 ≤ f 0 := by
      simpa [f, value_zero] using h.1
    have hmono : MonotoneOn f (Ici (0 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun s _ => (hcont s).continuousWithinAt)
        (fun s _ => (hdiff s).differentiableWithinAt) ?_
      intro s hs
      rw [show deriv f s = _ from (hd s).deriv]
      exact mul_nonneg (Real.exp_nonneg _) (hnonneg s (interior_subset hs))
    constructor
    · intro t ht
      exact nonneg_of_mul_nonneg_right (hzero.trans (hmono (by simp) ht ht)) (Real.exp_pos _)
    · intro hjet t ht
      simp only [positiveJet, Bool.or_eq_true, decide_eq_true_eq] at hjet
      apply pos_of_mul_pos_right (a := Real.exp (-(root : ℝ) * t)) _ (Real.exp_nonneg _)
      rcases hjet with hpositive | hjet
      · have hf0 : 0 < f 0 := by simpa [f, value_zero] using hpositive
        exact hf0.trans_le (hmono (by simp) ht.le ht.le)
      · have hstrict : StrictMonoOn f (Ici (0 : ℝ)) := by
          refine strictMonoOn_of_deriv_pos (convex_Ici 0)
            (fun s _ => (hcont s).continuousWithinAt) ?_
          intro s hs
          rw [show deriv f s = _ from (hd s).deriv]
          rw [interior_Ici] at hs
          exact mul_pos (Real.exp_pos _) (hpos hjet s hs)
        exact hzero.trans_lt (hstrict (by simp) ht.le ht)

private def roots (rows : Table) : List ℤ :=
  rows.flatMap fun (r, cs) => List.replicate cs.length r

private def discriminantTable : Table :=
  [(0, [-3]), (1, [18]), (2, [-33, -36]), (3, [-54, 72]),
   (4, [-18, -312, -144, 8, -96]), (5, [36, -216]),
   (6, [138, 144, -432, 72, 288, 0, 192]), (7, [36, 216]),
   (8, [-75, 216, 0, -72]), (9, [-54, -72]), (10, [-9, -12, 0, -8]), (11, [18])]

-- Multiply the discriminant by 25 and subtract the first surviving Taylor term.
private def marginTable : Table :=
  (0, [-75, 0, 0, 0, 0, 0, 0, 0, 0, 0, -144]) ::
    discriminantTable.tail.map fun (r, cs) => (r, cs.map (25 * ·))

private def repeatedTable : Table :=
  [(0, [-3]), (2, [0, -12, 0, -8]), (4, [3])]

private def differenceTable : Table :=
  [(0, [-1]), (2, [9]), (4, [9, 36]), (6, [-17, 12])]

private theorem discriminant_checks : checks (roots discriminantTable) discriminantTable = true :=
  by decide

private theorem discriminant_positiveJet :
    positiveJet (roots discriminantTable) discriminantTable = true := by decide

private theorem margin_checks : checks (roots marginTable) marginTable = true := by decide

private theorem repeated_checks : checks (roots repeatedTable) repeatedTable = true := by decide

private theorem repeated_positiveJet :
    positiveJet (roots repeatedTable) repeatedTable = true := by decide

private theorem difference_checks : checks (roots differenceTable) differenceTable = true :=
  by decide

private theorem difference_positiveJet :
    positiveJet (roots differenceTable) differenceTable = true := by decide

private noncomputable def centralNum (t : ℝ) : ℝ :=
  Real.exp (3 * t) - 3 * Real.exp t + 3 * Real.exp (-t) - Real.exp (-3 * t) - 8 * t ^ 3

private noncomputable def repeatedNum (t : ℝ) : ℝ :=
  3 * Real.exp (2 * t) - 3 * Real.exp (-2 * t) - 12 * t - 8 * t ^ 3

private noncomputable def upperNum (t : ℝ) : ℝ :=
  (12 * t - 8) * Real.exp (2 * t) + 9 - Real.exp (-4 * t) - 24 * t ^ 3

private noncomputable def lowerNum (t : ℝ) : ℝ :=
  Real.exp (4 * t) + (12 * t + 8) * Real.exp (-2 * t) - 9 - 24 * t ^ 3

/-- Centered continuum simplex mean at the four logarithmic knots
`(3t, t, -t, -3t)`, written in closed form for `t > 0`. -/
noncomputable def central (t : ℝ) : ℝ := centralNum t / (8 * t ^ 3)

/-- Common repeated-knot closed form in the two matchings. -/
noncomputable def repeated (t : ℝ) : ℝ := repeatedNum t / (8 * t ^ 3)

/-- Closed form at centered knots `(2t, 2t, 0, -4t)`. -/
noncomputable def upper (t : ℝ) : ℝ := upperNum t / (24 * t ^ 3)

/-- Closed form at centered knots `(4t, 0, -2t, -2t)`. -/
noncomputable def lower (t : ℝ) : ℝ := lowerNum t / (24 * t ^ 3)

private theorem exp_mul_nat (t r : ℝ) (n : ℕ) (h : (n : ℝ) = r) :
    Real.exp (r * t) = Real.exp t ^ n := by
  rw [← h, Real.exp_nat_mul]

private theorem discriminantTable_eq (t : ℝ) :
    value discriminantTable t = Real.exp (6 * t) *
      (repeatedNum t * lowerNum t - 3 * (centralNum t - repeatedNum t) ^ 2) := by
  norm_num [value, discriminantTable, polyValue, centralNum, repeatedNum, lowerNum, Real.exp_neg]
  simp only [exp_mul_nat t 2 2 (by norm_num), exp_mul_nat t 3 3 (by norm_num),
    exp_mul_nat t 4 4 (by norm_num), exp_mul_nat t 5 5 (by norm_num),
    exp_mul_nat t 6 6 (by norm_num), exp_mul_nat t 7 7 (by norm_num),
    exp_mul_nat t 8 8 (by norm_num), exp_mul_nat t 9 9 (by norm_num),
    exp_mul_nat t 10 10 (by norm_num), exp_mul_nat t 11 11 (by norm_num)]
  field_simp [Real.exp_ne_zero]
  ring

private theorem marginTable_eq (t : ℝ) :
    value marginTable t = 25 * value discriminantTable t - 144 * t ^ 10 := by
  norm_num [value, marginTable, discriminantTable, polyValue]
  ring

private theorem repeatedTable_eq (t : ℝ) :
    value repeatedTable t = Real.exp (2 * t) * repeatedNum t := by
  norm_num [value, repeatedTable, polyValue, repeatedNum, Real.exp_neg]
  simp only [exp_mul_nat t 2 2 (by norm_num), exp_mul_nat t 4 4 (by norm_num)]
  field_simp [Real.exp_ne_zero]
  ring

private theorem differenceTable_eq (t : ℝ) :
    value differenceTable t = Real.exp (4 * t) * (upperNum t - 3 * repeatedNum t) := by
  norm_num [value, differenceTable, polyValue, upperNum, repeatedNum, Real.exp_neg]
  simp only [exp_mul_nat t 2 2 (by norm_num), exp_mul_nat t 4 4 (by norm_num),
    exp_mul_nat t 6 6 (by norm_num)]
  field_simp [Real.exp_ne_zero]
  ring

theorem repeated_pos {t : ℝ} (ht : 0 < t) : 0 < repeated t := by
  have h := (check_sound _ _ repeated_checks).2 repeated_positiveJet t ht
  rw [repeatedTable_eq] at h
  exact div_pos (pos_of_mul_pos_right h (Real.exp_nonneg _)) (by positivity)

theorem repeated_lt_upper {t : ℝ} (ht : 0 < t) : repeated t < upper t := by
  have h := (check_sound _ _ difference_checks).2 difference_positiveJet t ht
  rw [differenceTable_eq] at h
  have hp := pos_of_mul_pos_right h (Real.exp_nonneg _)
  unfold repeated upper
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_pos hp (show 0 < 8 * t ^ 3 by positivity)]

private theorem discriminant_eq {t : ℝ} (ht : 0 < t) :
    repeated t * lower t - (central t - repeated t) ^ 2 =
      (repeatedNum t * lowerNum t - 3 * (centralNum t - repeatedNum t) ^ 2) / (192 * t ^ 6) := by
  unfold central repeated lower
  field_simp
  ring

/-- The lower repeated-knot product exceeds the square of the difference
between the central term and the common repeated-knot term. -/
theorem discriminant_pos {t : ℝ} (ht : 0 < t) :
    0 < repeated t * lower t - (central t - repeated t) ^ 2 := by
  have h := (check_sound _ _ discriminant_checks).2 discriminant_positiveJet t ht
  rw [discriminantTable_eq] at h
  have hp := pos_of_mul_pos_right h (Real.exp_nonneg _)
  rw [discriminant_eq ht]
  exact div_pos hp (by positivity)

/-- Quantitative lower bound for the repeated-knot discriminant. -/
theorem discriminant_lower_bound {t : ℝ} (ht : 0 < t) :
    3 / 100 * Real.exp (-(6 * t)) * t ^ 4 ≤
      repeated t * lower t - (central t - repeated t) ^ 2 := by
  have h := (check_sound _ _ margin_checks).1 t ht.le
  rw [marginTable_eq, discriminantTable_eq] at h
  rw [discriminant_eq ht]
  apply (le_div_iff₀ (by positivity)).2
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (6 * t))).mp
  have hexp : Real.exp (6 * t) * Real.exp (-(6 * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = (3 / 100 * (Real.exp (6 * t) * Real.exp (-(6 * t))) * 192) * t ^ 10 := by ring
    _ = 144 / 25 * t ^ 10 := by rw [hexp]; norm_num
    _ ≤ _ := by linarith only [h]

/-- Strict two-matching inequality for the continuum closed forms on an
arithmetic progression of four logarithmic knots. -/
theorem central_lt_matching {t : ℝ} (ht : 0 < t) :
    central t < Real.sqrt (repeated t * upper t) + Real.sqrt (repeated t * lower t) := by
  have hD := repeated_pos ht
  have hP := repeated_lt_upper ht
  have hQ := discriminant_pos ht
  have h₁ : repeated t < Real.sqrt (repeated t * upper t) := by
    apply (Real.lt_sqrt hD.le).2
    simpa [pow_two] using mul_lt_mul_of_pos_left hP hD
  have h₂ : central t - repeated t < Real.sqrt (repeated t * lower t) := by
    by_cases h : 0 ≤ central t - repeated t
    · exact (Real.lt_sqrt h).2 (sub_pos.mp hQ)
    · exact (lt_of_not_ge h).trans_le (Real.sqrt_nonneg _)
  linarith only [h₁, h₂]

private theorem central_eq_simplexGap {t : ℝ} (ht : 0 < t) :
    simplexGap (3 * t) t (-t) (-3 * t) = central t := by
  have h₁ : 3 * t ≠ -3 * t := by linarith
  have h₂ : t ≠ -3 * t := by linarith
  have h₃ : -t ≠ -3 * t := by linarith
  unfold simplexGap central centralNum
  rw [simplexExp_eval _ _ _ _ (by linarith) (by linarith) (by linarith)]
  rw [show (3 * t + t + -t + -3 * t) / 4 = 0 by ring, Real.exp_zero]
  simp only [expDividedDifference, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
  ring_nf
  field_simp

private theorem repeated_eq_simplexGap {t : ℝ} (ht : 0 < t) :
    simplexGap (2 * t) (-2 * t) 0 0 = repeated t := by
  have h₁ : 2 * t ≠ 0 := by linarith
  have h₂ : -2 * t ≠ 0 := by linarith
  unfold simplexGap repeated repeatedNum
  rw [simplexExp_eval _ _ _ _ (by linarith) h₁ h₂]
  rw [show (2 * t + -2 * t + 0 + 0) / 4 = 0 by ring, Real.exp_zero]
  simp only [expDividedDifference, ite_eq_right h₁, ite_eq_right h₂,
    ite_true, Real.exp_zero, sub_zero]
  ring_nf
  field_simp
  ring

private theorem upper_eq_simplexGap {t : ℝ} (ht : 0 < t) :
    simplexGap 0 (-4 * t) (2 * t) (2 * t) = upper t := by
  have h₁ : 0 ≠ 2 * t := by linarith
  have h₂ : -4 * t ≠ 2 * t := by linarith
  unfold simplexGap upper upperNum
  rw [simplexExp_eval _ _ _ _ (by linarith) h₁ h₂]
  rw [show (0 + -4 * t + 2 * t + 2 * t) / 4 = 0 by ring, Real.exp_zero]
  simp only [expDividedDifference, ite_eq_right h₁, ite_eq_right h₂,
    ite_true, Real.exp_zero]
  ring_nf
  field_simp
  ring

private theorem lower_eq_simplexGap {t : ℝ} (ht : 0 < t) :
    simplexGap (4 * t) 0 (-2 * t) (-2 * t) = lower t := by
  have h₁ : 4 * t ≠ -2 * t := by linarith
  have h₂ : 0 ≠ -2 * t := by linarith
  unfold simplexGap lower lowerNum
  rw [simplexExp_eval _ _ _ _ (by linarith) h₁ h₂]
  rw [show (4 * t + 0 + -2 * t + -2 * t) / 4 = 0 by ring, Real.exp_zero]
  simp only [expDividedDifference, ite_eq_right h₁, ite_eq_right h₂,
    ite_true, Real.exp_zero]
  ring_nf
  field_simp
  ring

/-- Strict two-matching comparison of the uniform simplex gaps at the four
logs \(3t,t,-t,-3t\). Each repeated knot occupies the last two slots in its
simplex integral. -/
theorem simplexGap_lt_matching {t : ℝ} (ht : 0 < t) :
    simplexGap (3 * t) t (-t) (-3 * t) <
      Real.sqrt (simplexGap t (-3 * t) (3 * t) (3 * t) * simplexGap t (-3 * t) (-t) (-t)) +
      Real.sqrt (simplexGap (3 * t) (-t) t t * simplexGap (3 * t) (-t) (-3 * t) (-3 * t)) := by
  have hp : simplexGap t (-3 * t) (3 * t) (3 * t) = Real.exp t * upper t := by
    rw [show -3 * t = -4 * t + t by ring, show 3 * t = 2 * t+t by ring]
    simpa only [zero_add, upper_eq_simplexGap ht] using
      simplexGap_add 0 (-4 * t) (2 * t) (2 * t) t
  have hq : simplexGap t (-3 * t) (-t) (-t) = Real.exp (-t) * repeated t := by
    conv_lhs => arg 1; rw [show t = 2 * t + -t by ring]
    rw [show -3 * t = -2 * t + -t by ring]
    simpa only [zero_add, repeated_eq_simplexGap ht] using
      simplexGap_add (2 * t) (-2 * t) 0 0 (-t)
  have hr : simplexGap (3 * t) (-t) t t = Real.exp t * repeated t := by
    conv_lhs => arg 1; rw [show 3 * t = 2 * t+t by ring]
    conv_lhs => arg 2; rw [show -t = -2 * t+t by ring]
    simpa only [zero_add, repeated_eq_simplexGap ht] using
      simplexGap_add (2 * t) (-2 * t) 0 0 t
  have hs : simplexGap (3 * t) (-t) (-3 * t) (-3 * t) = Real.exp (-t) * lower t := by
    conv_lhs => arg 1; rw [show 3 * t = 4 * t + -t by ring]
    rw [show -3 * t = -2 * t + -t by ring]
    simpa only [zero_add, lower_eq_simplexGap ht] using
      simplexGap_add (4 * t) 0 (-2 * t) (-2 * t) (-t)
  have cancel (a b : ℝ) : (Real.exp t * a) * (Real.exp (-t) * b) = a * b := by
    calc
      _ = (Real.exp t * Real.exp (-t)) * (a * b) := by ring
      _ = a * b := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [central_eq_simplexGap ht, hp, hq, hr, hs, cancel, cancel,
    mul_comm (upper t) (repeated t)]
  exact central_lt_matching ht

end ArithmeticProgression
end RefinedBMV.Tracial
