/- GID: D5/S0/Carrier/Euclidean
   generality: G
   mirror-B: D5/B/S0/Carrier/Norm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Nearest-coordinate division makes the golden integers norm-Euclidean. -/

import D5.S0.Carrier.Norm
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Data.Rat.Floor

namespace D5.S0.Carrier

/-- The golden norm vanishes only at zero. -/
@[simp] theorem norm_eq_zero_iff (x : GoldenInt) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply toZsqrtd_injective
    apply (Zsqrtd.norm_eq_zero (a := toZsqrtd x) ?_).mp
    · rw [zsqrtd_norm_toZsqrtd, hx]
      norm_num
    · intro n hn
      have hlower : -3 < n := by nlinarith
      have hupper : n < 3 := by nlinarith
      have hn_cases : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hn_cases with rfl | rfl | rfl | rfl | rfl <;> norm_num at hn
  · intro hx
    rw [hx]
    exact norm_zero

/-- Round both integral-basis coordinates of the exact quotient. Ties round upward. -/
def goldenQuotient (a b : GoldenInt) : GoldenInt :=
  let c := a * conj b
  let n := norm b
  ⟨round ((c.a : ℚ) / (n : ℚ)), round ((c.b : ℚ) / (n : ℚ))⟩

/-- The remainder paired with `goldenQuotient`. -/
def goldenRemainder (a b : GoldenInt) : GoldenInt :=
  a - goldenQuotient a b * b

@[simp] theorem goldenQuotient_zero (a : GoldenInt) : goldenQuotient a 0 = 0 := by
  ext <;> simp [goldenQuotient]

theorem golden_quotient_mul_add_remainder (a b : GoldenInt) :
    b * goldenQuotient a b + goldenRemainder a b = a := by
  simp [goldenRemainder]
  ring

private theorem golden_form_abs_le (x y : ℚ)
    (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    |x * x + x * y - y * y| ≤ 5 / 16 := by
  rw [abs_le] at hx hy ⊢
  have hx_sq : x * x ≤ 1 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - x by linarith)
      (show 0 ≤ 1 / 2 + x by linarith)]
  have hy_sq : y * y ≤ 1 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - y by linarith)
      (show 0 ≤ 1 / 2 + y by linarith)]
  constructor
  · nlinarith [sq_nonneg (x + y / 2)]
  · nlinarith [sq_nonneg (y - x / 2)]

private theorem golden_remainder_norm_lt (a : GoldenInt) {b : GoldenInt} (hb : b ≠ 0) :
    (norm (goldenRemainder a b)).natAbs < (norm b).natAbs := by
  let c := a * conj b
  let n := norm b
  let q := goldenQuotient a b
  let r := goldenRemainder a b
  let s := r * conj b
  let x : ℚ := (c.a : ℚ) / (n : ℚ) - (q.a : ℚ)
  let y : ℚ := (c.b : ℚ) / (n : ℚ) - (q.b : ℚ)
  have hn : n ≠ 0 := by
    simpa [n] using (mt (norm_eq_zero_iff b).mp hb)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hqa : q.a = round ((c.a : ℚ) / (n : ℚ)) := by
    rfl
  have hqb : q.b = round ((c.b : ℚ) / (n : ℚ)) := by
    rfl
  have hx : |x| ≤ 1 / 2 := by
    simpa [x, hqa] using (abs_sub_round ((c.a : ℚ) / (n : ℚ)))
  have hy : |y| ≤ 1 / 2 := by
    simpa [y, hqb] using (abs_sub_round ((c.b : ℚ) / (n : ℚ)))
  have hrs : s = c - (n : GoldenInt) * q := by
    dsimp [s, r, c, n]
    rw [goldenRemainder, sub_mul, mul_assoc, ← norm_eq_mul_conj]
    ring
  have hsa : s.a = c.a - n * q.a := by
    rw [hrs]
    change c.a - (n * q.a + 0 * q.b) = c.a - n * q.a
    ring
  have hsb : s.b = c.b - n * q.b := by
    rw [hrs]
    change c.b - (n * q.b + 0 * q.a + 0 * q.b) = c.b - n * q.b
    ring
  have hsax : (s.a : ℚ) = (n : ℚ) * x := by
    rw [hsa]
    push_cast
    dsimp [x]
    field_simp
  have hsby : (s.b : ℚ) = (n : ℚ) * y := by
    rw [hsb]
    push_cast
    dsimp [y]
    field_simp
  have hnorms : ((norm s : ℤ) : ℚ) =
      (n : ℚ) ^ 2 * (x * x + x * y - y * y) := by
    rw [norm_def]
    push_cast
    rw [hsax, hsby]
    ring
  have hnorms_int : norm s = norm r * n := by
    dsimp [s, n]
    rw [norm_mul, norm_conj]
  have hnormr : ((norm r : ℤ) : ℚ) =
      (n : ℚ) * (x * x + x * y - y * y) := by
    apply mul_left_cancel₀ hnq
    calc
      (n : ℚ) * (norm r : ℚ) = (norm s : ℤ) := by
        rw [hnorms_int]
        push_cast
        ring
      _ = (n : ℚ) ^ 2 * (x * x + x * y - y * y) := hnorms
      _ = (n : ℚ) * ((n : ℚ) * (x * x + x * y - y * y)) := by ring
  have hform := golden_form_abs_le x y hx hy
  have hnormr_le : |((norm r : ℤ) : ℚ)| ≤ |(n : ℚ)| * (5 / 16) := by
    rw [hnormr, abs_mul]
    exact mul_le_mul_of_nonneg_left hform (abs_nonneg _)
  have hn_abs_pos : 0 < |(n : ℚ)| := abs_pos.mpr hnq
  have hnormr_lt : |((norm r : ℤ) : ℚ)| < |(n : ℚ)| :=
    lt_of_le_of_lt hnormr_le (by nlinarith)
  have hnormr_lt_int : |norm r| < |n| := by
    exact_mod_cast hnormr_lt
  have hnormr_lt_natAbs : (norm r).natAbs < n.natAbs := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hnormr_lt_int
    exact_mod_cast hnormr_lt_int
  simpa [r, n] using hnormr_lt_natAbs

/-- Division with remainder strictly decreases the absolute golden norm. -/
theorem golden_division (a b : GoldenInt) (hb : b ≠ 0) :
    ∃ q r : GoldenInt,
      a = q * b + r ∧ (r = 0 ∨ (norm r).natAbs < (norm b).natAbs) := by
  refine ⟨goldenQuotient a b, goldenRemainder a b, ?_, Or.inr ?_⟩
  · simp [goldenRemainder]
  · exact golden_remainder_norm_lt a hb

private theorem norm_le_norm_mul_right (a : GoldenInt) {b : GoldenInt} (hb : b ≠ 0) :
    (norm a).natAbs ≤ (norm (a * b)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  exact Int.natAbs_pos.mpr (mt (norm_eq_zero_iff b).mp hb)

instance instNontrivialGoldenInt : Nontrivial GoldenInt :=
  ⟨⟨0, 1, by decide⟩⟩

/-- The golden integers form a Euclidean domain for the absolute algebraic norm. -/
instance instEuclideanDomainGoldenInt : EuclideanDomain GoldenInt :=
  { commRing, instNontrivialGoldenInt with
    quotient := goldenQuotient
    quotient_zero := goldenQuotient_zero
    remainder := goldenRemainder
    quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
    r := fun a b => (norm a).natAbs < (norm b).natAbs
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := golden_remainder_norm_lt
    mul_left_not_lt := fun a _ hb => not_lt_of_ge (norm_le_norm_mul_right a hb) }

end D5.S0.Carrier
