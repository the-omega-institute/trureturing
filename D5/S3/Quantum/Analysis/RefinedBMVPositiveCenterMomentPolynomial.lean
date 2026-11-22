/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMomentPolynomial
   generality: G
   mirror-B: none(waiver:internal-arithmetic-identity)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact degree-parameter coefficient polynomials of the small-corner moments. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterJointTaylor
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # Exact normalized small-corner moment polynomials -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open scoped BigOperators

set_option autoImplicit false

/-- Ascending-order Horner evaluation, with coefficients embedded as exact rationals. -/
noncomputable def momentHorner (h : ℝ) : List ℚ → ℝ
  | [] => 0
  | c :: cs => c + h * momentHorner h cs

private def coeffAdd : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: coeffAdd xs ys

private def coeffScale (c : ℚ) (xs : List ℚ) : List ℚ := xs.map (c * ·)

private def coeffMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: cs, ds => coeffAdd (coeffScale c ds) (0 :: coeffMul cs ds)

private def coeffSum (f : ℕ → List ℚ) : ℕ → List ℚ
  | 0 => []
  | n + 1 => coeffAdd (coeffSum f n) (f n)

private theorem horner_add (h : ℝ) (xs ys : List ℚ) :
    momentHorner h (coeffAdd xs ys) = momentHorner h xs + momentHorner h ys := by
  induction xs generalizing ys with
  | nil => simp [coeffAdd, momentHorner]
  | cons x xs ih =>
    cases ys with
    | nil => simp [coeffAdd, momentHorner]
    | cons y ys =>
      simp only [coeffAdd, momentHorner, Rat.cast_add, ih]
      ring

private theorem horner_scale (h : ℝ) (c : ℚ) (xs : List ℚ) :
    momentHorner h (coeffScale c xs) = c * momentHorner h xs := by
  induction xs with
  | nil => simp [coeffScale, momentHorner]
  | cons x xs ih =>
    simp only [coeffScale, List.map_cons, momentHorner, Rat.cast_mul] at *
    rw [ih]
    ring

private theorem horner_mul (h : ℝ) (xs ys : List ℚ) :
    momentHorner h (coeffMul xs ys) = momentHorner h xs * momentHorner h ys := by
  induction xs with
  | nil => simp [coeffMul, momentHorner]
  | cons x xs ih =>
    simp only [coeffMul, horner_add, horner_scale, momentHorner, Rat.cast_zero, zero_add, ih]
    ring

private theorem horner_sum (h : ℝ) (f : ℕ → List ℚ) (n : ℕ) :
    momentHorner h (coeffSum f n) = ∑ i ∈ Finset.range n, momentHorner h (f i) := by
  induction n with
  | zero => simp [coeffSum, momentHorner]
  | succ n ih => rw [coeffSum, horner_add, ih, Finset.sum_range_succ]

private theorem horner_monomial (h : ℝ) (k : ℕ) (c : ℚ) :
    momentHorner h (List.replicate k 0 ++ [c]) = (c : ℝ) * h ^ k := by
  induction k with
  | zero => simp [momentHorner]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, momentHorner, Rat.cast_zero, zero_add,
      ih, pow_succ]
    ring

/-- The series coefficient `[t^a] e^(-t) ((e^(ht)-1)/h)^i`. The powers of
`h` remaining after the order-`i` falling factorial are all nonnegative. -/
private def shiftCoeffs (a i : ℕ) : List ℚ :=
  (List.range (a + 1 - i)).map fun k =>
    (-1 : ℚ) ^ (a - (i + k)) * (a.choose (i + k) : ℚ) *
      (Nat.stirlingSecond (i + k) i : ℚ) * (i.factorial : ℚ) / (a.factorial : ℚ)

private theorem horner_range (h : ℝ) (f : ℕ → ℚ) (n : ℕ) :
    momentHorner h ((List.range n).map f) =
      ∑ k ∈ Finset.range n, (f k : ℝ) * h ^ k := by
  induction n generalizing f with
  | zero => simp [momentHorner]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, momentHorner, List.map_map, ih,
      Finset.sum_range_succ' (fun k ↦ (f k : ℝ) * h ^ k)]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ', Finset.mul_sum]
    rw [add_comm (f 0 : ℝ)]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring

private def fallingCoeffs : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => coeffScale (1 / ((n : ℚ) + 3)) (coeffMul (fallingCoeffs n) [3, -(n : ℚ)])

private theorem falling_eval_succ (h : ℝ) (n : ℕ) :
    momentHorner h (fallingCoeffs (n+1)) =
      momentHorner h (fallingCoeffs n) * (3 - n * h) / ((n : ℝ) + 3) := by
  simp only [fallingCoeffs, horner_scale, horner_mul, Rat.cast_div, Rat.cast_one, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_ofNat, momentHorner, Rat.cast_neg, mul_zero, add_zero]
  ring

private theorem falling_eval_at_degree {p : ℕ} (hp : 0 < p) (n : ℕ) :
    momentHorner (3 / (p : ℝ)) (fallingCoeffs n) =
      (3 / (p : ℝ)) ^ n * ((p + 2).choose (n + 2) : ℝ) /
        ((p + 2).choose 2 : ℝ) := by
  have hlen : 0 < ((p + 2).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ p + 2 by omega)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  induction n with
  | zero =>
    simp [fallingCoeffs, momentHorner, hlen.ne']
  | succ n ih =>
    rw [falling_eval_succ, ih, pow_succ]
    have hscale : 3 - (n : ℝ) * (3 / (p : ℝ)) =
        (3 / (p : ℝ)) * ((p : ℝ) - (n : ℝ)) := by
      field_simp
    rw [hscale]
    have hchoose := real_choose_next p n
    have h₃ : (n : ℝ) + 3 ≠ 0 := by positivity
    calc
      _ = (3 / (p : ℝ)) ^ n * (3 / (p : ℝ)) /
          (((p+2).choose 2 : ℝ) * ((n : ℝ) + 3)) *
            (((p+2).choose (n+2) : ℝ) * ((p : ℝ) - (n : ℝ))) := by
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
      _ = _ := by rw [← hchoose]; field_simp

private theorem shift_eval_scaled (h : ℝ) {a i : ℕ} (hi : i ≤ a) :
    momentHorner h (shiftCoeffs a i) * h ^ i =
      ∑ j ∈ Finset.range (a+1), h ^ j * (-1 : ℝ) ^ (a - j) * (a.choose j : ℝ) *
        (Nat.stirlingSecond j i : ℝ) * (i.factorial : ℝ) / (a.factorial : ℝ) := by
  rw [shiftCoeffs, horner_range, Finset.sum_mul]
  have hsplit := Finset.sum_range_add (fun j : ℕ =>
    h ^ j * (-1 : ℝ) ^ (a - j) * (a.choose j : ℝ) *
      (Nat.stirlingSecond j i : ℝ) * (i.factorial : ℝ) / (a.factorial : ℝ))
    i (a + 1 - i)
  rw [Nat.add_sub_of_le (show i ≤ a + 1 by omega)] at hsplit
  rw [hsplit]
  have hzero : ∑ j ∈ Finset.range i, h ^ j * (-1 : ℝ) ^ (a - j) *
      (a.choose j : ℝ) * (Nat.stirlingSecond j i : ℝ) * (i.factorial : ℝ) /
        (a.factorial : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [Nat.stirlingSecond_eq_zero_of_lt (Finset.mem_range.mp hj)]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  push_cast
  rw [pow_add]
  ring

private theorem shift_eval_at_degree (p : ℕ) {a i : ℕ} (hi : i ≤ a) :
    momentHorner (3 / (p : ℝ)) (shiftCoeffs a i) * (3 / (p : ℝ)) ^ i =
      centeredFallingCoefficient p a i * (i.factorial : ℝ) / (a.factorial : ℝ) := by
  rw [centeredFallingCoefficient, Finset.sum_mul, Finset.sum_div]
  exact shift_eval_scaled _ hi

private def rawMomentCoeffs (a b : ℕ) : List ℚ :=
  coeffSum (fun i ↦ coeffSum (fun j ↦ coeffMul (coeffMul (shiftCoeffs a i) (shiftCoeffs b j))
    (fallingCoeffs (i + j))) (b + 1)) (a + 1)

private theorem raw_moment_eval_at_degree {p : ℕ} (hp : 0 < p) (a b : ℕ) :
    momentHorner (3 / (p : ℝ)) (rawMomentCoeffs a b) =
      (∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (b+1),
        (centeredFallingCoefficient p a i * centeredFallingCoefficient p b j) *
          ((i.factorial : ℝ) * (j.factorial : ℝ) * ((p+2).choose (i+j+2) : ℝ))) /
        (((p+2).choose 2 : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ)) := by
  simp only [rawMomentCoeffs, horner_sum, horner_mul, falling_eval_at_degree hp, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [pow_add]
  have hi' := shift_eval_at_degree p (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hj' := shift_eval_at_degree p (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    _ = (momentHorner (3 / (p : ℝ)) (shiftCoeffs a i) * (3 / (p : ℝ)) ^ i) *
        (momentHorner (3 / (p : ℝ)) (shiftCoeffs b j) * (3 / (p : ℝ)) ^ j) *
          (((p+2).choose (i+j+2) : ℝ) / ((p+2).choose 2 : ℝ)) := by ring
    _ = _ := by rw [hi', hj']; ring

private def splitPlusOne : List ℚ → ℚ × List ℚ
  | [] => (0, [])
  | c :: cs =>
    let (r, q) := splitPlusOne cs
    (c-r, r::q)

private theorem horner_split (h : ℝ) (cs : List ℚ) :
    momentHorner h cs =
      (splitPlusOne cs).1 + (1 + h) * momentHorner h (splitPlusOne cs).2 := by
  induction cs with
  | nil => simp [momentHorner, splitPlusOne]
  | cons c cs ih =>
    simp only [momentHorner, splitPlusOne, Rat.cast_sub]
    rw [ih]
    ring

/-- Exact coefficient list for the analytically normalized Taylor moment `m_ab/c`. -/
def normalizedMomentCoeffs (a b : ℕ) : List ℚ :=
  coeffScale 4 (splitPlusOne (rawMomentCoeffs a b)).2

/-- Remainder of dividing the raw Taylor moment by the normalization factor `1 + h`. -/
def normalizedMomentRemainder (a b : ℕ) : ℚ :=
  (splitPlusOne (rawMomentCoeffs a b)).1

private theorem falling_at_neg_one (n : ℕ) :
    momentHorner (-1 : ℝ) (fallingCoeffs n) = 1 := by
  induction n with
  | zero => simp [fallingCoeffs, momentHorner]
  | succ n ih =>
    have h : (n : ℝ) + 3 ≠ 0 := by positivity
    rw [falling_eval_succ, ih, one_mul, mul_neg_one, sub_neg_eq_add, add_comm, div_self h]

private theorem minus_one_descPochhammer (i : ℕ) :
    (descPochhammer ℝ i).eval (-1) = (-1 : ℝ)^i * (i.factorial : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ,
      ← descPochhammer_eval_eq_prod_range, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one,
      pow_succ]
    ring

private theorem signed_stirling {k n : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range (n+1),
      (Nat.stirlingSecond k i : ℝ) * ((-1 : ℝ)^i * (i.factorial : ℝ))) = (-1 : ℝ)^k := by
  let q : Polynomial ℝ := ∑ i ∈ Finset.range (n+1),
    Polynomial.C (Nat.stirlingSecond k i : ℝ) * descPochhammer ℝ i
  have hpoly : q = Polynomial.X ^ k := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.infinite_range_of_injective
      (Nat.cast_injective (R := ℝ))).mono ?_)
    rintro _ ⟨m, rfl⟩
    simp only [Set.mem_ofPred_eq, q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      descPochhammer_eval_eq_descFactorial]
    have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m k
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))]
    · exact_mod_cast h.symm
    · intro i _ hi
      simp [Nat.stirlingSecond_eq_zero_of_lt (by simpa only [Finset.mem_range, not_lt,
        Nat.succ_le_iff] using hi : k < i)]
  have h := congrArg (Polynomial.eval (-1 : ℝ)) hpoly
  simpa only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, minus_one_descPochhammer] using h

private theorem shift_sum_at_neg_one (a : ℕ) :
    (∑ i ∈ Finset.range (a+1), momentHorner (-1 : ℝ) (shiftCoeffs a i)) =
      (-1 : ℝ)^a / (a.factorial : ℝ) * 0^a := by
  have hsingle (i : ℕ) (hi : i ∈ Finset.range (a+1)) :
      momentHorner (-1 : ℝ) (shiftCoeffs a i) =
        ∑ j ∈ Finset.range (a+1), ((-1 : ℝ)^a / (a.factorial : ℝ) * (a.choose j : ℝ)) *
          ((Nat.stirlingSecond j i : ℝ) * ((-1 : ℝ)^i * (i.factorial : ℝ))) := by
    have hs := shift_eval_scaled (-1 : ℝ) (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    have hsq : (-1 : ℝ)^i * (-1)^i = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = (momentHorner (-1 : ℝ) (shiftCoeffs a i) * (-1)^i) * (-1)^i := by
        rw [mul_assoc, hsq, mul_one]
      _ = _ := by
        rw [hs, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
        ring
  rw [Finset.sum_congr rfl hsingle, Finset.sum_comm]
  have hsum : (∑ j ∈ Finset.range (a+1), ∑ i ∈ Finset.range (a+1),
      ((-1 : ℝ)^a / (a.factorial : ℝ) * (a.choose j : ℝ)) *
        ((Nat.stirlingSecond j i : ℝ) * ((-1 : ℝ)^i * (i.factorial : ℝ)))) =
      ∑ j ∈ Finset.range (a+1),
      ((-1 : ℝ)^a / (a.factorial : ℝ) * (a.choose j : ℝ)) * (-1)^j := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← Finset.mul_sum, signed_stirling (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [hsum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have h := add_pow (-1 : ℝ) 1 a
  simpa only [neg_add_cancel, one_pow, one_mul, mul_one, mul_comm] using h.symm

/-- The normalization has zero remainder at every positive total degree. -/
theorem normalized_moment_remainder_zero {a b : ℕ} (hab : 0 < a + b) :
    normalizedMomentRemainder a b = 0 := by
  have heval := horner_split (-1 : ℝ) (rawMomentCoeffs a b)
  have hraw : momentHorner (-1 : ℝ) (rawMomentCoeffs a b) = 0 := by
    simp only [rawMomentCoeffs, horner_sum, horner_mul, falling_at_neg_one, mul_one,
      ← Finset.mul_sum, ← Finset.sum_mul, shift_sum_at_neg_one]
    rcases (show 0 < a ∨ 0 < b by omega) with h | h
    · simp [zero_pow h.ne']
    · simp [zero_pow h.ne']
  rw [hraw, add_neg_cancel, zero_mul, add_zero] at heval
  exact_mod_cast heval.symm

private theorem normalized_eval_eq_raw (h : ℝ) {a b : ℕ} (hab : 0 < a + b)
    (hh : 1 + h ≠ 0) :
    momentHorner h (normalizedMomentCoeffs a b) = 4 * momentHorner h (rawMomentCoeffs a b) / (1 + h) := by
  have hnorm := horner_split h (rawMomentCoeffs a b)
  have hzero := normalized_moment_remainder_zero hab
  change (splitPlusOne (rawMomentCoeffs a b)).1 = 0 at hzero
  simp only [hzero, Rat.cast_zero, zero_add] at hnorm
  rw [normalizedMomentCoeffs, horner_scale, hnorm]
  push_cast
  field_simp

/-- The normalized rational moment equals the exact joint Taylor coefficient. -/
theorem normalized_moment_eval_joint {p : ℕ} (hp : 0 < p) (r s : ℕ) :
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (r+2) s) =
      jointTaylorMoment p r s / (((r+2).factorial : ℝ) * (s.factorial : ℝ)) := by
  rw [normalized_eval_eq_raw _ (by omega) (by positivity), raw_moment_eval_at_degree hp,
    jointTaylorMoment_eq_falling, joint_normalization_eq hp, DimThree.gaps_length_eq_choose]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem rawMomentCoeffs_eval_swap (h : ℝ) (a b : ℕ) :
    momentHorner h (rawMomentCoeffs a b) = momentHorner h (rawMomentCoeffs b a) := by
  simp only [rawMomentCoeffs, horner_sum, horner_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.add_comm i j]
  ring

theorem normalized_moment_eval_swap {p : ℕ} (a b : ℕ) (hab : 0 < a + b) :
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs a b) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs b a) := by
  have hpos : 0 < 1 + 3 / (p : ℝ) := by positivity
  rw [normalized_eval_eq_raw _ hab hpos.ne',
    normalized_eval_eq_raw _ (by omega : 0 < b + a) hpos.ne', rawMomentCoeffs_eval_swap]

/-- The normalized rational marginal moment equals the Taylor coefficient of degree `k`
in the divided quadratic moment, including the factorial of that moment. -/
theorem normalized_moment_eval_marginal {p : ℕ} (hp : 0 < p) (k : ℕ) :
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k+2)) =
      ((DimThree.gaps p).map fun g ↦ (3 * (g.2.2 : ℝ) / (p : ℝ) - 1) ^ (k+2)).sum /
        (((DimThree.gaps p).length : ℝ) * (compositionMarginalVariance p / 2) *
          ((k+2).factorial : ℝ)) := by
  rw [normalized_moment_eval_swap 0 (k+2) (by omega), normalized_moment_eval_joint hp k 0]
  change (((DimThree.gaps p).map fun g ↦
      (3 * (g.2.1 : ℝ) / (p : ℝ) - 1) ^ 2 *
        ((3 * (g.2.1 : ℝ) / (p : ℝ) - 1) ^ k * (3 * (g.2.2 : ℝ) / (p : ℝ) - 1) ^ 0)).sum /
        (((DimThree.gaps p).length : ℝ) * (compositionMarginalVariance p / 2))) /
        (((k+2).factorial : ℝ) * ((0 : ℕ).factorial : ℝ)) = _
  have hcycle := ((DimThree.gaps_cycle_all p).map fun g ↦
    (3 * (g.2.1 : ℝ) / (p : ℝ) - 1)^ (k+2)).sum_eq
  simp only [List.map_map, Function.comp_def] at hcycle
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_div]
  simp_rw [← pow_add, Nat.add_comm 2 k]
  rw [← hcycle]

private theorem abs_centered_gap_le {p j : ℕ} (hp : 0 < p) (hj : j ≤ p) :
    |3 * (j : ℝ) / (p : ℝ) - 1| ≤ 2 := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hj' : (j : ℝ) ≤ p := by exact_mod_cast hj
  have h₀ : 0 ≤ 3 * (j : ℝ) / (p : ℝ) := by positivity
  have h₁ : 3 * (j : ℝ) / (p : ℝ) ≤ 3 := (div_le_iff₀ hp').2 (by linarith)
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem abs_list_sum_bound {α : Type*} (l : List α) (f w : α → ℝ)
    (h : ∀ t ∈ l, |f t| ≤ w t) : |(l.map f).sum| ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (abs_add_le (f t) (l.map f).sum).trans
        (add_le_add (h t (by simp)) (ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)))

private theorem jointTaylorMoment_abs_bound {p : ℕ} (hp : 0 < p) (r s : ℕ) :
    |jointTaylorMoment p r s| ≤ (2 : ℝ) ^ (r+s+1) := by
  let x (g : ℕ × ℕ × ℕ) : ℝ := 3 * (g.2.1 : ℝ) / (p : ℝ) - 1
  let y (g : ℕ × ℕ × ℕ) : ℝ := 3 * (g.2.2 : ℝ) / (p : ℝ) - 1
  let N : ℝ := (DimThree.gaps p).length
  let c : ℝ := compositionMarginalVariance p / 2
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (DimThree.word_counts_all p).2.1
  have hc : 0 < c := half_pos (compositionMarginalVariance_pos p)
  have hsumx : ((DimThree.gaps p).map fun g ↦ x g ^ 2).sum = N * (2*c) := by
    have hcycle := ((DimThree.gaps_cycle_all p).map fun g ↦ x g ^ 2).sum_eq
    simp only [List.map_map, Function.comp_def, x] at hcycle
    rw [← hcycle]
    change ((DimThree.gaps p).map fun g ↦ y g ^ 2).sum = N * (2*c)
    have hvar : compositionMarginalVariance p =
        ((DimThree.gaps p).map fun g ↦ y g ^ 2).sum / N := rfl
    dsimp only [c]
    rw [hvar]
    field_simp
  have hpoint (g : ℕ × ℕ × ℕ) (hg : g ∈ DimThree.gaps p) :
      |x g ^ 2 * (x g ^ r * y g ^ s)| ≤ (2 : ℝ)^r * 2^s * x g^2 := by
    have htotal := (DimThree.mem_gaps_iff_total p g).mp hg
    have hx : |x g| ≤ 2 := abs_centered_gap_le hp (by omega)
    have hy : |y g| ≤ 2 := abs_centered_gap_le hp (by omega)
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow, abs_pow, mul_comm (x g^2)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx _) (pow_le_pow_left₀ (abs_nonneg _) hy _)
        (pow_nonneg (abs_nonneg _) _) (by positivity)) (sq_nonneg _)
  change |((DimThree.gaps p).map (fun g ↦ x g ^ 2 * (x g ^ r * y g ^ s))).sum /
      (N*c)| ≤ _
  rw [abs_div, abs_of_pos (mul_pos hN hc), div_le_iff₀ (mul_pos hN hc)]
  have h := abs_list_sum_bound (DimThree.gaps p) _ _ hpoint
  rw [List.sum_map_mul_left, hsumx] at h
  refine h.trans (le_of_eq ?_)
  rw [pow_add, pow_add, pow_one]
  ring

/-- Elementary coarse bound on each joint Taylor coefficient, from the bound of two
on the magnitudes of the centered gaps and the exact total quadratic weight. -/
theorem normalized_moment_abs_bound_joint {p : ℕ} (hp : 0 < p) (r s : ℕ) :
    |momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (r+2) s)| ≤
      (2 : ℝ) ^ (r+s+1) / (((r+2).factorial : ℝ) * (s.factorial : ℝ)) := by
  have hfa : (0 : ℝ) ≤ ((r+2).factorial : ℝ) := Nat.cast_nonneg _
  have hfb : (0 : ℝ) ≤ (s.factorial : ℝ) := Nat.cast_nonneg _
  have hfac := mul_nonneg hfa hfb
  rw [normalized_moment_eval_joint hp, abs_div, abs_of_nonneg hfac]
  exact div_le_div_of_nonneg_right (jointTaylorMoment_abs_bound hp r s) hfac

/-- Elementary coarse bound on each marginal Taylor coefficient. -/
theorem normalized_moment_abs_bound_marginal {p : ℕ} (hp : 0 < p) (r : ℕ) :
    |momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (r+2))| ≤
      (2 : ℝ) ^ (r+1) / ((r+2).factorial : ℝ) := by
  rw [normalized_moment_eval_swap 0 (r+2) (by omega)]
  simpa using normalized_moment_abs_bound_joint hp r 0

private theorem factorial_eq_mul_desc (a i : ℕ) :
    ((a+i).factorial : ℝ) = (i.factorial : ℝ) * ((a+i).descFactorial a : ℝ) := by
  have h := Nat.factorial_mul_descFactorial (show a ≤ a+i by omega)
  rw [show a+i-a = i by omega] at h
  exact_mod_cast h.symm

/-- The differentiated joint Taylor polynomial expressed using the same
normalized rational coefficients that the interval calculation encloses. -/
theorem jointTaylorPolynomial_eq_normalized_moments {p : ℕ} (hp : 0 < p)
    (a b : ℕ) (u v : ℝ) :
    jointTaylorPolynomial p a b u v =
      ∑ m ∈ Finset.range (23-a-b), ∑ i ∈ Finset.range (m+1),
        let j := m-i
        momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (a+i+2) (b+j)) *
          ((a+i).descFactorial a : ℝ) * ((b+j).descFactorial b : ℝ) * u^i * v^j := by
  unfold jointTaylorPolynomial
  refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  let j := m-i
  change jointTaylorMoment p (a+i) (b+j) *
      (u^i * v^j / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
        (1 / ((((a+i : ℕ) : ℝ) + 1) * (((a+i : ℕ) : ℝ) + 2)))) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (a+i+2) (b+j)) *
        ((a+i).descFactorial a : ℝ) * ((b+j).descFactorial b : ℝ) * u^i * v^j
  rw [normalized_moment_eval_joint hp (a+i) (b+j)]
  have hfac : ((a+i+2).factorial : ℝ) =
      (((a+i : ℕ) : ℝ) + 2) * (((a+i : ℕ) : ℝ) + 1) *
        (i.factorial : ℝ) * ((a+i).descFactorial a : ℝ) := by
    rw [show a+i+2 = (a+i+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rw [factorial_eq_mul_desc]
    ring
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have ha : ((a+i).descFactorial a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (show a ≤ a+i by omega)).ne'
  have hb : ((b+j).descFactorial b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (show b ≤ b+j by omega)).ne'
  have h₁ : (((a+i : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have h₂ : (((a+i : ℕ) : ℝ) + 2) ≠ 0 := by positivity
  rw [hfac, factorial_eq_mul_desc b j]
  field_simp [ha, hb, hi, hj, h₁, h₂]
  <;> ring

#print axioms normalized_moment_remainder_zero
#print axioms normalized_moment_eval_joint
#print axioms normalized_moment_eval_marginal
#print axioms normalized_moment_abs_bound_joint
#print axioms normalized_moment_abs_bound_marginal
#print axioms jointTaylorPolynomial_eq_normalized_moments

end RefinedBMV.PositiveCenter.SmallCorner

namespace RefinedBMV.PositiveCenter.SmallCorner

open scoped BigOperators

set_option autoImplicit false

private def integerCoeffAdd : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: integerCoeffAdd xs ys

private def integerCoeffScale (c : ℤ) (xs : List ℤ) : List ℤ := xs.map (c * ·)

private def integerCoeffMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | c :: cs, ds => integerCoeffAdd (integerCoeffScale c ds) (0 :: integerCoeffMul cs ds)

private def integerCoeffSum (f : ℕ → List ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => integerCoeffAdd (integerCoeffSum f n) (f n)

private def scaledIntegers (d : ℚ) (xs : List ℤ) : List ℚ := xs.map fun (x : ℤ) => (x : ℚ) * d

private theorem scaledIntegers_add (d : ℚ) (xs ys : List ℤ) :
    scaledIntegers d (integerCoeffAdd xs ys) =
      coeffAdd (scaledIntegers d xs) (scaledIntegers d ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      change ((x + y : ℤ) : ℚ) * d :: scaledIntegers d (integerCoeffAdd xs ys) =
        ((x : ℚ) * d + (y : ℚ) * d) :: coeffAdd (scaledIntegers d xs) (scaledIntegers d ys)
      rw [ih, Int.cast_add, add_mul]

private theorem coeffScale_scaledIntegers (c d : ℚ) (xs : List ℤ) :
    coeffScale c (scaledIntegers d xs) = scaledIntegers (c * d) xs := by
  simp only [coeffScale, scaledIntegers, List.map_map, Function.comp_def]
  congr 1
  funext
  ring

private theorem scaledIntegers_scale (d : ℚ) (c : ℤ) (xs : List ℤ) :
    scaledIntegers d (integerCoeffScale c xs) = coeffScale ((c : ℚ) * d) (scaledIntegers 1 xs) := by
  simp only [scaledIntegers, integerCoeffScale, coeffScale, List.map_map, Function.comp_def,
    Int.cast_mul, mul_one]
  congr 1
  funext
  ring

private theorem scaledIntegers_mul (d e : ℚ) (xs ys : List ℤ) :
    scaledIntegers (d * e) (integerCoeffMul xs ys) =
      coeffMul (scaledIntegers d xs) (scaledIntegers e ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [integerCoeffMul, scaledIntegers_add]
    change coeffAdd (scaledIntegers (d * e) (integerCoeffScale x ys))
      ((0 : ℚ) * (d * e) :: scaledIntegers (d * e) (integerCoeffMul xs ys)) =
      coeffAdd (coeffScale ((x : ℚ) * d) (scaledIntegers e ys))
        (0 :: coeffMul (scaledIntegers d xs) (scaledIntegers e ys))
    rw [zero_mul, ih]
    congr 1
    simp only [scaledIntegers, integerCoeffScale, coeffScale, List.map_map, Function.comp_def,
      Int.cast_mul]
    congr 1
    funext
    ring

private theorem scaledIntegers_sum (d : ℚ) (f : ℕ → List ℤ) (g : ℕ → List ℚ)
    (n : ℕ) (h : ∀ j < n, scaledIntegers d (f j) = g j) :
    scaledIntegers d (integerCoeffSum f n) = coeffSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [integerCoeffSum, coeffSum, scaledIntegers_add, ih, h n (Nat.lt_succ_self _)]
    exact fun j hj => h j (Nat.lt_succ_of_lt hj)

private def shiftNumerators (a i : ℕ) : List ℤ :=
  (List.range (a + 1 - i)).map fun k =>
    (-1 : ℤ) ^ (a - (i + k)) * (a.choose (i + k) : ℤ) *
      (Nat.stirlingSecond (i + k) i : ℤ) * (i.factorial : ℤ)

private theorem shiftNumerators_scaled (a i : ℕ) :
    scaledIntegers ((a.factorial : ℚ)⁻¹) (shiftNumerators a i) = shiftCoeffs a i := by
  simp [scaledIntegers, shiftNumerators, shiftCoeffs, Int.cast_mul, Int.cast_pow, div_eq_mul_inv]

private def fallingNumerators : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => integerCoeffMul (fallingNumerators n) [3, -(n : ℤ)]

private theorem fallingNumerators_scaled (n : ℕ) :
    scaledIntegers (2 / ((n + 2).factorial : ℚ)) (fallingNumerators n) = fallingCoeffs n := by
  induction n with
  | zero => norm_num [scaledIntegers, fallingNumerators, fallingCoeffs, Nat.factorial]
  | succ n ih =>
    have h : (2 : ℚ) / (((n + 1) + 2).factorial : ℚ) =
        (1 / ((n : ℚ) + 3)) * (2 / ((n + 2).factorial : ℚ)) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
      have hn : ((n + 2 + 1 : ℕ) : ℚ) = (n : ℚ) + 3 := by push_cast; ring
      rw [Nat.cast_mul, hn]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [fallingNumerators, fallingCoeffs, h, ← coeffScale_scaledIntegers]
    have hmul := scaledIntegers_mul (2 / ((n + 2).factorial : ℚ)) 1
      (fallingNumerators n) [3, -(n : ℤ)]
    simp only [mul_one] at hmul
    rw [hmul, ih]
    simp [scaledIntegers]

private def momentRawNumerators (a b : ℕ) : List ℤ :=
  integerCoeffSum (fun i => integerCoeffSum (fun j =>
    integerCoeffScale (((a + b + 2).descFactorial (a + b - (i + j))) : ℤ)
      (integerCoeffMul (integerCoeffMul (shiftNumerators a i) (shiftNumerators b j))
        (fallingNumerators (i + j)))) (b + 1)) (a + 1)

/-- The common positive denominator for the integer coefficients of the normalized moment. -/
def certifiedMomentDenominator (a b : ℕ) : ℕ :=
  a.factorial * b.factorial * (a + b + 2).factorial

private theorem momentRawNumerators_scaled (a b : ℕ) :
    scaledIntegers (2 / (certifiedMomentDenominator a b : ℚ)) (momentRawNumerators a b) =
      rawMomentCoeffs a b := by
  unfold momentRawNumerators rawMomentCoeffs
  apply scaledIntegers_sum
  intro i hi
  apply scaledIntegers_sum
  intro j hj
  have hle : a + b - (i + j) ≤ a + b + 2 := by omega
  have hfac := Nat.factorial_mul_descFactorial hle
  rw [show a + b + 2 - (a + b - (i + j)) = i + j + 2 by omega] at hfac
  have hfactor (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hscale : (((a + b + 2).descFactorial (a + b - (i + j))) : ℚ) *
      (2 / (certifiedMomentDenominator a b : ℚ)) =
      ((a.factorial : ℚ)⁻¹ * (b.factorial : ℚ)⁻¹) * (2 / ((i + j + 2).factorial : ℚ)) := by
    rw [certifiedMomentDenominator, ← hfac]
    push_cast
    have hpos : 0 < (a + b + 2).descFactorial (a + b - (i + j)) :=
      Nat.descFactorial_pos.mpr (by omega)
    have hne : (((a + b + 2).descFactorial (a + b - (i + j))) : ℚ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    field_simp [hfactor, hne]
  rw [scaledIntegers_scale]
  change coeffScale (((a + b + 2).descFactorial (a + b - (i + j)) : ℚ) *
      (2 / (certifiedMomentDenominator a b : ℚ))) _ = _
  rw [hscale]
  rw [coeffScale_scaledIntegers, mul_one, scaledIntegers_mul, scaledIntegers_mul,
    shiftNumerators_scaled, shiftNumerators_scaled, fallingNumerators_scaled]

private def integerSplitPlusOne : List ℤ → ℤ × List ℤ
  | [] => (0, [])
  | c :: cs =>
    let (r, q) := integerSplitPlusOne cs
    (c-r, r::q)

private theorem integerSplitPlusOne_scaled (d : ℚ) (xs : List ℤ) :
    splitPlusOne (scaledIntegers d xs) =
      ((integerSplitPlusOne xs).1 * d, scaledIntegers d (integerSplitPlusOne xs).2) := by
  induction xs with
  | nil => simp [scaledIntegers, splitPlusOne, integerSplitPlusOne]
  | cons x xs ih =>
    change (let (r,q) := splitPlusOne (scaledIntegers d xs); ((x : ℚ) * d-r,r::q)) = _
    rw [ih]
    cases h : integerSplitPlusOne xs
    simp [integerSplitPlusOne, h, scaledIntegers, sub_mul]

/-- Integer numerators obtained before any division or rational normalization. -/
def certifiedMomentNumerators (a b : ℕ) : List ℤ :=
  integerCoeffScale 8 (integerSplitPlusOne (momentRawNumerators a b)).2

/-- Exact normalized moment coefficients computed with integer arithmetic before division. -/
def certifiedMomentCoeffs (a b : ℕ) : List ℚ :=
  (certifiedMomentNumerators a b).map fun (c : ℤ) => (c : ℚ) / (certifiedMomentDenominator a b : ℚ)

theorem certifiedMomentCoeffs_eq (a b : ℕ) :
    certifiedMomentCoeffs a b = normalizedMomentCoeffs a b := by
  rw [certifiedMomentCoeffs, certifiedMomentNumerators, normalizedMomentCoeffs,
    ← momentRawNumerators_scaled, integerSplitPlusOne_scaled]
  simp only [integerCoeffScale, scaledIntegers, coeffScale, List.map_map, Function.comp_def,
    Int.cast_mul, Int.cast_ofNat, div_eq_mul_inv]
  congr 1
  funext
  ring

#print axioms certifiedMomentCoeffs_eq

end RefinedBMV.PositiveCenter.SmallCorner
