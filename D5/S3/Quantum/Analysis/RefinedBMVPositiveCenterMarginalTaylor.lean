/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMarginalTaylor
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform marginal Taylor enclosures for the positive-center BMV small corner. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterJointTaylor
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Marginal Taylor bounds on the closed positive-center BMV small corner. -/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter.SmallCorner

open DimThree (gaps gaps_cycle_all mem_gaps_iff_total word_counts_all)

private abbrev Gap := ℕ × ℕ × ℕ
private abbrev varianceHalf (p : ℕ) : ℝ := compositionMarginalVariance p / 2
private abbrev exponent (p j : ℕ) : ℝ := 3 * (j : ℝ) / p - 1
private abbrev denominator (p : ℕ) : ℝ := ((gaps p).length : ℝ) * varianceHalf p

private theorem denominator_pos (p : ℕ) : 0 < denominator p :=
  mul_pos (by exact_mod_cast (word_counts_all p).2.1) (half_pos (compositionMarginalVariance_pos p))

private theorem exponent_abs_le {p : ℕ} (hp : 0 < p) {g : Gap} (hg : g ∈ gaps p) :
    |exponent p g.2.2| ≤ 2 := by
  have hsum := (mem_gaps_iff_total p g).mp hg
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hjR : (g.2.2 : ℝ) ≤ p := by exact_mod_cast (show g.2.2 ≤ p by omega)
  have h₀ : (0 : ℝ) ≤ 3 * (g.2.2 : ℝ) / p := by positivity
  have h₁ : 3 * (g.2.2 : ℝ) / p ≤ 3 := (div_le_iff₀ hpR).2 (by linarith)
  exact abs_le.2 ⟨by dsimp only [exponent]; linarith, by dsimp only [exponent]; linarith⟩

private theorem sum_marginal_square (p : ℕ) :
    ((gaps p).map fun g ↦ exponent p g.2.2 ^ 2).sum = 2 * denominator p := by
  have hN : ((gaps p).length : ℝ) ≠ 0 := by exact_mod_cast (word_counts_all p).2.1.ne'
  dsimp only [denominator, varianceHalf, exponent, compositionMarginalVariance]
  field_simp [hN]

private theorem sum_map_mono {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ i ∈ l, f i ≤ g i) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      add_le_add (h i (by simp)) (ih fun j hj ↦ h j (List.mem_cons_of_mem _ hj))

private theorem list_sum_map_finsetSum {α ι : Type*} (l : List α) (s : Finset ι)
    (f : α → ι → ℝ) :
    (l.map fun g ↦ ∑ i ∈ s, f g i).sum = ∑ i ∈ s, (l.map fun g ↦ f g i).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

private theorem marginal_power_sum_eq (p n : ℕ) :
    ((gaps p).map fun g ↦ exponent p g.2.2 ^ 2 * exponent p g.2.2 ^ n).sum /
      denominator p = jointTaylorMoment p n 0 := by
  have h := ((gaps_cycle_all p).map fun g ↦ exponent p g.2.1 ^ 2 * exponent p g.2.1 ^ n).sum_eq
  simp only [List.map_map, Function.comp_def] at h
  change _ = ((gaps p).map fun g ↦ exponent p g.2.1 ^ 2 *
    (exponent p g.2.1 ^ n * exponent p g.2.2 ^ 0)).sum / denominator p
  simp only [pow_zero, mul_one, h]

/-- The differentiated degree-22 BMV marginal polynomial, in the same normalized
moments as the joint Taylor polynomial. -/
def marginalTaylorPolynomial (p order : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (23 - order), jointTaylorMoment p (order + i) 0 * t ^ i /
    ((i.factorial : ℝ) * (((order + i : ℕ) : ℝ) + 1) * (((order + i : ℕ) : ℝ) + 2))

private theorem marginalTaylorPolynomial_eq_sum (p k : ℕ) (t : ℝ) :
    marginalTaylorPolynomial p k t =
      ((gaps p).map fun g ↦ exponent p g.2.2 ^ 2 *
        (∑ i ∈ Finset.range (23 - k), exponent p g.2.2 ^ (k + i) * t ^ i /
          ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) * (((k + i : ℕ) : ℝ) + 2)))).sum /
        denominator p := by
  simp only [marginalTaylorPolynomial, Finset.mul_sum, list_sum_map_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← marginal_power_sum_eq]
  simp_rw [show ∀ (x : ℝ), x ^ 2 *
      (x ^ (k + i) * t ^ i / ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) *
        (((k + i : ℕ) : ℝ) + 2))) =
      (x ^ 2 * x ^ (k + i)) * (t ^ i / ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) *
        (((k + i : ℕ) : ℝ) + 2))) by
    intro x
    ring]
  rw [List.sum_map_mul_right]
  ring

/-- Uniform remainder of the value and each of the four derivatives of the
marginal continuation. Both signs of the gap, and the gap zero, are included. -/
theorem integralMarginalDerivative_sub_taylor_le {p order : ℕ} (hp : 0 < p)
    (ho : order ≤ 4) {t : ℝ} (ht : |t| ≤ 1) :
    |integralMarginalDerivative p (varianceHalf p) order t -
      marginalTaylorPolynomial p order t| ≤ 1 / (2 : ℝ) ^ 30 := by
  rw [marginalTaylorPolynomial_eq_sum]
  let f (g : Gap) := exponent p g.2.2 ^ 2 *
    (∫ s in (0 : ℝ)..1, (1 - s) * (exponent p g.2.2 * s) ^ order *
      Real.exp (t * (exponent p g.2.2 * s)))
  let polynomial (g : Gap) := exponent p g.2.2 ^ 2 *
    ∑ i ∈ Finset.range (23 - order), exponent p g.2.2 ^ (order + i) * t ^ i /
      ((i.factorial : ℝ) * (((order + i : ℕ) : ℝ) + 1) * (((order + i : ℕ) : ℝ) + 2))
  let ε : ℝ := 1 / (2 : ℝ) ^ 31
  change |(List.map f (gaps p)).sum / denominator p -
    (List.map polynomial (gaps p)).sum / denominator p| ≤ _
  have hden := denominator_pos p
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_le]
  have localBound (g : Gap) (hg : g ∈ gaps p) :
      |f g - polynomial g| ≤ exponent p g.2.2 ^ 2 * ε := by
    dsimp only [f, polynomial]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (weighted_exponential_moment_integral_error (exponent_abs_le hp hg) ht ho (by omega))
      (sq_nonneg _)
  let weight (g : Gap) : ℝ := exponent p g.2.2 ^ 2 * ε
  have hw : ((gaps p).map weight).sum = (1 / (2 : ℝ) ^ 30) * denominator p := by
    dsimp only [weight]
    rw [List.sum_map_mul_right, sum_marginal_square]
    dsimp only [ε]
    ring
  have hl := sum_map_mono (gaps p) (fun g ↦ polynomial g - weight g) f (by
    intro g hg
    have h := (abs_le.mp (localBound g hg)).1
    dsimp only [weight]
    linarith)
  have hu := sum_map_mono (gaps p) f (fun g ↦ polynomial g + weight g) (by
    intro g hg
    have h := (abs_le.mp (localBound g hg)).2
    dsimp only [weight]
    linarith)
  rw [show (List.map (fun g ↦ polynomial g - weight g) (gaps p)).sum =
    (List.map polynomial (gaps p)).sum - (List.map weight (gaps p)).sum by
      induction gaps p with
      | nil => simp
      | cons g l ih => simp only [List.map_cons, List.sum_cons, ih]; ring] at hl
  rw [List.sum_map_add] at hu
  rw [hw] at hl hu
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

private theorem exp_bounded {x : ℝ} (hx : |x| ≤ 2) : 1 / 8 ≤ Real.exp x ∧ Real.exp x ≤ 8 := by
  have htwo : Real.exp 2 ≤ 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have ho := Real.exp_one_lt_d9
    calc
      _ ≤ 2.7182818286 * 2.7182818286 :=
        mul_le_mul ho.le ho.le (Real.exp_pos 1).le (by norm_num)
      _ ≤ _ := by norm_num
  have hneg : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) htwo
  exact ⟨hneg.trans (Real.exp_le_exp.mpr (abs_le.mp hx).1),
    (Real.exp_le_exp.mpr (abs_le.mp hx).2).trans htwo⟩

/-- The continued marginal is a positive average of exponentials with argument
in `[-2,2]`, justifying the radicand intersection in the boxes. -/
theorem integralMarginalDerivative_zero_mem {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht : |t| ≤ 1) :
    1 / 8 ≤ integralMarginalDerivative p (varianceHalf p) 0 t ∧
      integralMarginalDerivative p (varianceHalf p) 0 t ≤ 8 := by
  let f (y : ℝ) := ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (t * (y * s))
  have hhalf : (∫ s in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    simpa using unit_weight_moment 0
  have hint (q : ℝ) :
      (∫ s in (0 : ℝ)..1, q * (1 - s)) = q * (1 / 2) := by
    rw [intervalIntegral.integral_const_mul, hhalf]
  have hlocal (g : Gap) (hg : g ∈ gaps p) :
      1 / 8 * (1 / 2) ≤ f (exponent p g.2.2) ∧
        f (exponent p g.2.2) ≤ 8 * (1 / 2) := by
    have hbounds (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        1 / 8 ≤ Real.exp (t * (exponent p g.2.2 * s)) ∧
          Real.exp (t * (exponent p g.2.2 * s)) ≤ 8 := by
      apply exp_bounded
      rw [abs_mul, abs_mul, abs_of_nonneg hs.1]
      calc
        _ ≤ (1 : ℝ) * (2 * 1) := by
          exact mul_le_mul ht
            (mul_le_mul (exponent_abs_le hp hg) hs.2 hs.1 (by norm_num))
            (mul_nonneg (abs_nonneg (exponent p g.2.2)) hs.1) (by norm_num)
        _ = _ := by norm_num
    have hfi : IntervalIntegrable
        (fun s : ℝ ↦ (1 - s) * Real.exp (t * (exponent p g.2.2 * s))) volume 0 1 :=
      (by fun_prop : Continuous _).intervalIntegrable 0 1
    have hci (q : ℝ) : IntervalIntegrable (fun s : ℝ ↦ q * (1 - s)) volume 0 1 :=
      (by fun_prop : Continuous _).intervalIntegrable 0 1
    constructor
    · rw [← hint]
      exact intervalIntegral.integral_mono_on zero_le_one (hci _) hfi fun s hs ↦ by
        rw [mul_comm (1/8 : ℝ)]
        exact mul_le_mul_of_nonneg_left (hbounds s hs).1 (sub_nonneg.mpr hs.2)
    · rw [← hint]
      exact intervalIntegral.integral_mono_on zero_le_one hfi (hci _) fun s hs ↦ by
        rw [mul_comm (8 : ℝ)]
        exact mul_le_mul_of_nonneg_left (hbounds s hs).2 (sub_nonneg.mpr hs.2)
  have hden := denominator_pos p
  simp only [integralMarginalDerivative, pow_zero, mul_one]
  change 1 / 8 ≤ ((gaps p).map fun g ↦ exponent p g.2.2 ^ 2 *
    f (exponent p g.2.2)).sum / denominator p ∧ _ ≤ 8
  rw [le_div_iff₀ hden, div_le_iff₀ hden]
  constructor
  · have h := sum_map_mono (gaps p) (fun g ↦ exponent p g.2.2 ^ 2 * (1 / 8 * (1 / 2))) _
      (fun g hg ↦ mul_le_mul_of_nonneg_left (hlocal g hg).1 (sq_nonneg _))
    rw [List.sum_map_mul_right, sum_marginal_square] at h
    linarith only [h]
  · have h := sum_map_mono (gaps p) _ (fun g ↦ exponent p g.2.2 ^ 2 * (8 * (1 / 2)))
      (fun g hg ↦ mul_le_mul_of_nonneg_left (hlocal g hg).2 (sq_nonneg _))
    rw [List.sum_map_mul_right, sum_marginal_square] at h
    linarith only [h]

#print axioms integralMarginalDerivative_sub_taylor_le
#print axioms integralMarginalDerivative_zero_mem

private theorem hasDerivAt_marginalFamily (p order : ℕ) (t : ℝ) :
    HasDerivAt (integralMarginalDerivative p (varianceHalf p) order)
      (integralMarginalDerivative p (varianceHalf p) (order + 1) t) t := by
  let f (k : ℕ) (g : Gap) (x : ℝ) := exponent p g.2.2 ^ 2 *
    ∫ s in (0 : ℝ)..1, (1 - s) * (exponent p g.2.2 * s) ^ k *
      Real.exp (x * (exponent p g.2.2 * s))
  have h (l : List Gap) :
      HasDerivAt (fun x ↦ (l.map fun g ↦ f order g x).sum)
        ((l.map fun g ↦ f (order + 1) g t).sum) t := by
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const t (0 : ℝ)
    | cons g l ih =>
      have hg : HasDerivAt (f order g) (f (order + 1) g t) t :=
        (hasDerivAt_exponential_moment_integral _ order t).const_mul _
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using hg.add ih
  exact (h (gaps p)).div_const _

/-- The continued divided differences and their partial derivatives integrate
a marginal derivative along the segment from `v` to `v-u`. -/
def weightedMarginalIntegral (f : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (k a b : ℕ) (u v : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, w r * (-r) ^ a * f (k + a + b) (v - r * u)

/-- The Taylor remainder transfers through a divided-difference integral
with either weight used in the positive-center regularization. -/
theorem weightedMarginalIntegral_sub_taylor_le {p : ℕ} (hp : 0 < p)
    {w : ℝ → ℝ} (hcontinuous : Continuous w) (hw : ∀ r ∈ Icc (0 : ℝ) 1, |w r| ≤ 1)
    {k a b : ℕ} (hk : k + a + b ≤ 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    |weightedMarginalIntegral (integralMarginalDerivative p (varianceHalf p)) w k a b u v -
      weightedMarginalIntegral (marginalTaylorPolynomial p) w k a b u v| ≤ 1 / (2 : ℝ) ^ 30 := by
  unfold weightedMarginalIntegral
  let F (r : ℝ) := integralMarginalDerivative p (varianceHalf p) (k + a + b) (v - r * u)
  let P (r : ℝ) := marginalTaylorPolynomial p (k + a + b) (v - r * u)
  let W (r : ℝ) := w r * (-r) ^ a
  change |(∫ r in (0 : ℝ)..1, W r * F r) - (∫ r in (0 : ℝ)..1, W r * P r)| ≤ _
  have hF : Continuous F := by
    unfold F
    have hd : Differentiable ℝ
        (integralMarginalDerivative p (varianceHalf p) (k + a + b)) :=
      fun x ↦ (hasDerivAt_marginalFamily p (k + a + b) x).differentiableAt
    exact hd.continuous.comp (by fun_prop)
  have hP : Continuous P := by unfold P marginalTaylorPolynomial; fun_prop
  have hW : Continuous W := by unfold W; fun_prop
  have hFI : IntervalIntegrable (fun r ↦ W r * F r) volume 0 1 :=
    (hW.mul hF).intervalIntegrable 0 1
  have hPI : IntervalIntegrable (fun r ↦ W r * P r) volume 0 1 :=
    (hW.mul hP).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hFI hPI, ← Real.norm_eq_abs]
  have hpoint (r : ℝ) (hr : r ∈ uIoc (0 : ℝ) 1) :
      ‖W r * F r - W r * P r‖ ≤ 1 / (2 : ℝ) ^ 30 := by
    rw [uIoc_of_le zero_le_one] at hr
    have harg : |v - r * u| ≤ 1 := by
      have hm₀ := mul_nonneg hr.1.le hu
      have hm₁ : r * u ≤ u := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hr.2 hu
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hweight : |W r| ≤ 1 := by
      rw [show W r = w r * (-r) ^ a from rfl, abs_mul, abs_pow, abs_neg, abs_of_nonneg hr.1.le]
      calc
        _ ≤ 1 * r ^ a := mul_le_mul_of_nonneg_right (hw r ⟨hr.1.le, hr.2⟩)
          (pow_nonneg hr.1.le _)
        _ ≤ _ := by
          rw [one_mul]
          exact pow_le_one₀ hr.1.le hr.2
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    simpa only [one_mul] using mul_le_mul hweight
      (integralMarginalDerivative_sub_taylor_le hp hk harg) (abs_nonneg _) (by norm_num)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpoint

#print axioms weightedMarginalIntegral_sub_taylor_le

/-- The continued, integral divided differences agree with the quotient forms
on the open ordered corner. -/
theorem D_Q_eq_weightedMarginalIntegral {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    D p (varianceHalf p) u v =
        weightedMarginalIntegral (integralMarginalDerivative p (varianceHalf p))
          (fun _ ↦ 1) 1 0 0 u v ∧
      Q p (varianceHalf p) u v =
        weightedMarginalIntegral (integralMarginalDerivative p (varianceHalf p))
          (fun r ↦ 1 - r) 2 0 0 u v := by
  have hc := (half_pos (compositionMarginalVariance_pos p)).ne'
  obtain ⟨hD, hQ⟩ := D_Q_eq_integrals p hc hu huv
  have ht (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) 1) : v - r * u ≠ 0 := by
    rw [uIcc_of_le zero_le_one] at hr
    have hm : r * u ≤ u := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hr.2 hu.le
    exact (show 0 < v - r * u by linarith).ne'
  simp only [weightedMarginalIntegral, pow_zero, mul_one, one_mul, Nat.add_zero]
  constructor
  · rw [hD]
    apply intervalIntegral.integral_congr
    intro r hr
    simpa only [iteratedDeriv_one] using iteratedDeriv_G_eq_integral hp hc (ht r hr) 1
  · rw [hQ]
    apply intervalIntegral.integral_congr
    intro r hr
    have h₂ : iteratedDeriv 2 (G p (varianceHalf p)) =
        deriv (deriv (G p (varianceHalf p))) := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have h := iteratedDeriv_G_eq_integral hp hc (ht r hr) 2
    rw [h₂] at h
    exact congrArg (fun x : ℝ ↦ (1 - r) * x) h

#print axioms D_Q_eq_weightedMarginalIntegral


/-- The polynomial family uses one fixed list of coefficients and successive
ordinary derivatives, as in the simultaneous Horner evaluation. -/
theorem hasDerivAt_marginalTaylorPolynomial (p k : ℕ) (t : ℝ) :
    HasDerivAt (marginalTaylorPolynomial p k) (marginalTaylorPolynomial p (k + 1) t) t := by
  by_cases hk : k < 23
  · let c (i : ℕ) := jointTaylorMoment p (k + i) 0 /
      ((i.factorial : ℝ) * (((k + i : ℕ) : ℝ) + 1) * (((k + i : ℕ) : ℝ) + 2))
    have h (i : ℕ) : HasDerivAt (fun x : ℝ ↦ c i * x ^ i)
        (c i * ((i : ℝ) * t ^ (i - 1))) t := (hasDerivAt_pow i t).const_mul _
    have hsum := HasDerivAt.fun_sum (u := Finset.range (23 - k)) (fun i _ ↦ h i)
    have heq (x : ℝ) :
        (∑ i ∈ Finset.range (23 - k), c i * x ^ i) = marginalTaylorPolynomial p k x := by
      unfold marginalTaylorPolynomial
      apply Finset.sum_congr rfl
      intro i _
      unfold c
      ring
    have hder :
        (∑ i ∈ Finset.range (23 - k), c i * ((i : ℝ) * t ^ (i - 1))) =
          marginalTaylorPolynomial p (k + 1) t := by
      rw [show 23 - k = (23 - (k + 1)) + 1 by omega, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      unfold marginalTaylorPolynomial
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [c]
      rw [show k + (i + 1) = k + 1 + i by omega, Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.add_sub_cancel, Nat.cast_succ]
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      field_simp [hi.ne'] <;> ring
    simp_rw [heq] at hsum
    exact hder ▸ hsum
  · have h₀ (x : ℝ) : marginalTaylorPolynomial p k x = 0 := by
      simp only [marginalTaylorPolynomial, show 23 - k = 0 by omega,
        Finset.range_zero, Finset.sum_empty]
    have h₁ : marginalTaylorPolynomial p (k + 1) t = 0 := by
      simp only [marginalTaylorPolynomial, show 23 - (k + 1) = 0 by omega,
        Finset.range_zero, Finset.sum_empty]
    rw [show marginalTaylorPolynomial p k = fun _ ↦ 0 from funext h₀, h₁]
    exact hasDerivAt_const t (0 : ℝ)

#print axioms hasDerivAt_marginalTaylorPolynomial


private theorem hasDerivAt_weighted_comp_integral
    {w g dg a b : ℝ → ℝ} (hw : Continuous w) (ha : Continuous a) (hb : Continuous b)
    (hdg : Continuous dg) (hg : ∀ t, HasDerivAt g (dg t) t) (t : ℝ) :
    HasDerivAt (fun x ↦ ∫ r in (0 : ℝ)..1, w r * g (a r * x + b r))
      (∫ r in (0 : ℝ)..1, w r * dg (a r * t + b r) * a r) t := by
  let f (x r : ℝ) := w r * g (a r * x + b r)
  let df (x r : ℝ) := w r * dg (a r * x + b r) * a r
  let parameters := Icc (t - 1) (t + 1)
  have hcompact : IsCompact (parameters ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hgc : Continuous g :=
    (show Differentiable ℝ g from fun x ↦ (hg x).differentiableAt).continuous
  have hcontinuous : Continuous (fun z : ℝ × ℝ ↦ df z.1 z.2) := by
    unfold df
    fun_prop
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcontinuous.continuousOn
  have hnbhd : parameters ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hf (x : ℝ) : Continuous (f x) := by unfold f; fun_prop
  have hdf (x : ℝ) : Continuous (df x) := by unfold df; fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := f) (F' := df) (bound := fun _ ↦ C)
    hnbhd (.of_forall fun x ↦ (hf x).aestronglyMeasurable)
    ((hf t).intervalIntegrable 0 1) (hdf t).aestronglyMeasurable ?_
    (continuous_const.intervalIntegrable 0 1) ?_).2
  · filter_upwards with r hr x hx
    have hr' : r ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hr
      exact ⟨hr.1.le, hr.2⟩
    exact hC (x, r) ⟨hx, hr'⟩
  · filter_upwards with r _ x _
    have hax : HasDerivAt (fun y : ℝ ↦ a r * y + b r) (a r) x := by
      simpa only [mul_one] using (((hasDerivAt_id' x).const_mul (a r)).add_const (b r))
    have h := ((hg (a r * x + b r)).comp x hax).const_mul (w r)
    apply h.congr_deriv
    dsimp only [df]
    ring

private theorem hasDerivAt_weightedMarginalIntegral_fst
    {f : ℕ → ℝ → ℝ} (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    {w : ℝ → ℝ} (hw : Continuous w) (k a b : ℕ) (u v : ℝ) :
    HasDerivAt (fun x ↦ weightedMarginalIntegral f w k a b x v)
      (weightedMarginalIntegral f w k (a + 1) b u v) u := by
  have hc : Continuous (f (k + a + b + 1)) :=
    (show Differentiable ℝ (f (k + a + b + 1)) from fun x ↦
      (hf (k + a + b + 1) x).differentiableAt).continuous
  have h := hasDerivAt_weighted_comp_integral
    (w := fun r ↦ w r * (-r) ^ a) (a := fun r ↦ -r) (b := fun _ ↦ v)
    (by fun_prop) (by fun_prop) continuous_const hc (hf (k + a + b)) u
  simp only [weightedMarginalIntegral,
    show k + (a + 1) + b = k + a + b + 1 by omega, pow_succ]
  convert h using 1
  · funext x
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [show v - r * x = -r * x + v by ring]
  · apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [show v - r * u = -r * u + v by ring]
    ring

private theorem hasDerivAt_weightedMarginalIntegral_snd
    {f : ℕ → ℝ → ℝ} (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    {w : ℝ → ℝ} (hw : Continuous w) (k a b : ℕ) (u v : ℝ) :
    HasDerivAt (weightedMarginalIntegral f w k a b u)
      (weightedMarginalIntegral f w k a (b + 1) u v) v := by
  have hc : Continuous (f (k + a + b + 1)) :=
    (show Differentiable ℝ (f (k + a + b + 1)) from fun x ↦
      (hf (k + a + b + 1) x).differentiableAt).continuous
  have h := hasDerivAt_weighted_comp_integral
    (w := fun r ↦ w r * (-r) ^ a) (a := fun _ ↦ 1) (b := fun r ↦ -(r * u))
    (by fun_prop) continuous_const (by fun_prop) hc (hf (k + a + b)) v
  change HasDerivAt (fun y ↦ weightedMarginalIntegral f w k a b u y)
    (weightedMarginalIntegral f w k a (b + 1) u v) v
  simpa only [weightedMarginalIntegral, Nat.add_assoc, one_mul, mul_one, ← sub_eq_add_neg] using h

/-- The value and partials of either divided difference, ordered as in the
mixed-jet interval certificate. -/
def weightedMarginalJet (f : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (k : ℕ) (u v : ℝ) : MixedJet ℝ :=
  ⟨weightedMarginalIntegral f w k 0 0 u v,
    weightedMarginalIntegral f w k 1 0 u v,
    weightedMarginalIntegral f w k 0 1 u v,
    weightedMarginalIntegral f w k 1 1 u v⟩

theorem weightedMarginalJet_isAt {f : ℕ → ℝ → ℝ}
    (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    {w : ℝ → ℝ} (hw : Continuous w) (k : ℕ) (u v : ℝ) :
    MixedJet.IsAt (weightedMarginalJet f w k) u v :=
  ⟨Eventually.of_forall (fun y ↦ hasDerivAt_weightedMarginalIntegral_fst hf hw k 0 0 u y),
    hasDerivAt_weightedMarginalIntegral_snd hf hw k 0 0 u v,
    hasDerivAt_weightedMarginalIntegral_snd hf hw k 1 0 u v⟩

theorem integralMarginalJet_isAt (p : ℕ) {w : ℝ → ℝ} (hw : Continuous w)
    (k : ℕ) (u v : ℝ) :
    MixedJet.IsAt (weightedMarginalJet (integralMarginalDerivative p (varianceHalf p)) w k) u v :=
  weightedMarginalJet_isAt (hasDerivAt_marginalFamily p) hw k u v

#print axioms integralMarginalJet_isAt


/-- Value and partials of a marginal derivative evaluated on an affine gap. -/
def affineMarginalJet (f : ℕ → ℝ → ℝ) (k : ℕ) (a b u v : ℝ) : MixedJet ℝ :=
  let t := a * u + b * v
  ⟨f k t, a * f (k + 1) t, b * f (k + 1) t, a * b * f (k + 2) t⟩

theorem affineMarginalJet_isAt
    {f : ℕ → ℝ → ℝ} (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (k : ℕ) (a b u v : ℝ) : MixedJet.IsAt (affineMarginalJet f k a b) u v := by
  have hu (y : ℝ) : HasDerivAt (fun x ↦ a * x + b * y) a u := by
    simpa only [mul_one] using ((hasDerivAt_id' u).const_mul a).add_const (b * y)
  have hv : HasDerivAt (fun y ↦ a * u + b * y) b v := by
    simpa only [mul_one] using ((hasDerivAt_id' v).const_mul b).const_add (a * u)
  refine ⟨Eventually.of_forall ?_, ?_, ?_⟩
  · intro y
    exact ((hf k (a * u + b * y)).comp u (hu y)).congr_deriv (mul_comm _ _)
  · exact ((hf k (a * u + b * v)).comp v hv).congr_deriv (mul_comm _ _)
  · change HasDerivAt (fun y ↦ a * f (k + 1) (a * u + b * y))
      (a * b * f (k + 2) (a * u + b * v)) v
    exact ((((hf (k + 1) (a * u + b * v)).comp v hv).const_mul a).congr_deriv
      (by change a * (f (k + 2) (a * u + b * v) * b) = _; ring))

theorem continuedMarginalJet_isAt (p k : ℕ) (a b u v : ℝ) :
    MixedJet.IsAt (affineMarginalJet (integralMarginalDerivative p (varianceHalf p)) k a b) u v :=
  affineMarginalJet_isAt (hasDerivAt_marginalFamily p) k a b u v


end RefinedBMV.PositiveCenter.SmallCorner
