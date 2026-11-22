/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/JointTaylor
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform joint Taylor errors for the two-coordinate regularized BMV moment. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.Regularized
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.Moments

/-! # The joint Taylor enclosure on the closed small corner -/

noncomputable section

namespace RefinedBMV.PositiveCenter.SmallCorner

open DimThree (gaps gaps_cycle_all mem_gaps_iff_total word_counts_all)
open Filter MeasureTheory Set

private abbrev Gap := ℕ × ℕ × ℕ

private def gapExponent (p j : ℕ) : ℝ := 3 * (j : ℝ) / p - 1

private def jointAverage (p : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ((gaps p).map fun g ↦
    (gapExponent p g.2.1) ^ 2 * f (gapExponent p g.2.1) (gapExponent p g.2.2)).sum /
    (((gaps p).length : ℝ) * (compositionMarginalVariance p / 2))

/-- The joint moment after differentiation in the two coordinates, continued to zero. -/
def integralJointDerivative (p a b : ℕ) (u v : ℝ) : ℝ :=
  jointAverage p fun x y ↦ y ^ b * Real.exp (y * v) *
    ∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * Real.exp (u * (x * s))

private def jointTaylorSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ i / (i.factorial : ℝ)

private def integratedJointTaylor (p a b : ℕ) (u v : ℝ) : ℝ :=
  jointAverage p fun x y ↦
    ∫ s in (0 : ℝ)..1,
      (1 - s) * (x * s) ^ a * y ^ b * jointTaylorSeries (23 - a - b) (u * (x * s) + y * v)

private theorem factor_joint_integral (a b : ℕ) (x y u v : ℝ) :
    y ^ b * Real.exp (y * v) *
        (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * Real.exp (u * (x * s))) =
      ∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * y ^ b * Real.exp (u * (x * s) + y * v) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [Real.exp_add]
  ring

private theorem abs_gapExponent_le {p j : ℕ} (hp : 0 < p) (hj : j ≤ p) :
    |gapExponent p j| ≤ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hjR : (j : ℝ) ≤ p := by exact_mod_cast hj
  have h₀ : 0 ≤ 3 * (j : ℝ) / (p : ℝ) := by positivity
  have h₁ : 3 * (j : ℝ) / (p : ℝ) ≤ 3 := (div_le_iff₀ hpR).2 (by linarith)
  exact abs_le.2 ⟨by unfold gapExponent; linarith, by unfold gapExponent; linarith⟩

private theorem joint_integral_error {p : ℕ} (hp : 0 < p)
    {g : Gap} (hg : g ∈ gaps p) {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    let x := gapExponent p g.2.1
    let y := gapExponent p g.2.2
    |y ^ b * Real.exp (y * v) *
        (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * Real.exp (u * (x * s))) -
      (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * y ^ b *
        jointTaylorSeries (23 - a - b) (u * (x * s) + y * v))| ≤ 1 / (2 : ℝ) ^ 31 := by
  dsimp only
  rw [factor_joint_integral]
  let x := gapExponent p g.2.1
  let y := gapExponent p g.2.2
  let z (s : ℝ) := u * (x * s) + y * v
  let w (s : ℝ) := (1 - s) * (x * s) ^ a * y ^ b
  let pol := jointTaylorSeries (23 - a - b)
  change |(∫ s in (0 : ℝ)..1, w s * Real.exp (z s)) -
    (∫ s in (0 : ℝ)..1, w s * pol (z s))| ≤ _
  have hexp : IntervalIntegrable (fun s ↦ w s * Real.exp (z s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [w, z]
    fun_prop
  have hpol : IntervalIntegrable (fun s ↦ w s * pol (z s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [w, z, pol, jointTaylorSeries]
    fun_prop
  rw [← intervalIntegral.integral_sub hexp hpol]
  let ε : ℝ := 1 / (2 : ℝ) ^ 30
  have hε : IntervalIntegrable (fun s ↦ ε * (1 - s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htotal := (mem_gaps_iff_total p g).mp hg
  have hx : |x| ≤ 2 := abs_gapExponent_le hp (by omega)
  have hy : |y| ≤ 2 := abs_gapExponent_le hp (by omega)
  have hbound : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖w s * Real.exp (z s) - w s * pol (z s)‖ ≤ ε * (1 - s) := by
    intro s hs
    have hs₀ : 0 ≤ s := hs.1.le
    have hs₁ : s ≤ 1 := hs.2
    have hus : u * s ≤ v := (mul_le_of_le_one_right hu hs₁).trans huv
    have hxs : |x * s| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg hs₀]
      exact (mul_le_of_le_one_right (abs_nonneg _) hs₁).trans hx
    have ha' : |x * s| ^ a ≤ 2 :=
      (pow_le_pow_left₀ (abs_nonneg _) hxs a).trans
        (by simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) ha)
    have hb' : |y| ^ b ≤ 2 :=
      (pow_le_pow_left₀ (abs_nonneg _) hy b).trans
        (by simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hb)
    have hz : z s = x * (u * s) + y * v := by dsimp only [z]; ring
    have herr : 16 * |Real.exp (z s) - pol (z s)| ≤ ε := by
      rw [hz]
      exact composition_exp_remainder_le hp hg (mul_nonneg hu hs₀) hus hv
        (n := 23 - a - b) (by omega)
    have hw : |x * s| ^ a * |y| ^ b ≤ 16 := by
      calc
        _ ≤ (2 : ℝ) * 2 :=
          mul_le_mul ha' hb' (pow_nonneg (abs_nonneg _) _) (by norm_num)
        _ ≤ _ := by norm_num
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    have hwabs : |w s| = (1 - s) * (|x * s| ^ a * |y| ^ b) := by
      change |(1 - s) * (x * s) ^ a * y ^ b| = _
      rw [abs_mul, abs_mul ((1 - s)) ((x * s) ^ a), abs_of_nonneg (sub_nonneg.mpr hs₁),
        abs_pow, abs_pow, mul_assoc]
    rw [hwabs]
    calc
      _ = (1 - s) * ((|x * s| ^ a * |y| ^ b) * |Real.exp (z s) - pol (z s)|) := by ring
      _ ≤ (1 - s) * ε := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans herr) (sub_nonneg.mpr hs₁)
      _ = _ := mul_comm _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall hbound) hε
  have hhalf : (∫ s in (0 : ℝ)..1, 1 - s) = 1 / 2 := by
    simpa using unit_weight_moment 0
  rw [intervalIntegral.integral_const_mul, hhalf, Real.norm_eq_abs] at h
  convert h using 1
  norm_num [ε]

private theorem abs_sum_map_sub_le {α : Type*} (l : List α) (f g e : α → ℝ)
    (h : ∀ i ∈ l, |f i - g i| ≤ e i) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map e).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [show f i + (l.map f).sum - (g i + (l.map g).sum) =
      (f i - g i) + ((l.map f).sum - (l.map g).sum) by ring]
    exact (abs_add_le _ _).trans (add_le_add (h i (by simp))
      (ih fun j hj ↦ h j (List.mem_cons_of_mem _ hj)))

private theorem sum_first_square_eq (p : ℕ) :
    ((gaps p).map fun g ↦ (gapExponent p g.2.1) ^ 2).sum =
      ((gaps p).length : ℝ) * compositionMarginalVariance p := by
  have h := ((gaps_cycle_all p).map fun g ↦ (gapExponent p g.2.1) ^ 2).sum_eq
  simp only [List.map_map, Function.comp_def] at h
  rw [← h]
  unfold compositionMarginalVariance gapExponent
  have hN : ((gaps p).length : ℝ) ≠ 0 := by
    exact_mod_cast (word_counts_all p).2.1.ne'
  field_simp [hN]

/-- The regularized joint moment and each first or mixed partial have the same
uniform absolute error bound when truncating the exponential at degree `22-a-b`. -/
theorem integralJointDerivative_sub_integratedJointTaylor_le {p a b : ℕ} (hp : 0 < p)
    (ha : a ≤ 1) (hb : b ≤ 1) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    |integralJointDerivative p a b u v - integratedJointTaylor p a b u v| ≤ 1 / (2 : ℝ) ^ 30 := by
  let f (x y : ℝ) := y ^ b * Real.exp (y * v) *
    ∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * Real.exp (u * (x * s))
  let g (x y : ℝ) := ∫ s in (0 : ℝ)..1,
    (1 - s) * (x * s) ^ a * y ^ b * jointTaylorSeries (23 - a - b) (u * (x * s) + y * v)
  let x (i : Gap) := gapExponent p i.2.1
  let y (i : Gap) := gapExponent p i.2.2
  let N : ℝ := (gaps p).length
  let c := compositionMarginalVariance p / 2
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (word_counts_all p).2.1
  have hc : 0 < c := half_pos (compositionMarginalVariance_pos p)
  have hden : 0 < N * c := mul_pos hN hc
  change |((gaps p).map (fun i ↦ x i ^ 2 * f (x i) (y i))).sum / (N * c) -
    ((gaps p).map (fun i ↦ x i ^ 2 * g (x i) (y i))).sum / (N * c)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine (abs_sum_map_sub_le _ _ _ (fun i ↦ x i ^ 2 * (1 / (2 : ℝ) ^ 31)) ?_).trans ?_
  · intro i hi
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (joint_integral_error hp hi ha hb hu huv hv) (sq_nonneg _)
  · simp only [List.sum_map_mul_right, x, sum_first_square_eq]
    change N * compositionMarginalVariance p * (1 / (2 : ℝ) ^ 31) ≤ 1 / (2 : ℝ) ^ 30 * (N * c)
    dsimp only [c]
    apply le_of_eq
    ring

private theorem hasDerivAt_jointAverage (p : ℕ) {t : ℝ}
    {f : ℝ → ℝ → ℝ → ℝ} {df : ℝ → ℝ → ℝ}
    (h : ∀ x y, HasDerivAt (f x y) (df x y) t) :
    HasDerivAt (fun z ↦ jointAverage p (fun x y ↦ f x y z)) (jointAverage p df) t := by
  let x (g : Gap) := gapExponent p g.2.1
  let y (g : Gap) := gapExponent p g.2.2
  have hsum (l : List Gap) :
      HasDerivAt (fun z ↦ (l.map fun g ↦ x g ^ 2 * f (x g) (y g) z).sum)
        ((l.map fun g ↦ x g ^ 2 * df (x g) (y g)).sum) t := by
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const t (0 : ℝ)
    | cons g l ih =>
      simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
        ((h (x g) (y g)).const_mul (x g ^ 2)).add ih
  exact (hsum (gaps p)).div_const _

/-- Differentiation of the continued joint moment in its first coordinate. -/
theorem hasDerivAt_integralJointDerivative_fst (p a b : ℕ) (u v : ℝ) :
    HasDerivAt (fun t ↦ integralJointDerivative p a b t v)
      (integralJointDerivative p (a + 1) b u v) u := by
  unfold integralJointDerivative
  apply hasDerivAt_jointAverage
  intro x y
  exact (hasDerivAt_exponential_moment_integral x a u).const_mul (y ^ b * Real.exp (y * v))

/-- Differentiation of the continued joint moment in its second coordinate. -/
theorem hasDerivAt_integralJointDerivative_snd (p a b : ℕ) (u v : ℝ) :
    HasDerivAt (integralJointDerivative p a b u)
      (integralJointDerivative p a (b + 1) u v) v := by
  unfold integralJointDerivative
  apply hasDerivAt_jointAverage
  intro x y
  let I := ∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * Real.exp (u * (x * s))
  change HasDerivAt (fun t ↦ y ^ b * Real.exp (y * t) * I)
    (y ^ (b + 1) * Real.exp (y * v) * I) v
  rw [pow_succ]
  convert ((((hasDerivAt_const_mul (x := v) y).exp).const_mul (y ^ b)).mul_const I) using 1
  ring

/-- The integral continuation agrees with the original quotient away from zero. -/
theorem A_eq_integralJointDerivative {p : ℕ} {u v : ℝ} (hu : u ≠ 0) :
    A p (compositionMarginalVariance p / 2) u v = integralJointDerivative p 0 0 u v := by
  rw [A_eq_integral_average p (half_pos (compositionMarginalVariance_pos p)).ne' hu]
  have h (x s : ℝ) : x * u * s = u * (x * s) := by ring
  simp only [integralJointDerivative, jointAverage, gapExponent, pow_zero, mul_one, one_mul, h,
    mul_assoc]

/-- The normalized exact joint power moment, including the quadratic weight in the
first coordinate. -/
def jointTaylorMoment (p r s : ℕ) : ℝ :=
  jointAverage p (fun x y ↦ x ^ r * y ^ s)

private def taylorMonomial (i j : ℕ) (u v : ℝ) : ℝ :=
  u ^ i * v ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))

private def unitWeightMoment (k : ℕ) : ℝ :=
  1 / ((((k : ℕ) : ℝ) + 1) * ((k : ℝ) + 2))

/-- The differentiated joint Taylor polynomial through total degree `22-a-b`.
For a term of bidegree `(i,j)`, the integrated weight is
`1 / ((a+i+1)(a+i+2))`. -/
def jointTaylorPolynomial (p a b : ℕ) (u v : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (23 - a - b), ∑ i ∈ Finset.range (m + 1),
    jointTaylorMoment p (a + i) (b + (m - i)) *
      (taylorMonomial i (m - i) u v * unitWeightMoment (a + i))

private theorem expand_joint_exponential_term (m a b : ℕ) (x y u v s : ℝ) :
    (1 - s) * (x * s) ^ a * y ^ b *
        ((u * (x * s) + y * v) ^ m / (m.factorial : ℝ)) =
      ∑ i ∈ Finset.range (m + 1), (x ^ (a + i) * y ^ (b + (m - i)) *
        taylorMonomial i (m - i) u v) * ((1 - s) * s ^ (a + i)) := by
  rw [add_pow, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hchoose : (m.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos him).ne'
  have hfac : (m.choose i : ℝ) * (i.factorial : ℝ) * ((m - i).factorial : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial him
  rw [← hfac]
  simp only [taylorMonomial, mul_pow, pow_add]
  have hi₀ : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj₀ : ((m - i).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hchoose, hi₀, hj₀]

private theorem integral_jointTaylor_eq (a b : ℕ) (x y u v : ℝ) :
    (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ a * y ^ b *
        jointTaylorSeries (23 - a - b) (u * (x * s) + y * v)) =
      ∑ m ∈ Finset.range (23 - a - b), ∑ i ∈ Finset.range (m + 1),
        (x ^ (a + i) * y ^ (b + (m - i))) *
          (taylorMonomial i (m - i) u v * unitWeightMoment (a + i)) := by
  simp only [jointTaylorSeries, Finset.mul_sum]
  simp_rw [expand_joint_exponential_term]
  rw [intervalIntegral.integral_finsetSum (fun m _ ↦
    (show Continuous (fun s : ℝ ↦ ∑ i ∈ Finset.range (m + 1),
      (x ^ (a + i) * y ^ (b + (m - i)) * taylorMonomial i (m - i) u v) *
        ((1 - s) * s ^ (a + i))) from by fun_prop).intervalIntegrable 0 1)]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [intervalIntegral.integral_finsetSum (fun i _ ↦
    (show Continuous (fun s : ℝ ↦
      (x ^ (a + i) * y ^ (b + (m - i)) * taylorMonomial i (m - i) u v) *
        ((1 - s) * s ^ (a + i))) from by fun_prop).intervalIntegrable 0 1)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [intervalIntegral.integral_const_mul, unit_weight_moment, unitWeightMoment, mul_assoc]

private theorem jointAverage_finsetSum {ι : Type*} (p : ℕ) (s : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) :
    jointAverage p (fun x y ↦ ∑ i ∈ s, f i x y) =
      ∑ i ∈ s, jointAverage p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jointAverage]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih]
    simp only [jointAverage, mul_add, List.sum_map_add, add_div]

private theorem jointAverage_mul (p : ℕ) (f : ℝ → ℝ → ℝ) (c : ℝ) :
    jointAverage p (fun x y ↦ f x y * c) = jointAverage p f * c := by
  simp only [jointAverage, ← mul_assoc, List.sum_map_mul_right]
  ring

private theorem integratedJointTaylor_eq_polynomial (p a b : ℕ) (u v : ℝ) :
    integratedJointTaylor p a b u v = jointTaylorPolynomial p a b u v := by
  simp only [integratedJointTaylor, integral_jointTaylor_eq, jointTaylorPolynomial,
    jointAverage_finsetSum, jointAverage_mul, jointTaylorMoment]

/-- The value and both first partials and the mixed partial of the continued joint
moment are enclosed by their Taylor polynomials on the entire ordered triangle. -/
theorem integralJointDerivative_sub_jointTaylorPolynomial_le {p a b : ℕ} (hp : 0 < p)
    (ha : a ≤ 1) (hb : b ≤ 1) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    |integralJointDerivative p a b u v - jointTaylorPolynomial p a b u v| ≤ 1 / (2 : ℝ) ^ 30 := by
  rw [← integratedJointTaylor_eq_polynomial]
  exact integralJointDerivative_sub_integratedJointTaylor_le hp ha hb hu huv hv

/-- The four joint enclosures for the continued `A`, with the mixed derivative
taken first in `u` and then in `v`. -/
theorem A_jointTaylor_enclosures {p : ℕ} (hp : 0 < p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    let A₀ := integralJointDerivative p 0 0
    |A₀ u v - jointTaylorPolynomial p 0 0 u v| ≤ 1 / (2 : ℝ) ^ 30 ∧
    |deriv (fun t ↦ A₀ t v) u - jointTaylorPolynomial p 1 0 u v| ≤ 1 / (2 : ℝ) ^ 30 ∧
    |deriv (A₀ u) v - jointTaylorPolynomial p 0 1 u v| ≤ 1 / (2 : ℝ) ^ 30 ∧
    |deriv (fun s ↦ deriv (fun t ↦ A₀ t s) u) v -
      jointTaylorPolynomial p 1 1 u v| ≤ 1 / (2 : ℝ) ^ 30 := by
  dsimp only
  simp_rw [(hasDerivAt_integralJointDerivative_fst p 0 0 _ _).deriv,
    (hasDerivAt_integralJointDerivative_snd p 0 0 _ _).deriv,
    (hasDerivAt_integralJointDerivative_snd p 1 0 _ _).deriv]
  exact ⟨integralJointDerivative_sub_jointTaylorPolynomial_le hp (by decide) (by decide) hu huv hv,
    integralJointDerivative_sub_jointTaylorPolynomial_le hp (by decide) (by decide) hu huv hv,
    integralJointDerivative_sub_jointTaylorPolynomial_le hp (by decide) (by decide) hu huv hv,
    integralJointDerivative_sub_jointTaylorPolynomial_le hp (by decide) (by decide) hu huv hv⟩

private theorem real_pow_eq_stirling_sum (j k n : ℕ) (hk : k ≤ n) :
    (j : ℝ) ^ k = ∑ i ∈ Finset.range (n + 1),
      (Nat.stirlingSecond k i : ℝ) * (j.descFactorial i : ℝ) := by
  have h := congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial j k)
  simp only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] at h
  rw [h]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk)) fun i _ hi ↦ ?_
  have hki : k < i := by rw [Finset.mem_range, not_lt] at hi; omega
  simp [Nat.stirlingSecond_eq_zero_of_lt hki]

/-- Coefficient of the falling factorial of order `i` in the centered power of degree `k`. -/
def centeredFallingCoefficient (p k i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (3 / (p : ℝ)) ^ j * (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (Nat.stirlingSecond j i : ℝ)

private theorem gapExponent_pow_eq_falling (p j k : ℕ) :
    gapExponent p j ^ k =
      ∑ i ∈ Finset.range (k + 1), centeredFallingCoefficient p k i * (j.descFactorial i : ℝ) := by
  rw [show gapExponent p j = (3 / (p : ℝ)) * (j : ℝ) + (-1) by unfold gapExponent; ring,
    add_pow]
  simp only [centeredFallingCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  rw [mul_pow, real_pow_eq_stirling_sum j l k hlk]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

private theorem list_sum_map_finsetSum {α ι : Type*} (l : List α) (s : Finset ι)
    (f : α → ι → ℝ) :
    (l.map fun g ↦ ∑ i ∈ s, f g i).sum = ∑ i ∈ s, (l.map fun g ↦ f g i).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The exact coefficient moments reduce to Stirling numbers and the joint
falling-factorial sums, with the same quadratic normalization as the enclosure. -/
theorem jointTaylorMoment_eq_falling (p r s : ℕ) :
    jointTaylorMoment p r s =
      (∑ i ∈ Finset.range (r + 2 + 1), ∑ j ∈ Finset.range (s + 1),
        (centeredFallingCoefficient p (r + 2) i * centeredFallingCoefficient p s j) *
          ((i.factorial : ℝ) * (j.factorial : ℝ) * ((p + 2).choose (i + j + 2) : ℝ))) /
        (((gaps p).length : ℝ) * (compositionMarginalVariance p / 2)) := by
  unfold jointTaylorMoment jointAverage
  congr 1
  have hterm (g : Gap) :
      gapExponent p g.2.1 ^ 2 * (gapExponent p g.2.1 ^ r * gapExponent p g.2.2 ^ s) =
        ∑ i ∈ Finset.range (r + 2 + 1), ∑ j ∈ Finset.range (s + 1),
          (centeredFallingCoefficient p (r + 2) i * centeredFallingCoefficient p s j) *
            ((g.2.1.descFactorial i : ℝ) * (g.2.2.descFactorial j : ℝ)) := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm 2 r,
      gapExponent_pow_eq_falling p g.2.1 (r + 2), gapExponent_pow_eq_falling p g.2.2 s,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [hterm, list_sum_map_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [List.sum_map_mul_left]
  congr 1
  have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (sum_gaps_mul_descFactorial p i j)
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_mul] using h

/-- The quadratic normalization is `(1 + h) / 4` at `h = 3 / p`. -/
theorem joint_normalization_eq {p : ℕ} (hp : 0 < p) :
    compositionMarginalVariance p / 2 = (1 + 3 / (p : ℝ)) / 4 := by
  have h := (centered_marginal_sums hp).2
  dsimp only at h
  unfold compositionMarginalVariance
  rw [h]
  have hN : ((gaps p).length : ℝ) ≠ 0 := by exact_mod_cast (word_counts_all p).2.1.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hN, hpR]
  ring

#print axioms jointTaylorMoment_eq_falling
#print axioms joint_normalization_eq

#print axioms A_jointTaylor_enclosures
#print axioms A_eq_integralJointDerivative

#print axioms integralJointDerivative_sub_integratedJointTaylor_le

end RefinedBMV.PositiveCenter.SmallCorner
