/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapProfile
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover the short-gap curvature and slope from the scalar sign tests. -/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The scalar curvature and endpoint slope tests for the positive-center short-gap profile. -/

@[expose] public section

open Set
open scoped BigOperators

noncomputable section

namespace RefinedBMV.PositiveCenter

/-- The finite geometric part of the short-gap profile, continued through zero. -/
def shortGapProfileT (p : ℕ) (h t : ℝ) : ℝ :=
  h * (∑ l ∈ Finset.range (p + 1), Real.exp ((h * l - 3 / 2) * t)) -
    Real.exp (-(3 / 2 + h) * t) / 4

/-- The scalar curvature test with the square roots eliminated. -/
def shortGapProfileD (T U : ℝ → ℝ) (t : ℝ) : ℝ :=
  16 * U t ^ 3 * (deriv (deriv T) t - 1 / 200) ^ 2 -
    (4 * U t * deriv U t + t * (2 * U t * deriv (deriv U) t - (deriv U t) ^ 2)) ^ 2

/-- The scalar slope test with the square roots eliminated. -/
def shortGapProfileH (T U : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2 * U t + t * deriv U t) ^ 2 - 4 * U t * (deriv T t) ^ 2

private theorem hasDerivAt_exp_monomial (a : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun x ↦ a ^ k * Real.exp (a * x))
      (a ^ (k + 1) * Real.exp (a * t)) t := by
  convert (((hasDerivAt_id' t).const_mul a).exp.const_mul (a ^ k)) using 1
  simp only [pow_succ, mul_one]
  ring

private def profileMoment (p : ℕ) (h : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  h * (∑ l ∈ Finset.range (p + 1), (h * l - 3 / 2) ^ k *
      Real.exp ((h * l - 3 / 2) * t)) -
    (-(3 / 2 + h)) ^ k * Real.exp (-(3 / 2 + h) * t) / 4

private theorem hasDerivAt_profileMoment (p : ℕ) (h : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (profileMoment p h k) (profileMoment p h (k + 1) t) t :=
  ((HasDerivAt.fun_sum (u := Finset.range (p + 1))
    fun l _ ↦ hasDerivAt_exp_monomial (h * l - 3 / 2) k t).const_mul h).fun_sub
      ((hasDerivAt_exp_monomial (-(3 / 2 + h)) k t).div_const 4)

private theorem deriv_shortGapProfileT (p : ℕ) (h : ℝ) :
    deriv (shortGapProfileT p h) = profileMoment p h 1 := by
  have hzero : profileMoment p h 0 = shortGapProfileT p h := by
    funext t
    simp [profileMoment, shortGapProfileT]
  rw [← hzero]
  exact funext fun t ↦ (hasDerivAt_profileMoment p h 0 t).deriv

private theorem profileExp_hasSum (a t : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ ↦ a^(n+k) * (t^n / (n.factorial : ℝ)))
      (a^k * Real.exp (a*t)) := by
  rw [Real.exp_eq_exp_ℝ]
  refine ((NormedSpace.expSeries_div_hasSum_exp (a*t)).mul_left (a^k)).congr_fun fun n ↦ ?_
  rw [mul_pow, pow_add]
  ring

private theorem profileMoment_hasSum (p : ℕ) (h t : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ ↦
      (h*(∑ l ∈ Finset.range (p+1), (h*l-3/2)^(n+k)) - (-(3/2+h))^(n+k)/4) *
        (t^n/(n.factorial : ℝ))) (profileMoment p h k t) := by
  have hs : HasSum (fun n : ℕ ↦ ∑ l ∈ Finset.range (p+1),
      (h*l-3/2)^(n+k) * (t^n/(n.factorial : ℝ)))
      (∑ l ∈ Finset.range (p+1), (h*l-3/2)^k*Real.exp ((h*l-3/2)*t)) := by
    exact hasSum_sum fun l _ ↦ profileExp_hasSum (h*l-3/2) t k
  refine ((hs.mul_left h).sub ((profileExp_hasSum (-(3/2+h)) t k).div_const 4)).congr_fun
    fun n ↦ ?_
  simp only [← Finset.sum_mul]
  ring

/-- The finite exponential profile and its first two derivatives have
Taylor coefficients given by the shifted grid moments. -/
theorem shortGapProfileT_series (p : ℕ) (h t : ℝ) :
    let a (n k : ℕ) := (h*(∑ l ∈ Finset.range (p+1), (h*l-3/2)^(n+k)) -
      (-(3/2+h))^(n+k)/4) * (t^n/(n.factorial : ℝ))
    HasSum (fun n ↦ a n 0) (shortGapProfileT p h t) ∧
    HasSum (fun n ↦ a n 1) (deriv (shortGapProfileT p h) t) ∧
    HasSum (fun n ↦ a n 2) (deriv (deriv (shortGapProfileT p h)) t) := by
  dsimp only
  rw [deriv_shortGapProfileT, (hasDerivAt_profileMoment p h 1 t).deriv]
  have hzero : profileMoment p h 0 t = shortGapProfileT p h t := by
    simp [profileMoment, shortGapProfileT]
  exact ⟨hzero ▸ profileMoment_hasSum p h t 0, profileMoment_hasSum p h t 1,
    profileMoment_hasSum p h t 2⟩

/-- The coefficient of degree `n` in the `k`th derivative of the exponential profile. -/
def geometricCoeff (p : ℕ) (h : ℝ) (k n : ℕ) : ℝ :=
  (h*(∑ l ∈ Finset.range (p+1), (h*l-3/2)^(n+k)) -
    (-(3/2+h))^(n+k)/4) / (n.factorial : ℝ)

private theorem geometricCoeff_majorant {p : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hhmax : h ≤ 3/11) (hgrid : h*(p : ℝ) = 3) (k n : ℕ) :
    |geometricCoeff p h k n| ≤
      ((3+h)*(3/2)^k+(9/5)^k/4) *((9/5)^n/(n.factorial : ℝ)) := by
  let a (l : ℕ) := h*(l : ℝ)-3/2
  let g := -(3/2+h)
  have hb (l : ℕ) (hl : l ∈ Finset.range (p+1)) : |a l| ≤ 3/2 := by
    have hlp : (l : ℝ) ≤ p := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hm := mul_le_mul_of_nonneg_left hlp hh
    rw [hgrid] at hm
    exact abs_le.mpr ⟨by dsimp [a]; linarith [mul_nonneg hh (Nat.cast_nonneg l)],
      by dsimp [a]; linarith⟩
  have hg : |g| ≤ 9/5 := by
    unfold g
    rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ 3/2+h)]
    linarith
  have hs :
      |∑ l ∈ Finset.range (p+1), (a l)^(n+k)| ≤
        ((p : ℝ)+1)*(9/5)^n*(3/2)^k := calc
    _ ≤ ∑ l ∈ Finset.range (p+1), |(a l)^(n+k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ Finset.range (p+1), ((9/5)^n*(3/2)^k : ℝ) := by
      refine Finset.sum_le_sum fun l hl ↦ ?_
      rw [abs_pow, pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ((hb l hl).trans (by norm_num)) _)
        (pow_le_pow_left₀ (abs_nonneg _) (hb l hl) _) (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]; ring
  have hgk : |g^(n+k)| ≤ (9/5 : ℝ)^n*(9/5)^k := by
    rw [abs_pow, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hg _) (pow_le_pow_left₀ (abs_nonneg _) hg _)
      (by positivity) (by positivity)
  have hmass : h*((p : ℝ)+1) = 3+h := by rw [mul_add, hgrid, mul_one]
  unfold geometricCoeff
  change |(h*(∑ l ∈ Finset.range (p+1), (a l)^(n+k)) - g^(n+k)/4) / (n.factorial : ℝ)| ≤ _
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ))]
  calc
    _ ≤ (h*|∑ l ∈ Finset.range (p+1), (a l)^(n+k)| + |g^(n+k)|/4) /
        (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      refine (abs_sub _ _).trans_eq ?_
      rw [abs_mul, abs_of_nonneg hh, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ (h*(((p : ℝ)+1)*(9/5)^n*(3/2)^k) + ((9/5)^n*(9/5)^k)/4) /
        (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hs hh)
        (div_le_div_of_nonneg_right hgk (by norm_num))) (by positivity)
    _ = _ := by rw [show h*(((p : ℝ)+1)*(9/5)^n*(3/2)^k) =
        (h*((p : ℝ)+1))*(9/5)^n*(3/2)^k by ring, hmass]; ring

/-- Coefficients of the geometric profile slope, and of its curvature
after the strict margin has been subtracted. -/
theorem shortGap_profileT_majorants {p : ℕ} {h : ℝ} (hh : 0 ≤ h) (hhmax : h ≤ 3/11)
    (hgrid : h*(p : ℝ) = 3) (n : ℕ) :
    |geometricCoeff p h 1 n| ≤ 6*((9/5)^n/(n.factorial : ℝ)) ∧
    |geometricCoeff p h 2 n-(if n=0 then (1/200 : ℝ) else 0)| ≤
      11*((9/5)^n/(n.factorial : ℝ)) := by
  have he (k : ℕ) := geometricCoeff_majorant hh hhmax hgrid k n
  constructor
  · refine (he 1).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    norm_num
    linarith
  · by_cases hn : n=0
    · subst n
      simp only [if_pos rfl, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      calc
        _ ≤ |geometricCoeff p h 2 0| + 1/200 := by
          simpa using abs_sub (geometricCoeff p h 2 0) (1/200 : ℝ)
        _ ≤ _ := by
          have hB := geometricCoeff_majorant hh hhmax hgrid 2 0
          norm_num at hB
          linarith
    · rw [if_neg hn, sub_zero]
      refine (he 2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      norm_num
      linarith

private theorem profileCurvature_continuous (p : ℕ) (h : ℝ) :
    Continuous (deriv (deriv (shortGapProfileT p h))) := by
  rw [deriv_shortGapProfileT, funext fun t ↦ (hasDerivAt_profileMoment p h 1 t).deriv]
  exact (show Differentiable ℝ (profileMoment p h 2) from
    fun t ↦ (hasDerivAt_profileMoment p h 2 t).differentiableAt).continuous

private theorem sum_shifted_squares (h b : ℝ) (n : ℕ) :
    (∑ l ∈ Finset.range n, (h * l - b) ^ 2) =
      h ^ 2 * n * ((n : ℝ) - 1) * (2 * n - 1) / 6 -
        h * b * n * ((n : ℝ) - 1) + b ^ 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

/-- The exact curvature of the geometric profile at zero. -/
theorem shortGapProfileT_second_zero {p : ℕ} {h : ℝ} (hgrid : h * (p : ℝ) = 3) :
    deriv (deriv (shortGapProfileT p h)) 0 = 27 / 16 + 3 * h / 2 + h ^ 2 / 4 := by
  rw [deriv_shortGapProfileT, (hasDerivAt_profileMoment p h 1 0).deriv]
  simp only [profileMoment, mul_zero, Real.exp_zero, mul_one]
  rw [sum_shifted_squares, Nat.cast_add, Nat.cast_one]
  linear_combination (norm := ring)
    (h * (p : ℝ) * (2 * h * p + 3 * h - 3) / 6 + h ^ 2 / 6 + 3 / 4) * hgrid

/-- The derivatives of the continued square-root profile, with denominators cleared. -/
theorem sqrtProfile_jets {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hpos : ∀ t, 0 < U t) :
    let J : ℝ → ℝ := fun t ↦ t * Real.sqrt (U t)
    (∀ t, 2 * Real.sqrt (U t) * deriv J t = 2 * U t + t * deriv U t) ∧
    (∀ t, 4 * Real.sqrt (U t) ^ 3 * deriv (deriv J) t =
      4 * U t * deriv U t + t * (2 * U t * deriv (deriv U) t - (deriv U t) ^ 2)) := by
  dsimp only
  let S : ℝ → ℝ := fun t ↦ Real.sqrt (U t)
  let S₁ : ℝ → ℝ := fun t ↦ deriv U t / (2 * S t)
  have hdiff := hU.differentiable (by norm_num)
  have hS (t : ℝ) : HasDerivAt S (S₁ t) t :=
    (hdiff t).hasDerivAt.sqrt (hpos t).ne'
  have hJ (t : ℝ) :
      HasDerivAt (fun x ↦ x * S x) (S t + t * S₁ t) t := by
    simpa only [one_mul] using (hasDerivAt_id' t).fun_mul (hS t)
  have hJfun : deriv (fun x ↦ x * S x) = fun t ↦ S t + t * S₁ t :=
    funext fun t ↦ (hJ t).deriv
  have hSsq (t : ℝ) : S t ^ 2 = U t := Real.sq_sqrt (hpos t).le
  have hSne (t : ℝ) : S t ≠ 0 := (Real.sqrt_pos.2 (hpos t)).ne'
  constructor
  · intro t
    change 2 * S t * deriv (fun x ↦ x * S x) t = _
    rw [hJfun, ← hSsq t]
    dsimp only [S₁]
    field_simp [hSne t]
    <;> ring
  · intro t
    have hden : 2 * S t ≠ 0 := mul_ne_zero (by norm_num) (hSne t)
    have hS₁ := (hU.differentiable_deriv_two t).hasDerivAt.fun_div ((hS t).const_mul 2) hden
    have hJ₂ := (hS t).fun_add ((hasDerivAt_id' t).fun_mul hS₁)
    change 4 * S t ^ 3 * deriv (deriv (fun x ↦ x * S x)) t = _
    rw [hJfun, hJ₂.deriv, ← hSsq t]
    simp only [S₁, one_mul]
    field_simp [hSne t]
    <;> ring

/-- The two scalar tests give strict curvature and negative slope on the closed
short-gap interval. The positive smooth function represents the continued marginal. -/
theorem shortGapProfile_of_signs {p : ℕ} {h : ℝ} {U J : ℝ → ℝ}
    (hh : 0 < h) (hgrid : h * (p : ℝ) = 3)
    (hU : ContDiff ℝ 2 U) (hpos : ∀ t, 0 < U t)
    (hJ : J = fun t ↦ t * Real.sqrt (U t))
    (hJ₂ : 0 < deriv J 2)
    (hD : ∀ t ∈ Icc (0 : ℝ) 2, 0 < shortGapProfileD (shortGapProfileT p h) U t)
    (hH : 0 < shortGapProfileH (shortGapProfileT p h) U 2) :
    let F := fun t ↦ shortGapProfileT p h t - J t
    ∀ t ∈ Icc (0 : ℝ) 2, 1 / 200 < deriv (deriv F) t ∧ deriv F t < 0 := by
  subst J
  let J : ℝ → ℝ := fun t ↦ t * Real.sqrt (U t)
  let T := shortGapProfileT p h
  let A : ℝ → ℝ := fun t ↦ deriv (deriv T) t - 1 / 200
  let F : ℝ → ℝ := fun t ↦ T t - J t
  change ∀ t ∈ Icc (0 : ℝ) 2, 1 / 200 < deriv (deriv F) t ∧ deriv F t < 0
  obtain ⟨hj₁, hj₂⟩ := sqrtProfile_jets hU hpos
  have hDsq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
      (deriv (deriv J) t) ^ 2 < A t ^ 2 := by
    have hs := Real.sq_sqrt (hpos t).le
    have hd := hD t ht
    unfold shortGapProfileD at hd
    rw [← hj₂ t, mul_pow, show (4 * Real.sqrt (U t) ^ 3) ^ 2 = 16 * U t ^ 3 by
      rw [mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by decide, pow_mul, hs]
      norm_num] at hd
    exact lt_of_mul_lt_mul_left (sub_pos.mp hd)
      (mul_nonneg (by norm_num) (pow_nonneg (hpos t).le _))
  have hA0 : 0 < A 0 := by
    change 0 < deriv (deriv (shortGapProfileT p h)) 0 - 1 / 200
    rw [shortGapProfileT_second_zero hgrid]
    nlinarith only [hh, sq_nonneg h]
  have hAcont : Continuous A := (profileCurvature_continuous p h).sub continuous_const
  have hApos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : 0 < A t := by
    by_contra! hAt
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 2 := fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩
    obtain ⟨x, hx, hz⟩ := intermediate_value_Icc' ht.1 hAcont.continuousOn
      (show (0 : ℝ) ∈ Icc (A t) (A 0) from ⟨hAt, hA0.le⟩)
    have h := hDsq x (hsub hx)
    rw [hz, zero_pow (by decide)] at h
    exact (not_lt_of_ge (sq_nonneg _) h)
  have hJdiff : ContDiff ℝ 2 J :=
    contDiff_id.mul (hU.sqrt fun t ↦ (hpos t).ne')
  have hTdiff : Differentiable ℝ T := fun t ↦ by
    rw [← show profileMoment p h 0 = T by funext x; simp [profileMoment, T, shortGapProfileT]]
    exact (hasDerivAt_profileMoment p h 0 t).differentiableAt
  have hT'diff (t : ℝ) : DifferentiableAt ℝ (deriv T) t := by
    change DifferentiableAt ℝ (deriv (shortGapProfileT p h)) t
    rw [deriv_shortGapProfileT]
    exact (hasDerivAt_profileMoment p h 1 t).differentiableAt
  have hF₁ : deriv F = fun t ↦ deriv T t - deriv J t := by
    funext t
    exact ((hTdiff t).hasDerivAt.sub ((hJdiff.differentiable (by norm_num)) t).hasDerivAt).deriv
  have hF₂ (t : ℝ) : HasDerivAt (deriv F) (deriv (deriv T) t - deriv (deriv J) t) t := by
    rw [hF₁]
    exact (hT'diff t).hasDerivAt.sub (hJdiff.differentiable_deriv_two t).hasDerivAt
  have hcurv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : 1 / 200 < deriv (deriv F) t := by
    have hs := (sq_lt_sq.mp (hDsq t ht)).trans_eq (abs_of_pos (hApos t ht))
    have hj := (le_abs_self (deriv (deriv J) t)).trans_lt hs
    rw [(hF₂ t).deriv]
    change deriv (deriv J) t < deriv (deriv T) t - 1 / 200 at hj
    linarith only [hj]
  have hEnd : deriv F 2 < 0 := by
    unfold shortGapProfileH at hH
    rw [← hj₁ 2, mul_pow, mul_pow, Real.sq_sqrt (hpos 2).le] at hH
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hH
    have hs : (deriv T 2) ^ 2 < (deriv J 2) ^ 2 :=
      lt_of_mul_lt_mul_left (sub_pos.mp hH) (mul_nonneg (by norm_num) (hpos 2).le)
    have hlt := (le_abs_self (deriv T 2)).trans_lt
      ((sq_lt_sq.mp hs).trans_eq (abs_of_pos hJ₂))
    rw [hF₁]
    exact sub_neg.mpr hlt
  have hmono : MonotoneOn (deriv F) (Icc (0 : ℝ) 2) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t _ ↦ (hF₂ t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hF₂ t).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (by norm_num : (0 : ℝ) ≤ 1 / 200).trans
        (hcurv t (interior_subset ht)).le)
  intro t ht
  exact ⟨hcurv t ht, (hmono ht (right_mem_Icc.mpr (by norm_num)) ht.2).trans_lt hEnd⟩

/-- info: 'RefinedBMV.PositiveCenter.shortGapProfileT_second_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shortGapProfileT_second_zero

/-- info: 'RefinedBMV.PositiveCenter.shortGapProfile_of_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shortGapProfile_of_signs

end RefinedBMV.PositiveCenter
