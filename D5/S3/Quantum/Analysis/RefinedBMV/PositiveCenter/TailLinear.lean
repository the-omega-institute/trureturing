/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/TailLinear
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not - specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive convolutions and derivative bounds for the upper-tail linear remainder. -/
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailLinearCoefficients

/-! # Linear error in the positive-center upper tail of the refined BMV kernel -/

open Filter MeasureTheory Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

local notation "g(" h ")" => (3 + h)
local notation "k(" h ")" => (3 + 2 * h)
local notation "m(" h ")" => (3 + 3 * h)
local notation "j(" h ")" => (1 + h)
local notation "c(" h ")" => (g(h) * k(h) / 2)

/-- The linear remainder's tail multiplier with denominator power one or two. -/
noncomputable def upperTailLinearW (h : ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  Real.exp (-(j(h)*d)) / upperTailGap h d ^ n

theorem hasDerivAt_upperTailLinearW {h d : ℝ} {n : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hn : n = 1 ∨ n = 2) :
    HasDerivAt (upperTailLinearW h n)
      (-(j(h) + n * upperTailSlope h d) * upperTailLinearW h n d) d := by
  have ha := upperTailLinear_gap_pos hh hd
  have ha' := upperTailGap_logDeriv hh hd
  rw [(hasDerivAt_upperTailGap hh).deriv] at ha'
  have hg : HasDerivAt (upperTailGap h) (upperTailSlope h d * upperTailGap h d) d := by
    rw [← (div_eq_iff ha.ne').1 ha']
    exact hasDerivAt_upperTailGap hh
  have he := hasDerivAt_upperTailLinearDecay j(h) d
  have hw := he.div (hg.pow n) (pow_ne_zero n ha.ne')
  unfold upperTailLinearW
  convert hw using 1
  rcases hn with rfl | rfl
  all_goals simp only [Pi.pow_apply]
  all_goals norm_num
  all_goals field_simp [ha.ne'] <;> ring

theorem hasDerivAt_deriv_upperTailLinearW {h d : ℝ} {n : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hn : n = 1 ∨ n = 2) :
    HasDerivAt (deriv (upperTailLinearW h n))
      (((j(h) + n * upperTailSlope h d)^2 +
        n * (upperTailSlope h d * (h + upperTailSlope h d))) * upperTailLinearW h n d) d := by
  have hl := (hasDerivAt_upperTailSlope hh hd).const_mul (n : ℝ) |>.const_add j(h) |>.neg
  have hw := hasDerivAt_upperTailLinearW hh hd hn
  have hprod := hl.mul hw
  have hnear : deriv (upperTailLinearW h n) =ᶠ[nhds d]
      (fun t ↦ -(j(h) + n * upperTailSlope h t) * upperTailLinearW h n t) := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact (hasDerivAt_upperTailLinearW hh ht hn).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ hnear
  convert hprod using 1
  simp only [Pi.neg_apply]
  ring

/-- Uniform tail bounds for the first and second derivatives of the multipliers. -/
theorem upperTailLinearW_bounds {h d : ℝ} {n : ℕ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hd : 11 ≤ d) (hn : n = 1 ∨ n = 2) :
    let W := upperTailLinearW h n d
    0 < W ∧ W ≤ Real.exp (-d) / 3^n ∧
    |deriv (upperTailLinearW h n) d| ≤ (3/2)*W ∧
    |deriv (deriv (upperTailLinearW h n)) d| ≤ (9/4)*W := by
  dsimp only
  have hd₀ : 0 < d := by linarith
  have ha := upperTailLinear_gap_pos hh hd₀
  have ha3 := upperTailGap_ge_three hh hhmax hd
  have hW : 0 < upperTailLinearW h n d := div_pos (Real.exp_pos _) (pow_pos ha _)
  have he : Real.exp (-(j(h)*d)) ≤ Real.exp (-d) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hh.le hd₀.le]
  have hw : upperTailLinearW h n d ≤ Real.exp (-d) / 3^n :=
    div_le_div₀ (Real.exp_pos _).le he (by positivity)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) ha3 n)
  let L := upperTailSlope h d
  have hL := upperTailSlope_bounds hh hd₀
  have hL₀ : 0 < L := hL.1
  have hL₁ : L ≤ 1/11 := hL.2.1.trans ((div_le_div_iff₀ hd₀ (by norm_num)).2 (by simpa using hd))
  have hn₀ : (0 : ℝ) ≤ n := by positivity
  have hn₂ : (n : ℝ) ≤ 2 := by rcases hn with rfl | rfl <;> norm_num
  have hNL : (n : ℝ) * L ≤ 2 * (1/11) :=
    mul_le_mul hn₂ hL₁ hL₀.le (by norm_num)
  have hrate₀ : 0 ≤ j(h) + n*L := by positivity
  have hrate : j(h) + n*L ≤ 16/11 := by linarith
  have hcurv₀ : 0 ≤ L*(h+L) := by positivity
  have hcurv : L*(h+L) ≤ (1/11)*(4/11) :=
    mul_le_mul hL₁ (by linarith) (by positivity) (by norm_num)
  have hncurv : (n : ℝ) * (L*(h+L)) ≤ 2 * ((1/11)*(4/11)) :=
    mul_le_mul hn₂ hcurv hcurv₀ (by norm_num)
  have hsecond : (j(h)+n*L)^2 + n*(L*(h+L)) ≤ (9/4 : ℝ) := by
    linarith [pow_le_pow_left₀ hrate₀ hrate 2]
  refine ⟨hW, hw, ?_, ?_⟩
  · rw [(hasDerivAt_upperTailLinearW hh hd₀ hn).deriv]
    change |-(j(h) + n*L) * upperTailLinearW h n d| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg hrate₀, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_right (hrate.trans (by norm_num)) hW.le
  · rw [(hasDerivAt_deriv_upperTailLinearW hh hd₀ hn).deriv]
    change |((j(h)+n*L)^2 + n*(L*(h+L))) * upperTailLinearW h n d| ≤ _
    rw [abs_mul, abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hn₀ hcurv₀)), abs_of_pos hW]
    exact mul_le_mul_of_nonneg_right hsecond hW.le

/-- The linear summand of the normalized error, in independent coordinates u and d. -/
noncomputable def upperTailLinearError (h u d : ℝ) : ℝ :=
  (-upperTailLinearP0 h u * upperTailLinearW h 2 d +
    upperTailLinearP1 h u * upperTailLinearW h 1 d) / c(h)

/-- Recover the regularized numerator formula, including the sign of A - 1. -/
theorem upperTailLinearError_eq_regularized {h u d : ℝ} (hh : 0 < h) (hu : 0 < u)
    (hd : 0 < d) :
    upperTailLinearError h u d =
      Real.exp (-(j(h)*d)) *
        (upperTailLinearA h u - 1 + upperTailGap h d * upperTailLinearA1 h u) /
        (c(h) * upperTailGap h d ^ 2 * (1 - Real.exp (-u)) ^ 2) := by
  have hc : 0 < c(h) := by positivity
  unfold upperTailLinearError upperTailLinearP0 upperTailLinearP1 upperTailLinearW
  field_simp [hc.ne', (upperTailLinear_gap_pos hh hd).ne', (upperTailLinear_ell_pos hu).ne']
  ring

private theorem deriv_linearCombination {f g : ℝ → ℝ} {a b C x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun t ↦ (-a * f t + b * g t) / C) x =
      (-a * deriv f x + b * deriv g x) / C :=
  (((hf.hasDerivAt.const_mul (-a)).add (hg.hasDerivAt.const_mul b)).div_const C).deriv

private theorem deriv_upperTailLinearError_u {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) :
    deriv (fun t ↦ upperTailLinearError h t d) u =
      (-deriv (upperTailLinearP0 h) u * upperTailLinearW h 2 d +
        deriv (upperTailLinearP1 h) u * upperTailLinearW h 1 d) / c(h) := by
  have h0 := (upperTailLinearP0_differentiableAt (h := h) hu).hasDerivAt
  have h1 := (upperTailLinearP1_differentiableAt hh hu).hasDerivAt
  exact (((h0.neg.mul_const _).add (h1.mul_const _)).div_const _).deriv

private theorem deriv_upperTailLinearError_d {h u d : ℝ} (hh : 0 < h) (hd : 0 < d) :
    deriv (upperTailLinearError h u) d =
      (-upperTailLinearP0 h u * deriv (upperTailLinearW h 2) d +
        upperTailLinearP1 h u * deriv (upperTailLinearW h 1) d) / c(h) :=
  deriv_linearCombination (hasDerivAt_upperTailLinearW hh hd (Or.inr rfl)).differentiableAt
    (hasDerivAt_upperTailLinearW hh hd (Or.inl rfl)).differentiableAt

/-- The two mixed partials agree by the separated product formula for the linear error. -/
theorem upperTailLinearError_mixed_commute {h u d : ℝ} (hh : 0 < h) (hu : 0 < u)
    (hd : 0 < d) :
    deriv (fun y ↦ deriv (fun x ↦ upperTailLinearError h x y) u) d =
      deriv (fun x ↦ deriv (upperTailLinearError h x) d) u := by
  simp_rw [deriv_upperTailLinearError_u hh hu, deriv_upperTailLinearError_d hh hd]
  rw [deriv_linearCombination
    (hasDerivAt_upperTailLinearW hh hd (Or.inr rfl)).differentiableAt
    (hasDerivAt_upperTailLinearW hh hd (Or.inl rfl)).differentiableAt]
  have h0 := (upperTailLinearP0_differentiableAt (h := h) hu).hasDerivAt
  have h1 := (upperTailLinearP1_differentiableAt hh hu).hasDerivAt
  exact ((((h0.neg.mul_const _).add (h1.mul_const _)).div_const _).deriv).symm

/-- The signed profiles are kept separate when differentiating the linear
correction in the independent lower coordinate and gap. -/
theorem upperTailLinearError_derivatives {h u d : ℝ} (hh : 0 < h) (hu : 0 < u)
    (hd : 0 < d) :
    let E := upperTailLinearError h
    let P₀ := upperTailLinearP0 h
    let P₁ := upperTailLinearP1 h
    let L := upperTailSlope h d
    let q := L * (h + L)
    let M₁ := j(h) + L
    let M₂ := j(h) + 2 * L
    let e₀ := P₀ u * upperTailLinearW h 2 d / c(h)
    let e₁ := P₁ u * upperTailLinearW h 1 d / c(h)
    let l₀ := deriv P₀ u / P₀ u
    let l₁ := deriv P₁ u / P₁ u
    E u d = -e₀ + e₁ ∧
      deriv (fun x ↦ E x d) u = -l₀ * e₀ + l₁ * e₁ ∧
      deriv (E u) d = M₂ * e₀ - M₁ * e₁ ∧
      deriv (fun x ↦ deriv (E x) d) u = M₂ * l₀ * e₀ - M₁ * l₁ * e₁ ∧
      deriv (deriv (E u)) d = -(M₂ ^ 2 + 2 * q) * e₀ + (M₁ ^ 2 + q) * e₁ := by
  let E := upperTailLinearError h
  let P₀ := upperTailLinearP0 h
  let P₁ := upperTailLinearP1 h
  let W₁ := upperTailLinearW h 1
  let W₂ := upperTailLinearW h 2
  let c₀ := c(h)
  obtain ⟨⟨hp₀, _⟩, hp₁, _⟩ := upperTailLinear_value_bounds hh hu
  have hw₁ := (hasDerivAt_upperTailLinearW hh hd (Or.inl (rfl : (1 : ℕ) = 1))).deriv
  have hw₂ := (hasDerivAt_upperTailLinearW hh hd (Or.inr (rfl : (2 : ℕ) = 2))).deriv
  have hww₁ := hasDerivAt_deriv_upperTailLinearW hh hd (Or.inl (rfl : (1 : ℕ) = 1))
  have hww₂ := hasDerivAt_deriv_upperTailLinearW hh hd (Or.inr (rfl : (2 : ℕ) = 2))
  have hmix : deriv (fun x ↦ deriv (E x) d) u =
      (-deriv P₀ u * deriv W₂ d + deriv P₁ u * deriv W₁ d) / c₀ := by
    simp_rw [E, deriv_upperTailLinearError_d hh hd]
    have h0 := (upperTailLinearP0_differentiableAt (h := h) hu).hasDerivAt
    have h1 := (upperTailLinearP1_differentiableAt hh hu).hasDerivAt
    exact (((h0.neg.mul_const _).add (h1.mul_const _)).div_const _).deriv
  have hnear : deriv (E u) =ᶠ[𝓝 d]
      fun t ↦ (-P₀ u * deriv W₂ t + P₁ u * deriv W₁ t) / c₀ := by
    filter_upwards [eventually_gt_nhds hd] with t ht
    exact deriv_upperTailLinearError_d hh ht
  have hsecond : deriv (deriv (E u)) d =
      (-P₀ u * deriv (deriv W₂) d + P₁ u * deriv (deriv W₁) d) / c₀ := by
    rw [hnear.deriv_eq]
    exact deriv_linearCombination hww₂.differentiableAt hww₁.differentiableAt
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold upperTailLinearError
    ring
  · rw [deriv_upperTailLinearError_u hh hu]
    field_simp [hp₀.ne', hp₁.ne'] <;> ring
  · rw [deriv_upperTailLinearError_d hh hd, hw₁, hw₂]
    push_cast
    ring
  · rw [show deriv (fun x ↦ deriv (upperTailLinearError h x) d) u = _ from hmix, hw₁, hw₂]
    dsimp only [P₀, P₁, c₀]
    push_cast
    field_simp [hp₀.ne', hp₁.ne'] <;> ring
  · rw [show deriv (deriv (upperTailLinearError h u)) d = _ from hsecond,
      hww₁.deriv, hww₂.deriv]
    push_cast
    ring

private theorem linear_absolute_bound {x₀ x₁ y₂ y₁ C m e l r : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (he : 0 ≤ e) (hl : 0 ≤ l) (_hr : 0 ≤ r)
    (hlr : l * r ≤ 6) (hm4 : m ≤ 4)
    (hx₀ : |x₀| ≤ l * C) (hx₁ : |x₁| ≤ l * (C * m))
    (hy₂ : |y₂| ≤ r * (e / 9)) (hy₁ : |y₁| ≤ r * (e / 3)) :
    |(-x₀*y₂ + x₁*y₁)/C| ≤ (26/3)*e := by
  rw [abs_div, abs_of_pos hC]
  apply (div_le_iff₀ hC).2
  have h2 := mul_le_mul hx₀ hy₂ (abs_nonneg y₂) (mul_nonneg hl hC.le)
  have h1 := mul_le_mul hx₁ hy₁ (abs_nonneg y₁) (mul_nonneg hl (mul_nonneg hC.le hm))
  calc
    _ ≤ |-x₀*y₂| + |x₁*y₁| := abs_add_le ..
    _ ≤ (l * r)*(e / 9 + m*(e / 3))*C := by
      rw [abs_mul, abs_neg, abs_mul]
      convert add_le_add h2 h1 using 1
      ring
    _ ≤ 6*(e / 9 + m*(e / 3))*C := by gcongr
    _ ≤ 6*(e / 9 + 4*(e / 3))*C := by gcongr
    _ = _ := by ring

/-- The five linear remainder terms used by the positive-center upper-tail sign
test have the same bound throughout the positive u range. -/
theorem upperTailLinearError_bounds {h u d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (hu : 0 < u) (hd : 11 ≤ d) :
    let E := upperTailLinearError h
    let B := (26/3) * Real.exp (-d)
    |E u d| ≤ B ∧
    |deriv (fun x ↦ E x d) u| ≤ B ∧
    |deriv (E u) d| ≤ B ∧
    |deriv (fun y ↦ deriv (fun x ↦ E x y) u) d| ≤ B ∧
    |deriv (deriv (E u)) d| ≤ B := by
  dsimp only
  have hd₀ : 0 < d := by linarith
  have hc : 0 < c(h) := by positivity
  have hm : 0 ≤ m(h) := by positivity
  have hm4 : m(h) ≤ 4 := by linarith
  have hk4 : k(h) ≤ 4 := by linarith
  have he := (Real.exp_pos (-d)).le
  obtain ⟨⟨hp₀, hp₀'⟩, ⟨hp₁, hp₁'⟩⟩ := upperTailLinear_value_bounds hh hu
  obtain ⟨hpu₀, hpu₁⟩ := upperTailLinear_deriv_bounds hh hu
  have hp0 : |upperTailLinearP0 h u| ≤ 1*c(h) := by
    simpa only [abs_of_pos hp₀, one_mul] using hp₀'
  have hp1 : |upperTailLinearP1 h u| ≤ 1*(c(h)*m(h)) := by
    simpa only [abs_of_pos hp₁, one_mul] using hp₁'
  have hpu0 := hpu₀.trans (mul_le_mul hk4 hp₀' hp₀.le (by norm_num))
  have hpu1 := hpu₁.trans (mul_le_mul hm4 hp₁' hp₁.le (by norm_num))
  have hn1 : 1 = 1 ∨ 1 = 2 := Or.inl rfl
  have hn2 : 2 = 1 ∨ 2 = 2 := Or.inr rfl
  have hw1 := upperTailLinearW_bounds hh hhmax hd hn1
  have hw2 := upperTailLinearW_bounds hh hhmax hd hn2
  have hW1 : upperTailLinearW h 1 d ≤ Real.exp (-d)/3 := by
    simpa only [pow_one] using hw1.2.1
  have hW2 : upperTailLinearW h 2 d ≤ Real.exp (-d)/9 := by
    norm_num at hw2
    exact hw2.2.1
  have hW1₀ : |upperTailLinearW h 1 d| ≤ 1*(Real.exp (-d)/3) := by
    simpa only [abs_of_pos hw1.1, one_mul] using hW1
  have hW2₀ : |upperTailLinearW h 2 d| ≤ 1*(Real.exp (-d)/9) := by
    simpa only [abs_of_pos hw2.1, one_mul] using hW2
  have hw1' := (hasDerivAt_upperTailLinearW hh hd₀ hn1).differentiableAt
  have hw2' := (hasDerivAt_upperTailLinearW hh hd₀ hn2).differentiableAt
  have hw1'' := (hasDerivAt_deriv_upperTailLinearW hh hd₀ hn1).differentiableAt
  have hw2'' := (hasDerivAt_deriv_upperTailLinearW hh hd₀ hn2).differentiableAt
  have hw1d := hw1.2.2.1.trans (mul_le_mul_of_nonneg_left hW1 (by norm_num))
  have hw2d := hw2.2.2.1.trans (mul_le_mul_of_nonneg_left hW2 (by norm_num))
  have hw1dd := hw1.2.2.2.trans (mul_le_mul_of_nonneg_left hW1 (by norm_num))
  have hw2dd := hw2.2.2.2.trans (mul_le_mul_of_nonneg_left hW2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hW2₀ hW1₀
  · rw [deriv_upperTailLinearError_u hh hu]
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hpu0 hpu1 hW2₀ hW1₀
  · rw [deriv_upperTailLinearError_d hh hd₀]
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hw2d hw1d
  · simp_rw [deriv_upperTailLinearError_u hh hu]
    rw [deriv_linearCombination hw2' hw1']
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hpu0 hpu1 hw2d hw1d
  · have hnear : deriv (upperTailLinearError h u) =ᶠ[𝓝 d]
        (fun t ↦ (-upperTailLinearP0 h u * deriv (upperTailLinearW h 2) t +
          upperTailLinearP1 h u * deriv (upperTailLinearW h 1) t) / c(h)) := by
      filter_upwards [eventually_gt_nhds hd₀] with t ht using deriv_upperTailLinearError_d hh ht
    rw [hnear.deriv_eq, deriv_linearCombination hw2'' hw1'']
    exact linear_absolute_bound hc hm he (by norm_num) (by norm_num) (by norm_num)
      hm4 hp0 hp1 hw2dd hw1dd

#print axioms hasDerivAt_upperTailLinearW
#print axioms hasDerivAt_deriv_upperTailLinearW
#print axioms upperTailLinearW_bounds
#print axioms upperTailLinearError_eq_regularized
#print axioms upperTailLinearError_mixed_commute
#print axioms upperTailLinearError_bounds

end RefinedBMV.PositiveCenter
