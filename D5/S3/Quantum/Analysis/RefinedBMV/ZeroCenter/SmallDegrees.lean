/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/SmallDegrees
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict curvature of the zero-centered refined BMV profile in degrees one and two. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Profile

/-! Factored polynomial curvature proofs for the first two degrees. -/

open Filter
open scoped BigOperators Topology

namespace RefinedBMV.FourSpectrumLift

noncomputable section

private theorem hasDerivAt_exp_scale (k x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (k * u)) (k * Real.exp (k * x)) x :=
  (hasDerivAt_const_mul (x := x) k).exp.congr_deriv (mul_comm _ _)

/-- For `t = exp (k * c)`, the supplied derivatives apply the operator `t d/dt`
to the polynomials. The exponential normalization shifts this operator by `-a`. -/
private theorem curvature_of_factored_profile
    {f H H₁ H₂ Q Q₁ Q₂ : ℝ → ℝ} {c k a n : ℝ}
    (hc : 0 < c) (hk : k ≠ 0) (hn : 0 < n)
    (hf : ∀ x : ℝ, 0 < x →
      f x = Real.exp ((-k * a) * x) / n *
        (H x - (1 - Real.exp (k * x)) * Real.sqrt (Q x)))
    (hq : ∀ x : ℝ, 0 < x → 0 < Q x)
    (hH : ∀ x : ℝ, HasDerivAt H (k * H₁ x) x)
    (hH₁ : ∀ x : ℝ, HasDerivAt H₁ (k * H₂ x) x)
    (hQ : ∀ x : ℝ, HasDerivAt Q (k * Q₁ x) x)
    (hQ₁ : ∀ x : ℝ, HasDerivAt Q₁ (k * Q₂ x) x)
    (hP : 0 < H₂ c - 2 * a * H₁ c + a ^ 2 * H c)
    (hgap :
      let t := Real.exp (k * c)
      let B := 1 - t
      let B₁ := -t - a * B
      let B₂ := -t + 2 * a * t + a ^ 2 * B
      let P := H₂ c - 2 * a * H₁ c + a ^ 2 * H c
      let M := 4 * Q c ^ 2 * B₂ + 4 * Q c * B₁ * Q₁ c +
        2 * B * Q c * Q₂ c - B * Q₁ c ^ 2
      0 < 16 * Q c ^ 3 * P ^ 2 - M ^ 2) :
    0 < deriv^[2] f c := by
  let t (x : ℝ) := Real.exp (k * x)
  let E (x : ℝ) := Real.exp ((-k * a) * x) / n
  let B (x : ℝ) := 1 - t x
  let B₁ (x : ℝ) := -t x - a * B x
  let R (x : ℝ) := Real.sqrt (Q x)
  let P := H₂ c - 2 * a * H₁ c + a ^ 2 * H c
  let M := 4 * Q c ^ 2 * (-t c + 2 * a * t c + a ^ 2 * B c) +
    4 * Q c * B₁ c * Q₁ c + 2 * B c * Q c * Q₂ c - B c * Q₁ c ^ 2
  let G₁ (x : ℝ) := H₁ x - a * H x - B₁ x * R x - B x * (Q₁ x / (2 * R x))
  have ht (x : ℝ) : HasDerivAt t (k * t x) x := hasDerivAt_exp_scale k x
  have hE (x : ℝ) : HasDerivAt E ((-k * a) * E x) x := by
    refine ((hasDerivAt_exp_scale (-k * a) x).div_const n).congr_deriv ?_
    dsimp only [E]
    simp only [div_eq_mul_inv]
    ring
  have hB (x : ℝ) : HasDerivAt B (-(k * t x)) x := by
    simpa only [zero_sub] using (hasDerivAt_const x (1 : ℝ)).fun_sub (ht x)
  have hR (x : ℝ) (hx : 0 < x) : HasDerivAt R (k * Q₁ x / (2 * R x)) x :=
    (hQ x).sqrt (hq x hx).ne'
  have hfirst : deriv f =ᶠ[𝓝 c] (fun x ↦ k * (E x * G₁ x)) := by
    filter_upwards [eventually_gt_nhds hc] with x hx
    have heq : f =ᶠ[𝓝 x] (fun y ↦ E y * (H y - B y * R y)) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact hf y hy
    have hd : HasDerivAt (fun y ↦ E y * (H y - B y * R y)) (k * (E x * G₁ x)) x := by
      refine ((hE x).fun_mul ((hH x).fun_sub ((hB x).fun_mul (hR x hx)))).congr_deriv ?_
      dsimp only [G₁, B₁]
      simp only [div_eq_mul_inv]
      ring
    exact (hd.congr_of_eventuallyEq heq).deriv
  have hr : 0 < R c := Real.sqrt_pos.2 (hq c hc)
  have hRsq : R c ^ 2 = Q c := Real.sq_sqrt (hq c hc).le
  have hB₁ : HasDerivAt B₁ (-(k * t c) - a * (-(k * t c))) c :=
    (ht c).fun_neg.fun_sub ((hB c).const_mul a)
  have hquot := (hQ₁ c).fun_div ((hR c hc).const_mul 2)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hr).ne'
  have hG₁ := (((hH₁ c).fun_sub ((hH c).const_mul a)).fun_sub (hB₁.fun_mul (hR c hc))).fun_sub
    ((hB c).fun_mul hquot)
  have hsecond : HasDerivAt (fun x ↦ k * (E x * G₁ x))
      (k ^ 2 * E c * (P - M / (4 * R c ^ 3))) c := by
    refine (((hE c).fun_mul hG₁).const_mul k).congr_deriv ?_
    dsimp only [G₁, B₁, P, M]
    rw [← hRsq]
    field_simp [hr.ne']
    ring
  have hden : 0 < 4 * R c ^ 3 := mul_pos (by norm_num) (pow_pos hr _)
  have hsq : M ^ 2 < (P * (4 * R c ^ 3)) ^ 2 := by
    rw [show (P * (4 * R c ^ 3)) ^ 2 = 16 * Q c ^ 3 * P ^ 2 by rw [← hRsq]; ring]
    exact sub_pos.mp hgap
  have hdiff : 0 < P - M / (4 * R c ^ 3) := by
    have hPpos : 0 < P := hP
    exact sub_pos.mpr ((div_lt_iff₀ hden).2
      (lt_of_pow_lt_pow_left₀ 2 (mul_nonneg hPpos.le hden.le) hsq))
  change 0 < deriv (deriv f) c
  rw [hfirst.deriv_eq, hsecond.deriv]
  exact mul_pos (mul_pos (sq_pos_of_ne_zero hk) (div_pos (Real.exp_pos _) hn)) hdiff

/-- The degree-one zero-centered profile has positive curvature at every positive gap. -/
theorem zeroProfile_curvature_one {c : ℝ} (hc : 0 < c) :
    0 < deriv^[2] (zeroProfile 1) c := by
  let t (x : ℝ) := Real.exp (-(1 : ℝ) * x)
  let H (x : ℝ) := 1 + t x ^ 3
  let H₁ (x : ℝ) := 3 * t x ^ 3
  let H₂ (x : ℝ) := 9 * t x ^ 3
  let Q (x : ℝ) := 1 + 2 * t x
  let Q₁ (x : ℝ) := 2 * t x
  let Q₂ (x : ℝ) := 2 * t x
  have ht (x : ℝ) : 0 < t x := Real.exp_pos _
  have ht' (x : ℝ) : HasDerivAt t ((-1 : ℝ) * t x) x := hasDerivAt_exp_scale (-1) x
  have hP : H₂ c - 2 * (3 / 2 : ℝ) * H₁ c + (3 / 2 : ℝ) ^ 2 * H c = (9 / 4 : ℝ) * H c := by
    dsimp only [H, H₁, H₂]
    ring
  refine curvature_of_factored_profile (k := -1) (a := 3 / 2) (n := 2)
    (H := H) (H₁ := H₁) (H₂ := H₂) (Q := Q) (Q₁ := Q₁) (Q₂ := Q₂)
    hc (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have ht_lt : t x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hb : 0 ≤ 1 - t x := sub_nonneg.mpr ht_lt.le
    have he₃ : Real.exp (-3 * x / ((1 : ℕ) : ℝ)) = t x ^ 3 := by
      dsimp only [t]
      rw [← Real.exp_nat_mul]
      congr 1 <;> norm_num <;> ring
    have he₂ : Real.exp (-2 * x) = t x ^ 2 := by
      dsimp only [t]
      rw [← Real.exp_nat_mul]
      congr 1 <;> norm_num <;> ring
    have hH : (∑ j ∈ Finset.range 2, (t x ^ 3) ^ j) = H x := by
      norm_num [Finset.sum_range_succ, H] <;> ring
    have hJ : (∑ j ∈ Finset.range 2, (j + 1 : ℝ) * (t x ^ 3) ^ j) = 1 + 2 * t x ^ 3 := by
      norm_num [Finset.sum_range_succ] <;> ring
    have hchoose : ((1 + 2 : ℕ).choose 2 : ℝ) = 3 := by norm_num [Nat.choose]
    have hrad : 1 + 2 * t x ^ 3 - 3 * t x ^ 2 = (1 - t x) ^ 2 * Q x := by
      dsimp only [Q]
      ring
    unfold zeroProfile
    dsimp only
    rw [he₃, he₂, hH, hJ, hchoose, hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb]
    rw [show (-(-1 : ℝ) * (3 / 2)) * x = 3 * x / 2 by ring,
      show -3 * x / 2 = -(3 * x / 2) by ring, Real.exp_neg,
      show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
    change (H x - (1 - t x) * √(Q x)) / (2 * (Real.exp (3 * x / 2))⁻¹) =
      Real.exp (3 * x / 2) / 2 * (H x - (1 - t x) * √(Q x))
    simp only [div_mul_eq_div_div_swap, div_inv_eq_mul, div_mul_eq_mul_div, mul_comm]
  · intro x _
    have htx := ht x
    dsimp only [Q]
    positivity
  · intro x
    refine ((hasDerivAt_const x (1 : ℝ)).fun_add ((ht' x).fun_pow 3)).congr_deriv ?_
    dsimp only [H₁]
    ring
  · intro x
    refine (((ht' x).fun_pow 3).const_mul 3).congr_deriv ?_
    dsimp only [H₂]
    ring
  · intro x
    refine ((hasDerivAt_const x (1 : ℝ)).fun_add ((ht' x).const_mul 2)).congr_deriv ?_
    dsimp only [Q₁]
    ring
  · intro x
    refine ((ht' x).const_mul 2).congr_deriv ?_
    dsimp only [Q₂]
    ring
  · rw [hP]
    have htc := ht c
    dsimp only [H]
    positivity
  · have htc := ht c
    calc
      0 < 9 * t c ^ 2 *
          (3 + 18 * t c + 92 * t c ^ 2 + 216 * t c ^ 3 + 153 * t c ^ 4 +
            54 * t c ^ 5 + 108 * t c ^ 6 + 72 * t c ^ 7) := by positivity
      _ = _ := by
        change _ = 16 * Q c ^ 3 * (H₂ c - 2 * (3 / 2 : ℝ) * H₁ c + (3 / 2 : ℝ) ^ 2 * H c) ^ 2 - _
        rw [hP]
        dsimp only [H, Q, Q₁, Q₂, t]
        ring

/-- The degree-two zero-centered profile has positive curvature at every positive gap. -/
theorem zeroProfile_curvature_two {c : ℝ} (hc : 0 < c) :
    0 < deriv^[2] (zeroProfile 2) c := by
  let t (x : ℝ) := Real.exp ((-(1 : ℝ) / 2) * x)
  let H (x : ℝ) := 1 + t x ^ 3 + t x ^ 6
  let H₁ (x : ℝ) := 3 * t x ^ 3 + 6 * t x ^ 6
  let H₂ (x : ℝ) := 9 * t x ^ 3 + 36 * t x ^ 6
  let Q (x : ℝ) := 1 + 2 * t x + 3 * t x ^ 2 + 6 * t x ^ 3 + 3 * t x ^ 4
  let Q₁ (x : ℝ) := 2 * t x + 6 * t x ^ 2 + 18 * t x ^ 3 + 12 * t x ^ 4
  let Q₂ (x : ℝ) := 2 * t x + 12 * t x ^ 2 + 54 * t x ^ 3 + 48 * t x ^ 4
  have ht (x : ℝ) : 0 < t x := Real.exp_pos _
  have ht' (x : ℝ) : HasDerivAt t ((-(1 : ℝ) / 2) * t x) x := hasDerivAt_exp_scale (-1 / 2) x
  have hP : H₂ c - 2 * (3 : ℝ) * H₁ c + (3 : ℝ) ^ 2 * H c = 9 * (1 + t c ^ 6) := by
    dsimp only [H, H₁, H₂]
    ring
  refine curvature_of_factored_profile (k := -1 / 2) (a := 3) (n := 3)
    (H := H) (H₁ := H₁) (H₂ := H₂) (Q := Q) (Q₁ := Q₁) (Q₂ := Q₂)
    hc (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have ht_lt : t x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hb : 0 ≤ 1 - t x := sub_nonneg.mpr ht_lt.le
    have he₃ : Real.exp (-3 * x / ((2 : ℕ) : ℝ)) = t x ^ 3 := by
      dsimp only [t]
      rw [← Real.exp_nat_mul]
      congr 1 <;> norm_num <;> ring
    have he₄ : Real.exp (-2 * x) = t x ^ 4 := by
      dsimp only [t]
      rw [← Real.exp_nat_mul]
      congr 1 <;> norm_num <;> ring
    have hH : (∑ j ∈ Finset.range 3, (t x ^ 3) ^ j) = H x := by
      norm_num [Finset.sum_range_succ, H] <;> ring
    have hJ : (∑ j ∈ Finset.range 3, (j + 1 : ℝ) * (t x ^ 3) ^ j) =
        1 + 2 * t x ^ 3 + 3 * t x ^ 6 := by
      norm_num [Finset.sum_range_succ] <;> ring
    have hchoose : ((2 + 2 : ℕ).choose 2 : ℝ) = 6 := by norm_num [Nat.choose]
    have hrad : 1 + 2 * t x ^ 3 + 3 * t x ^ 6 - 6 * t x ^ 4 = (1 - t x) ^ 2 * Q x := by
      dsimp only [Q]
      ring
    unfold zeroProfile
    dsimp only
    rw [he₃, he₄, hH, hJ, hchoose, hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb]
    rw [show (-(-1 / 2 : ℝ) * 3) * x = 3 * x / 2 by ring,
      show -3 * x / 2 = -(3 * x / 2) by ring, Real.exp_neg,
      show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num]
    change (H x - (1 - t x) * √(Q x)) / (3 * (Real.exp (3 * x / 2))⁻¹) =
      Real.exp (3 * x / 2) / 3 * (H x - (1 - t x) * √(Q x))
    simp only [div_mul_eq_div_div_swap, div_inv_eq_mul, div_mul_eq_mul_div, mul_comm]
  · intro x _
    have htx := ht x
    dsimp only [Q]
    positivity
  · intro x
    refine (((hasDerivAt_const x (1 : ℝ)).fun_add ((ht' x).fun_pow 3)).fun_add
      ((ht' x).fun_pow 6)).congr_deriv ?_
    dsimp only [H₁]
    ring
  · intro x
    refine ((((ht' x).fun_pow 3).const_mul 3).fun_add (((ht' x).fun_pow 6).const_mul 6)).congr_deriv ?_
    dsimp only [H₂]
    ring
  · intro x
    refine (((((hasDerivAt_const x (1 : ℝ)).fun_add ((ht' x).const_mul 2)).fun_add
      (((ht' x).fun_pow 2).const_mul 3)).fun_add (((ht' x).fun_pow 3).const_mul 6)).fun_add
      (((ht' x).fun_pow 4).const_mul 3)).congr_deriv ?_
    dsimp only [Q₁]
    ring
  · intro x
    refine (((((ht' x).const_mul 2).fun_add (((ht' x).fun_pow 2).const_mul 6)).fun_add
      (((ht' x).fun_pow 3).const_mul 18)).fun_add (((ht' x).fun_pow 4).const_mul 12)).congr_deriv ?_
    dsimp only [Q₂]
    ring
  · rw [hP]
    have htc := ht c
    positivity
  · have htc := ht c
    calc
      0 < 144 * t c ^ 4 *
          (6 + 36 * t c + 126 * t c ^ 2 + 276 * t c ^ 3 + 512 * t c ^ 4 +
            1020 * t c ^ 5 + 1836 * t c ^ 6 + 3480 * t c ^ 7 + 6669 * t c ^ 8 +
            10098 * t c ^ 9 + 11709 * t c ^ 10 + 11250 * t c ^ 11 + 8586 * t c ^ 12 +
            5346 * t c ^ 13 + 4455 * t c ^ 14 + 5346 * t c ^ 15 + 5832 * t c ^ 16 +
            5346 * t c ^ 17 + 3645 * t c ^ 18 + 1458 * t c ^ 19 + 243 * t c ^ 20) := by
        positivity
      _ = _ := by
        change _ = 16 * Q c ^ 3 * (H₂ c - 2 * (3 : ℝ) * H₁ c + (3 : ℝ) ^ 2 * H c) ^ 2 - _
        rw [hP]
        dsimp only [Q, Q₁, Q₂, t]
        ring

#print axioms zeroProfile_curvature_one
#print axioms zeroProfile_curvature_two

section

variable {n : Type*} [Fintype n] [DecidableEq n]

#check @product_bound_singular n _ _ 1 (by decide)
  (zeroUpperPSD_of_profile_curvature (by decide) (fun _ hc ↦ (zeroProfile_curvature_one hc).le))

#check @product_bound_singular n _ _ 2 (by decide)
  (zeroUpperPSD_of_profile_curvature (by decide) (fun _ hc ↦ (zeroProfile_curvature_two hc).le))

end

end

end RefinedBMV.FourSpectrumLift
