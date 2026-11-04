/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SignedLaplace
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SignedLaplace
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: An explicit negative signed Laplace average of the literal factorial G. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Cancellation
import D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
The signed average concerns the literal factorial compensation. The finite model
matches only the first two floor cells; both infinite tails are explicitly paid.
The gamma, logarithm, harmonic-tail and finite-smoothing suppliers keep their
original owners and attribution. No RH or zero-exclusion statement is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

private def laplaceCell (d y : ℝ) : ℝ := d * (y - 1) - y * Real.log y


/-- The finite model agrees only on the two literal right-closed floor cells. -/
private lemma two_cells {x : ℝ} (hx : 1 ≤ x) (hx3 : x < 3) :
    G x = laplaceCell (1 + gamma - alpha) x +
      (if 2 ≤ x then laplaceCell (1 + gamma + Real.log 2) (x / 2) else 0) := by
  have he := G_formula hx
  by_cases hx2 : 2 ≤ x
  · have hn : ⌊x⌋₊ = 2 := (Nat.floor_eq_iff (by linarith : 0 ≤ x)).mpr
      ⟨hx2, by norm_num; exact hx3⟩
    rw [ite_eq_left hx2, he]
    norm_num [H, J, prefixSum, hn, Finset.sum_Icc_succ_top, laplaceCell]
    rw [Real.log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  · have hn : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith : 0 ≤ x)).mpr
      ⟨by simpa using hx, by norm_num; linarith⟩
    rw [ite_eq_right hx2, he]
    norm_num [H, J, prefixSum, hn, Finset.sum_Icc_succ_top, laplaceCell]
    ring

/-- The existing sharp tail and the nineteen certified dyadic logarithms
bound the actual integral-defined alpha; the harmonic cutoff remains 20. -/
private lemma alpha_bounds :
    (1479615 / 10000000 : ℝ) < alpha ∧ alpha < 2279659 / 10000000 ∧
      (3492496 / 10000000 : ℝ) < gamma - alpha := by
  have hg := GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  change (5772155 / 10000000 : ℝ) < gamma ∧ gamma < 5772161 / 10000000 at hg
  have h2 : (693147180299 / 1000000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < (693147180801 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 2 (1 / 1 : ℝ) _ _ 1 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h3 : (1098612288407 / 1000000000000 : ℝ) < Real.log 3 ∧
      Real.log 3 < (109861228891 / 100000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 3 (3 / 2 : ℝ) _ _ 1 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h4 : (1386294360599 / 1000000000000 : ℝ) < Real.log 4 ∧
      Real.log 4 < (1386294361601 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 4 (1 / 1 : ℝ) _ _ 2 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h5 : (1609437911913 / 1000000000000 : ℝ) < Real.log 5 ∧
      Real.log 5 < (402359478229 / 250000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 5 (5 / 4 : ℝ) _ _ 2 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h6 : (1791759468707 / 1000000000000 : ℝ) < Real.log 6 ∧
      Real.log 6 < (179175946971 / 100000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 6 (3 / 2 : ℝ) _ _ 2 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h7 : (972955074251 / 500000000000 : ℝ) < Real.log 7 ∧
      Real.log 7 < (1945910149537 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 7 (7 / 4 : ℝ) _ _ 2 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h8 : (2079441540899 / 1000000000000 : ℝ) < Real.log 8 ∧
      Real.log 8 < (2079441542401 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 8 (1 / 1 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h9 : (439444915311 / 200000000000 : ℝ) < Real.log 9 ∧
      Real.log 9 < (1098612289029 / 500000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 9 (9 / 8 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h10 : (2302585092213 / 1000000000000 : ℝ) < Real.log 10 ∧
      Real.log 10 < (575646273429 / 250000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 10 (5 / 4 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h11 : (2397895272017 / 1000000000000 : ℝ) < Real.log 11 ∧
      Real.log 11 < (29973690919 / 12500000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 11 (11 / 8 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h12 : (2484906649007 / 1000000000000 : ℝ) < Real.log 12 ∧
      Real.log 12 < (248490665051 / 100000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 12 (3 / 2 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h13 : (2564949356677 / 1000000000000 : ℝ) < Real.log 13 ∧
      Real.log 13 < (2564949358183 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 13 (13 / 8 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h14 : (1319528664401 / 500000000000 : ℝ) < Real.log 14 ∧
      Real.log 14 < (2639057330337 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 14 (7 / 4 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h15 : (2708050200109 / 1000000000000 : ℝ) < Real.log 15 ∧
      Real.log 15 < (1354025100913 / 500000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 15 (15 / 8 : ℝ) _ _ 3 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h16 : (2772588721199 / 1000000000000 : ℝ) < Real.log 16 ∧
      Real.log 16 < (2772588723201 / 1000000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 16 (1 / 1 : ℝ) _ _ 4 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h17 : (566642668603 / 200000000000 : ℝ) < Real.log 17 ∧
      Real.log 17 < (1416606672509 / 500000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 17 (17 / 16 : ℝ) _ _ 4 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h18 : (578074351371 / 200000000000 : ℝ) < Real.log 18 ∧
      Real.log 18 < (1445185879429 / 500000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 18 (9 / 8 : ℝ) _ _ 4 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h19 : (942220473 / 320000000 : ℝ) < Real.log 19 ∧
      Real.log 19 < (92013718129 / 31250000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 19 (19 / 16 : ℝ) _ _ 4 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have h20 : (2995732272513 / 1000000000000 : ℝ) < Real.log 20 ∧
      Real.log 20 < (748933068629 / 250000000000 : ℝ) := by
    apply GoldenResource.RobinRationalBasis.rational_log_bounds 20 (5 / 4 : ℝ) _ _ 4 8
    all_goals norm_num [GoldenResource.RobinRationalBasis.atanhPartial,
      Finset.sum_range_succ]
  have hH : H 20 = (55835135 / 15519504 : ℝ) := by
    norm_num [H, prefixSum, Finset.sum_Icc_succ_top]
  have hJ : (4488867670209 / 1000000000000 : ℝ) < J 20 ∧
      J 20 < (4488867673063 / 1000000000000 : ℝ) := by
    norm_num [J, prefixSum, Finset.sum_Icc_succ_top]
    constructor <;> linarith only [
      h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
      h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2,
      h10.1, h10.2, h11.1, h11.2, h12.1, h12.2, h13.1, h13.2,
      h14.1, h14.2, h15.1, h15.2, h16.1, h16.2, h17.1, h17.2,
      h18.1, h18.2, h19.1, h19.2, h20.1, h20.2]
  have hid := J_tail_from_slope (x := 20) (by norm_num)
  have ht := T_epsilon_quadratic_bound (x := 20) (by norm_num)
  rw [abs_le] at ht
  norm_num at ht
  have halpha : alpha = (gamma + Real.log 20) ^ 2 + 2 * J 20 -
      2 * H 20 * Real.log 20 - 2 * T_epsilon 20 := by
    dsimp [epsilon] at hid
    nlinarith only [hid]
  have hpos : 0 < gamma + Real.log 20 := by linarith only [hg.1, h20.1]
  rw [halpha, hH]
  constructor
  · nlinarith only [hg.1, h20.1, h20.2, hJ.1, ht.2,
      sq_nonneg (gamma + Real.log 20 -
        (5772155 / 10000000 + 2995732272513 / 1000000000000))]
  · constructor
    · nlinarith only [hg.2, h20.1, h20.2, hJ.2, ht.1,
        mul_self_lt_mul_self hpos.le (show gamma + Real.log 20 <
          5772161 / 10000000 + 748933068629 / 250000000000 by
          linarith only [hg.2, h20.2])]
    · nlinarith only [hg.1, hg.2, h20.1, h20.2, hJ.2, ht.1,
        mul_self_lt_mul_self hpos.le (show gamma + Real.log 20 <
          5772161 / 10000000 + 748933068629 / 250000000000 by
          linarith only [hg.2, h20.2])]


/-- Public Gamma convergence and its exact integral, scaled to any positive rate. -/
private lemma moment_zero (b : ℝ) (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) * t ^ n) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ n) =
        (n.factorial : ℝ) / b ^ (n + 1) := by
  constructor
  · have hsource :=
      D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample.exp_moment_integrable hb n
    simpa only [mul_comm] using hsource
  · have he := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n : ℝ) + 1) (r := b) (by positivity) hb
    convert he using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [add_sub_cancel_right, Real.rpow_natCast]
      ring_nf
    · rw [Real.Gamma_nat_eq_factorial,
        show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
      simp [div_eq_mul_inv, mul_comm]

private lemma translate_Ioi (A : ℝ) (v : ℝ → ℝ) :
    (IntegrableOn (fun u => v (u + A)) (Ioi 0) ↔ IntegrableOn v (Ioi A)) ∧
    (∫ u in Ioi (0 : ℝ), v (u + A)) = ∫ t in Ioi A, v t := by
  have hp : (fun u : ℝ => u + A) ⁻¹' Ioi A = Ioi 0 := by
    ext u
    simp
  have hm := measurePreserving_add_right (volume : Measure ℝ) A
  have he := (Homeomorph.addRight A).measurableEmbedding
  constructor
  · simpa only [hp, Function.comp_def] using hm.integrableOn_comp_preimage he (f := v) (s := Ioi A)
  · simpa only [hp] using hm.setIntegral_preimage_emb he v (Ioi A)

private def tailPolynomial (n : ℕ) (b A : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * (k.factorial : ℝ) * A ^ (n - k) / b ^ (k + 1)

/-- Translation and the binomial theorem pay the complete polynomial tail. -/
private lemma moment_tail (b : ℝ) (hb : 0 < b) (A : ℝ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) * t ^ n) (Ioi A) ∧
      (∫ t in Ioi A, Real.exp (-b * t) * t ^ n) =
        Real.exp (-b * A) * tailPolynomial n b A := by
  have he (u : ℝ) : Real.exp (-b * (u + A)) * (u + A) ^ n =
      Real.exp (-b * A) * ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * A ^ (n - k)) * (Real.exp (-b * u) * u ^ k) := by
    rw [show -b * (u + A) = -b * A + -b * u by ring, Real.exp_add, add_pow]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hi (k : ℕ) : IntegrableOn
      (fun u : ℝ => ((n.choose k : ℝ) * A ^ (n - k)) *
        (Real.exp (-b * u) * u ^ k)) (Ioi 0) :=
    ((moment_zero b hb k).1.const_mul _)
  have hs := (integrable_finsetSum (Finset.range (n + 1)) (fun k _ => hi k)).const_mul
    (Real.exp (-b * A))
  have hshift : IntegrableOn
      (fun u : ℝ => Real.exp (-b * (u + A)) * (u + A) ^ n) (Ioi 0) := by
    exact hs.congr (Eventually.of_forall (fun u => (he u).symm))
  refine ⟨(translate_Ioi A _).1.mp hshift, ?_⟩
  rw [← (translate_Ioi A (fun t => Real.exp (-b * t) * t ^ n)).2]
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum (Finset.range (n + 1)) (fun k _ => hi k)]
  simp_rw [integral_const_mul, (moment_zero b hb _).2]
  congr 1
  unfold tailPolynomial
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma tailPolynomial_mono (n : ℕ) {b A B : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) (hAB : A ≤ B) :
    tailPolynomial n b A ≤ tailPolynomial n b B := by
  apply Finset.sum_le_sum
  intro k _
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ hA hAB _

private def cellExp (d t : ℝ) : ℝ := d * (Real.exp t - 1) - t * Real.exp t
private def signedCell (d p q t : ℝ) : ℝ :=
  (p - q * t) * Real.exp (-(21 / 2 : ℝ) * t) * cellExp d t
private def momentM (d : ℝ) : ℝ := (4 / 399 : ℝ) * d - 4 / 361
private def momentMprime (d : ℝ) : ℝ := -(320 / 159201 : ℝ) * d + 16 / 6859

private lemma signedCell_data (d p q : ℝ) :
    IntegrableOn (signedCell d p q) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), signedCell d p q t) = p * momentM d + q * momentMprime d := by
  have hb0 := moment_zero (19 / 2) (by norm_num) 0
  have hb1 := moment_zero (19 / 2) (by norm_num) 1
  have hb2 := moment_zero (19 / 2) (by norm_num) 2
  have hs0 := moment_zero (21 / 2) (by norm_num) 0
  have hs1 := moment_zero (21 / 2) (by norm_num) 1
  have he (t : ℝ) : signedCell d p q t =
      (d * p) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) -
      (d * p) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 0) -
      (d * q + p) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 1) +
      (d * q) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 1) +
      q * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 2) := by
    have hex : Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t =
        Real.exp (-(19 / 2 : ℝ) * t) := by rw [← Real.exp_add]; congr 1; ring
    dsimp [signedCell, cellExp]
    calc
      _ = d * p * (Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t) -
          d * p * Real.exp (-(21 / 2 : ℝ) * t) -
          (d * q + p) * t * (Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t) +
          d * q * t * Real.exp (-(21 / 2 : ℝ) * t) +
          q * t ^ 2 * (Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t) := by ring
      _ = _ := by rw [hex]; ring
  have hi0 : IntegrableOn (fun t : ℝ =>
      d * p * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) -
      d * p * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 0)) (Ioi 0) :=
    (hb0.1.const_mul (d * p)).sub (hs0.1.const_mul (d * p))
  have hi1 : IntegrableOn (fun t : ℝ =>
      d * p * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) -
      d * p * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 0) -
      (d * q + p) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 1)) (Ioi 0) :=
    hi0.sub (hb1.1.const_mul (d * q + p))
  have hi2 : IntegrableOn (fun t : ℝ =>
      d * p * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) -
      d * p * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 0) -
      (d * q + p) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 1) +
      d * q * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 1)) (Ioi 0) :=
    hi1.add (hs1.1.const_mul (d * q))
  have hi := hi2.add (hb2.1.const_mul q)
  constructor
  · exact hi.congr (Eventually.of_forall (fun t => (he t).symm))
  · simp_rw [he]
    rw [integral_add hi2 (hb2.1.const_mul q)]
    rw [integral_add hi1 (hs1.1.const_mul (d * q))]
    rw [integral_sub hi0 (hb1.1.const_mul (d * q + p))]
    rw [integral_sub (hb0.1.const_mul (d * p)) (hs0.1.const_mul (d * p))]
    simp_rw [integral_const_mul]
    rw [hb0.2, hb1.2, hb2.2, hs0.2, hs1.2]
    norm_num [momentM, momentMprime]
    ring

private def signedWeight (t : ℝ) : ℝ := (1 - 10 * t) * Real.exp (-(21 / 2 : ℝ) * t)
private def modelValue (t : ℝ) : ℝ :=
  cellExp (1 + gamma - alpha) t +
    (Ioi (Real.log 2)).indicator (fun t => cellExp (1 + gamma + Real.log 2) (t - Real.log 2)) t
private def modelSigned (t : ℝ) : ℝ := signedWeight t * modelValue t

private lemma shiftedCell_data (d A : ℝ) :
    IntegrableOn (fun t => signedWeight t * cellExp d (t - A)) (Ioi A) ∧
      (∫ t in Ioi A, signedWeight t * cellExp d (t - A)) =
        Real.exp (-(21 / 2 : ℝ) * A) *
          ((1 - 10 * A) * momentM d + 10 * momentMprime d) := by
  have he (u : ℝ) : signedWeight (u + A) * cellExp d (u + A - A) =
      Real.exp (-(21 / 2 : ℝ) * A) * signedCell d (1 - 10 * A) 10 u := by
    simp only [signedWeight, signedCell, add_sub_cancel_right]
    rw [show -(21 / 2 : ℝ) * (u + A) = -(21 / 2 : ℝ) * A + -(21 / 2 : ℝ) * u
      by ring, Real.exp_add]
    ring
  have hi := (signedCell_data d (1 - 10 * A) 10).1.const_mul
    (Real.exp (-(21 / 2 : ℝ) * A))
  refine ⟨(translate_Ioi A _).1.mp
    (hi.congr (Eventually.of_forall (fun u => (he u).symm))), ?_⟩
  rw [← (translate_Ioi A (fun t => signedWeight t * cellExp d (t - A))).2]
  simp_rw [he]
  rw [integral_const_mul, (signedCell_data d (1 - 10 * A) 10).2]

private lemma model_data :
    IntegrableOn modelSigned (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), modelSigned t) < -(94846 / 75620475 : ℝ) := by
  have hg := GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  have hl := GoldenResource.RobinRationalBasis.log_two_decimal_bounds
  have hL : (0 : ℝ) < Real.log 2 := by linarith only [hl.1]
  have hd := signedCell_data (1 + gamma - alpha) 1 10
  have hs := shiftedCell_data (1 + gamma + Real.log 2) (Real.log 2)
  have hind : IntegrableOn
      ((Ioi (Real.log 2)).indicator (fun t => signedWeight t *
        cellExp (1 + gamma + Real.log 2) (t - Real.log 2))) (Ioi 0) :=
    (hs.1.integrable_indicator measurableSet_Ioi).integrableOn
  have he (t : ℝ) : modelSigned t = signedCell (1 + gamma - alpha) 1 10 t +
      (Ioi (Real.log 2)).indicator (fun t => signedWeight t *
        cellExp (1 + gamma + Real.log 2) (t - Real.log 2)) t := by
    dsimp [modelSigned, modelValue, signedCell, signedWeight]
    by_cases ht : t ∈ Ioi (Real.log 2) <;> simp [ht, mul_add]
  refine ⟨(hd.1.add hind).congr (Eventually.of_forall (fun t => (he t).symm)), ?_⟩
  simp_rw [he]
  rw [integral_add hd.1 hind, hd.2, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi hL.le), hs.2]
  have hd2 : (2 : ℝ) < 1 + gamma + Real.log 2 := by
    change (5772155 / 10000000 : ℝ) < gamma ∧ gamma < 5772161 / 10000000 at hg
    linarith only [hg.1, hl.1]
  have hm : 0 < momentM (1 + gamma + Real.log 2) := by dsimp [momentM]; linarith only [hd2]
  have hmp : momentMprime (1 + gamma + Real.log 2) < 0 := by
    dsimp [momentMprime]; linarith only [hd2]
  have hp : 1 - 10 * Real.log 2 < 0 := by linarith only [hl.1]
  have hn : Real.exp (-(21 / 2 : ℝ) * Real.log 2) *
      ((1 - 10 * Real.log 2) * momentM (1 + gamma + Real.log 2) +
        10 * momentMprime (1 + gamma + Real.log 2)) < 0 := by
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      (add_neg (mul_neg_of_neg_of_pos hp hm) (mul_neg_of_pos_of_neg (by norm_num) hmp))
  have hc := alpha_bounds.2.2
  dsimp [momentM, momentMprime] at *
  linarith only [hc, hn]

private lemma model_matches {t : ℝ} (ht : 0 ≤ t) (h3 : t < Real.log 3) :
    G (Real.exp t) = modelValue t := by
  have hex : Real.exp t < 3 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using Real.exp_lt_exp.mpr h3
  have he := two_cells (Real.one_le_exp_iff.mpr ht) hex
  have hc (d u : ℝ) : laplaceCell d (Real.exp u) = cellExp d u := by
    simp [laplaceCell, cellExp, Real.log_exp, mul_comm]
  have hdiv : Real.exp t / 2 = Real.exp (t - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he, hc]
  dsimp only [modelValue]
  by_cases hL : Real.log 2 < t
  · have hx : 2 ≤ Real.exp t := by
      exact (show (2 : ℝ) < Real.exp t by
        simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
          Real.exp_lt_exp.mpr hL).le
    rw [ite_eq_left hx, indicator_of_mem (show t ∈ Ioi (Real.log 2) from hL), hdiv, hc]
  · rw [indicator_of_notMem (show t ∉ Ioi (Real.log 2) from hL)]
    by_cases hx : 2 ≤ Real.exp t
    · have heq : t = Real.log 2 := by
        have hx' : Real.log 2 ≤ t := by
          apply Real.exp_le_exp.mp
          simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hx
        linarith
      simp [heq, laplaceCell, Real.exp_log, cellExp]
    · simp [ite_eq_right hx]

private lemma cellExp_bound {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) :
    |cellExp d t| ≤ Real.exp t * (d + t) := by
  have hex : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  calc
    _ ≤ |d * (Real.exp t - 1)| + |t * Real.exp t| := abs_sub _ _
    _ = d * (Real.exp t - 1) + t * Real.exp t := by
      rw [abs_of_nonneg (mul_nonneg hd (by linarith)),
        abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
    _ ≤ _ := by nlinarith only [hd]

private lemma model_bound {t : ℝ} (ht : 0 ≤ t) :
    |modelValue t| ≤ (11 / 4 + 3 * t / 2) * Real.exp t := by
  have hg := GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
  change (5772155 / 10000000 : ℝ) < gamma ∧ gamma < 5772161 / 10000000 at hg
  have hl := GoldenResource.RobinRationalBasis.log_two_decimal_bounds
  have ha := alpha_bounds
  have hd : 0 ≤ 1 + gamma - alpha ∧ 1 + gamma - alpha ≤ (8 / 5 : ℝ) := by
    constructor <;> linarith only [hg.2, ha.1, ha.2.2]
  have hd2 : 0 ≤ 1 + gamma + Real.log 2 ∧ 1 + gamma + Real.log 2 ≤ (23 / 10 : ℝ) := by
    constructor <;> linarith only [hg.1, hg.2, hl.1, hl.2]
  have hfirst : |cellExp (1 + gamma - alpha) t| ≤ Real.exp t * (8 / 5 + t) := by
    exact (cellExp_bound hd.1 ht).trans (mul_le_mul_of_nonneg_left
      (by linarith only [hd.2]) (Real.exp_pos _).le)
  have hsecond : |(Ioi (Real.log 2)).indicator
      (fun t => cellExp (1 + gamma + Real.log 2) (t - Real.log 2)) t| ≤
        Real.exp t / 2 * (23 / 10 + t) := by
    by_cases hL : Real.log 2 < t
    · rw [indicator_of_mem (show t ∈ Ioi (Real.log 2) from hL)]
      have hi := cellExp_bound hd2.1 (sub_nonneg.mpr hL.le)
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hi
      refine hi.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      linarith only [hd2.2, hl.1]
    · rw [indicator_of_notMem (show t ∉ Ioi (Real.log 2) from hL)]
      simp only [abs_zero]
      positivity
  exact (abs_add_le _ _).trans (by
    calc
      _ ≤ Real.exp t * (8 / 5 + t) + Real.exp t / 2 * (23 / 10 + t) :=
        add_le_add hfirst hsecond
      _ = _ := by ring)


private def actualMajorant (t : ℝ) : ℝ :=
  (13 / 5 : ℝ) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 1) +
  (53 / 2 : ℝ) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 2) +
  5 * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 3)
private def modelMajorant (t : ℝ) : ℝ :=
  (11 / 4 : ℝ) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) +
  29 * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 1) +
  15 * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 2)

private lemma majorants_integrable (A : ℝ) :
    IntegrableOn actualMajorant (Ioi A) ∧ IntegrableOn modelMajorant (Ioi A) := by
  constructor
  · exact (((moment_tail (21 / 2) (by norm_num) A 1).1.const_mul (13 / 5)).add
      ((moment_tail (21 / 2) (by norm_num) A 2).1.const_mul (53 / 2))).add
        ((moment_tail (21 / 2) (by norm_num) A 3).1.const_mul 5)
  · exact (((moment_tail (19 / 2) (by norm_num) A 0).1.const_mul (11 / 4)).add
      ((moment_tail (19 / 2) (by norm_num) A 1).1.const_mul 29)).add
        ((moment_tail (19 / 2) (by norm_num) A 2).1.const_mul 15)

private lemma weight_bound {t : ℝ} (ht : 0 ≤ t) : |1 - 10 * t| ≤ 1 + 10 * t := by
  simpa only [abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10),
    abs_of_nonneg ht] using (abs_sub (1 : ℝ) (10 * t))

private lemma actual_signed_bound {t : ℝ} (ht : 0 ≤ t) :
    |signedWeight t * G (Real.exp t)| ≤ actualMajorant t := by
  have hg := GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds.2
  have hG := compensation.2.2.2.2.1 t ht
  have hG' : |G (Real.exp t)| ≤ (13 / 5 : ℝ) * t + t ^ 2 / 2 := by
    refine hG.trans ?_
    change gamma < (5772161 / 10000000 : ℝ) at hg
    nlinarith only [mul_nonneg (sub_nonneg.mpr (show gamma ≤ (3 / 5 : ℝ) by
      linarith only [hg])) ht]
  rw [abs_mul, signedWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((1 + 10 * t) * Real.exp (-(21 / 2 : ℝ) * t)) *
        ((13 / 5 : ℝ) * t + t ^ 2 / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (weight_bound ht) (Real.exp_pos _).le)
        hG' (abs_nonneg _) (by positivity)
    _ = actualMajorant t := by dsimp [actualMajorant]; ring

private lemma model_signed_bound {t : ℝ} (ht : 0 ≤ t) :
    |modelSigned t| ≤ modelMajorant t := by
  rw [modelSigned, abs_mul, signedWeight, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((1 + 10 * t) * Real.exp (-(21 / 2 : ℝ) * t)) *
        ((11 / 4 + 3 * t / 2) * Real.exp t) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (weight_bound ht) (Real.exp_pos _).le)
        (model_bound ht) (abs_nonneg _) (by positivity)
    _ = modelMajorant t := by
      have he : Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t =
          Real.exp (-(19 / 2 : ℝ) * t) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (11 / 4 + 29 * t + 15 * t ^ 2) *
            (Real.exp (-(21 / 2 : ℝ) * t) * Real.exp t) := by ring
        _ = _ := by rw [he]; dsimp [modelMajorant]; ring

private lemma actual_integrable :
    IntegrableOn (fun t => signedWeight t * G (Real.exp t)) (Ioi 0) := by
  have hG : ContinuousOn (fun t : ℝ => G (Real.exp t)) (Ioi 0) :=
    compensation.2.1.comp Real.continuous_exp.continuousOn
      (fun t ht => Real.one_le_exp_iff.mpr ht.le)
  have hw : Continuous signedWeight := by unfold signedWeight; fun_prop
  apply (majorants_integrable 0).1.mono'
    ((hw.continuousOn.mul hG).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs, Pi.mul_apply] using actual_signed_bound ht.le

private lemma log_three_bound : 0 < Real.log 3 ∧
      Real.log 3 < (11 / 10 : ℝ) := by
  have h := GoldenResource.RobinRationalBasis.rational_log_bounds
    3 (3 / 2) (1098612288 / 1000000000) (1098612289 / 1000000000) 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [GoldenResource.RobinRationalBasis.atanhPartial, Finset.sum_range_succ])
  constructor <;> linarith only [h.1, h.2]

private lemma exp_three_bound :
    Real.exp (-(21 / 2 : ℝ) * Real.log 3) ≤ (1 / 100000 : ℝ) ∧
    Real.exp (-(19 / 2 : ℝ) * Real.log 3) ≤ (3 / 100000 : ℝ) := by
  have he : Real.exp (-(21 / 2 : ℝ) * Real.log 3) ^ 2 = (1 : ℝ) / 3 ^ 21 := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(21 / 2 : ℝ) * Real.log 3) = -(21 * Real.log 3) by ring]
    have hn := Real.exp_nat_mul (Real.log 3) 21
    norm_num only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hn
    rw [Real.exp_neg, hn]
    simp only [one_div]
  have hsmall : Real.exp (-(21 / 2 : ℝ) * Real.log 3) < (1 / 100000 : ℝ) :=
    (sq_lt_sq₀ (Real.exp_pos _).le (by norm_num)).mp (by rw [he]; norm_num)
  refine ⟨hsmall.le, ?_⟩
  rw [show -(19 / 2 : ℝ) * Real.log 3 = Real.log 3 + -(21 / 2 : ℝ) * Real.log 3 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  linarith only [hsmall]

/-- Only the polynomial argument is enlarged. The exponential factor stays
at the true lower endpoint log 3. -/
private lemma paid_tail :
    (∫ t in Ioi (Real.log 3), actualMajorant t + modelMajorant t) ≤
      (65567192153 / 277905245625000 : ℝ) := by
  let A := Real.log 3
  have hA : 0 ≤ A := log_three_bound.1.le
  have hAB : A ≤ (11 / 10 : ℝ) := log_three_bound.2.le
  have hp (n : ℕ) (b : ℝ) (hb : 0 < b) := tailPolynomial_mono n hb hA hAB
  have hiA := majorants_integrable A
  rw [integral_add hiA.1 hiA.2]
  have h21 : IntegrableOn (fun t : ℝ =>
      (13 / 5 : ℝ) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 1) +
      (53 / 2 : ℝ) * (Real.exp (-(21 / 2 : ℝ) * t) * t ^ 2)) (Ioi A) :=
    ((moment_tail (21 / 2) (by norm_num) A 1).1.const_mul (13 / 5)).add
      ((moment_tail (21 / 2) (by norm_num) A 2).1.const_mul (53 / 2))
  have h19 : IntegrableOn (fun t : ℝ =>
      (11 / 4 : ℝ) * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 0) +
      29 * (Real.exp (-(19 / 2 : ℝ) * t) * t ^ 1)) (Ioi A) :=
    ((moment_tail (19 / 2) (by norm_num) A 0).1.const_mul (11 / 4)).add
      ((moment_tail (19 / 2) (by norm_num) A 1).1.const_mul 29)
  unfold actualMajorant modelMajorant
  rw [integral_add h21 ((moment_tail (21 / 2) (by norm_num) A 3).1.const_mul 5)]
  rw [integral_add ((moment_tail (21 / 2) (by norm_num) A 1).1.const_mul (13 / 5))
    ((moment_tail (21 / 2) (by norm_num) A 2).1.const_mul (53 / 2))]
  rw [integral_add h19 ((moment_tail (19 / 2) (by norm_num) A 2).1.const_mul 15)]
  rw [integral_add ((moment_tail (19 / 2) (by norm_num) A 0).1.const_mul (11 / 4))
    ((moment_tail (19 / 2) (by norm_num) A 1).1.const_mul 29)]
  simp_rw [integral_const_mul]
  rw [(moment_tail (21 / 2) (by norm_num) A 1).2,
    (moment_tail (21 / 2) (by norm_num) A 2).2,
    (moment_tail (21 / 2) (by norm_num) A 3).2,
    (moment_tail (19 / 2) (by norm_num) A 0).2,
    (moment_tail (19 / 2) (by norm_num) A 1).2,
    (moment_tail (19 / 2) (by norm_num) A 2).2]
  have heA := exp_three_bound.1
  have heB := exp_three_bound.2
  have hpa := hp 1 (21 / 2) (by norm_num)
  have hpa2 := hp 2 (21 / 2) (by norm_num)
  have hpa3 := hp 3 (21 / 2) (by norm_num)
  have hpb := hp 0 (19 / 2) (by norm_num)
  have hpb1 := hp 1 (19 / 2) (by norm_num)
  have hpb2 := hp 2 (19 / 2) (by norm_num)
  have hmul (b v V E : ℝ) (hv : v ≤ V) (hV : 0 ≤ V)
      (he : Real.exp (-b * A) ≤ E) : Real.exp (-b * A) * v ≤ E * V :=
    (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right he hV)
  have h1 := hmul (21 / 2) _ _ _ hpa (by norm_num [tailPolynomial, Finset.sum_range_succ]) heA
  have h2 := hmul (21 / 2) _ _ _ hpa2 (by norm_num [tailPolynomial, Finset.sum_range_succ]) heA
  have h3 := hmul (21 / 2) _ _ _ hpa3 (by norm_num [tailPolynomial, Finset.sum_range_succ]) heA
  have h0' := hmul (19 / 2) _ _ _ hpb (by norm_num [tailPolynomial, Finset.sum_range_succ]) heB
  have h1' := hmul (19 / 2) _ _ _ hpb1 (by norm_num [tailPolynomial, Finset.sum_range_succ]) heB
  have h2' := hmul (19 / 2) _ _ _ hpb2 (by norm_num [tailPolynomial, Finset.sum_range_succ]) heB
  norm_num [tailPolynomial, Finset.sum_range_succ] at h1 h2 h3 h0' h1' h2' ⊢
  linarith only [h1, h2, h3, h0', h1', h2']

/-- An explicitly negative signed average of the actual factorial G. Both
integrability and the strict rational bound are unconditional. -/
theorem G_signed_laplace_negative :
    IntegrableOn (fun t : ℝ => (1 - 10 * t) * Real.exp (-(21 / 2 : ℝ) * t) *
      G (Real.exp t)) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), (1 - 10 * t) * Real.exp (-(21 / 2 : ℝ) * t) *
      G (Real.exp t)) < -(1 / 1000 : ℝ) := by
  change IntegrableOn (fun t => signedWeight t * G (Real.exp t)) (Ioi 0) ∧ _
  refine ⟨actual_integrable, ?_⟩
  let A := Real.log 3
  let tail : ℝ → ℝ := (Ici A).indicator (fun t => actualMajorant t + modelMajorant t)
  have hi := actual_integrable
  have hm := model_data
  have hit : IntegrableOn (fun t => actualMajorant t + modelMajorant t) (Ici A) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((majorants_integrable A).1.add (majorants_integrable A).2)
  have ht : IntegrableOn tail (Ioi 0) :=
    (hit.integrable_indicator measurableSet_Ici).integrableOn
  have hcomp : (∫ t in Ioi (0 : ℝ), signedWeight t * G (Real.exp t) - modelSigned t) ≤
      ∫ t in Ioi (0 : ℝ), tail t := by
    apply setIntegral_mono_on (hi.sub hm.1) ht measurableSet_Ioi
    intro t ht0
    by_cases hAt : A ≤ t
    · rw [show tail t = actualMajorant t + modelMajorant t from
        indicator_of_mem (show t ∈ Ici A from hAt) _]
      exact (le_abs_self _).trans ((abs_sub _ _).trans
        (add_le_add (actual_signed_bound ht0.le) (model_signed_bound ht0.le)))
    · have he := model_matches ht0.le (lt_of_not_ge hAt)
      simp [tail, hAt, he, modelSigned]
  have heq : (∫ t in Ioi (0 : ℝ), tail t) =
      ∫ t in Ioi A, actualMajorant t + modelMajorant t := by
    rw [setIntegral_indicator measurableSet_Ici,
      inter_eq_right.mpr (show Ici A ⊆ Ioi (0 : ℝ) from
        fun t ht0 => lt_of_lt_of_le log_three_bound.1 ht0), integral_Ici_eq_integral_Ioi]
  rw [integral_sub hi hm.1, heq] at hcomp
  have htail := paid_tail
  change (∫ t in Ioi (0 : ℝ), signedWeight t * G (Real.exp t)) < -(1 / 1000 : ℝ)
  linarith only [hcomp, hm.2, htail]

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
