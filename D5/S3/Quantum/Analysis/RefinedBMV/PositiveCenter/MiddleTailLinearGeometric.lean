/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailLinearGeometric
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive geometric sum for the ratio of the two linear correction derivatives. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailLinearCoefficients

/-! Separate the common exponential factor before comparing the linear coefficients. -/

namespace RefinedBMV.PositiveCenter

open Set
open scoped BigOperators

open private sub_le_sub_of_derivatives from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical

noncomputable def middleTailLinearGeom (n : ℕ) (h u : ℝ) : ℝ :=
  ((n : ℝ) / 2) * (1 + Real.exp (-(h * ((n : ℝ) + 1) * u))) -
    ∑ i ∈ Finset.range n, Real.exp (-(h * ((i : ℝ) + 1) * u))

noncomputable def middleTailLinearWeight (n : ℕ) (h u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ((i : ℝ) + 1) *
    ∑ j ∈ Finset.range (n - i), Real.exp (h * ((n - (i + 1 + j) : ℕ) : ℝ) * u)

noncomputable def middleTailLinearLoss (n : ℕ) (h u : ℝ) : ℝ :=
  (1 - ((n : ℝ) + 1) * Real.exp (-(h * (n : ℝ) * u)) +
    (n : ℝ) * Real.exp (-(h * ((n : ℝ) + 1) * u))) / 2

private theorem sum_shifted_index (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem exp_sum_difference (h u : ℝ) {i n : ℕ} (hi : i < n) :
    Real.exp (-(h * ((i : ℝ) + 1) * u)) - Real.exp (-(h * ((n : ℝ) + 1) * u)) =
      (Real.exp (-(h * (n : ℝ) * u)) * (1 - Real.exp (-(h * u)))) *
        ∑ j ∈ Finset.range (n - i), Real.exp (h * ((n - (i + 1 + j) : ℕ) : ℝ) * u) := by
  let x := Real.exp (-(h * u))
  have hx (a : ℕ) : x ^ a = Real.exp (-(h * (a : ℝ) * u)) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show Real.exp (-(h * ((i : ℝ) + 1) * u)) = x ^ (i + 1) by
    rw [hx, Nat.cast_add, Nat.cast_one],
    show Real.exp (-(h * ((n : ℝ) + 1) * u)) = x ^ (n + 1) by
      rw [hx, Nat.cast_add, Nat.cast_one], ← hx n]
  change x ^ (i + 1) - x ^ (n + 1) = x ^ n * (1 - x) * _
  have hsum := geom_sum_mul_neg x (n - i)
  calc
    _ = x ^ (i + 1) * (1 - x ^ (n - i)) := by
      rw [mul_sub, mul_one, ← pow_add, show i + 1 + (n - i) = n + 1 by omega]
    _ = (x ^ (i + 1) * (∑ j ∈ Finset.range (n - i), x ^ j)) * (1 - x) := by
      rw [← hsum, mul_assoc]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hijn : i + 1 + j ≤ n := by have := Finset.mem_range.mp hj; omega
      rw [← pow_add, hx (i + 1 + j), hx n, mul_comm (Real.exp (-(h * (n : ℝ) * u))) (1 - x),
        mul_assoc, ← Real.exp_add, mul_comm (1 - x)]
      congr 1
      congr 1
      push_cast [Nat.cast_sub hijn]
      ring

/-- The two coefficient derivatives share a positive elementary factor. -/
theorem hasDerivAt_middleTailLinearGeom (n : ℕ) (h u : ℝ) :
    HasDerivAt (middleTailLinearGeom n h)
      (h * (Real.exp (-(h * (n : ℝ) * u)) * (1 - Real.exp (-(h * u)))) *
        middleTailLinearWeight n h u) u := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range n)
    (fun i _ ↦ hasDerivAt_upperTailLinearDecay (h * ((i : ℝ) + 1)) u)
  have hterm := (hasDerivAt_upperTailLinearDecay (h * ((n : ℝ) + 1)) u).const_add 1
  apply ((hterm.const_mul ((n : ℝ) / 2)).sub hsum).congr_deriv
  unfold middleTailLinearWeight
  have he : ((n : ℝ) / 2) * (-(h * ((n : ℝ) + 1)) *
      Real.exp (-(h * ((n : ℝ) + 1) * u))) =
      ∑ i ∈ Finset.range n, -(h * ((i : ℝ) + 1)) * Real.exp (-(h * ((n : ℝ) + 1) * u)) := by
    simp_rw [show ∀ i : ℕ, -(h * ((i : ℝ) + 1)) * Real.exp (-(h * ((n : ℝ) + 1) * u)) =
        (-(h * Real.exp (-(h * ((n : ℝ) + 1) * u)))) * ((i : ℝ) + 1) by intro i; ring]
    rw [← Finset.mul_sum, sum_shifted_index]
    ring
  rw [he, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hsplit := exp_sum_difference h u hi'
  linear_combination (h * ((i : ℝ) + 1)) * hsplit

theorem middleTailLinearWeight_mono (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    Monotone (middleTailLinearWeight n h) := by
  intro u v huv
  unfold middleTailLinearWeight
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huv (by positivity))

theorem hasDerivAt_middleTailLinearLoss (n : ℕ) (h u : ℝ) :
    HasDerivAt (middleTailLinearLoss n h)
      ((h * (Real.exp (-(h * (n : ℝ) * u)) * (1 - Real.exp (-(h * u)))) *
        ((n : ℝ) * ((n : ℝ) + 1) / 2)) u := by
  have h₁ := (hasDerivAt_upperTailLinearDecay (h * (n : ℝ)) u).const_mul ((n : ℝ) + 1)
  have h₂ := (hasDerivAt_upperTailLinearDecay (h * ((n : ℝ) + 1)) u).const_mul (n : ℝ)
  apply (((h₁.const_sub (1 : ℝ)).add h₂).div_const 2).congr_deriv
  rw [show Real.exp (-(h * ((n : ℝ) + 1) * u)) =
    Real.exp (-(h * (n : ℝ) * u)) * Real.exp (-(h * u)) by rw [← Real.exp_add]; congr 1; ring]
  ring

/-- Integrating the increasing derivative ratio bounds the ratio of the original coefficients. -/
theorem middleTailLinear_ratio_comparison (n : ℕ) {h u : ℝ} (hh : 0 < h) (hu : 0 ≤ u) :
    let N := (n : ℝ) * ((n : ℝ) + 1) / 2
    let D := middleTailLinearGeom n h u
    let L := middleTailLinearLoss n h u
    middleTailLinearWeight n h 0 * L ≤ N * D ∧ N * D ≤ middleTailLinearWeight n h u * L := by
  let N := (n : ℝ) * ((n : ℝ) + 1) / 2
  let D := middleTailLinearGeom n h
  let L := middleTailLinearLoss n h
  let W := middleTailLinearWeight n h
  let F (t : ℝ) := h * (Real.exp (-(h * (n : ℝ) * t)) * (1 - Real.exp (-(h * t))))
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hF (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F t := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le ht))
    exact mul_nonneg hh.le (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr he))
  have hD₀ : D 0 = 0 := by simp [D, middleTailLinearGeom]; ring
  have hL₀ : L 0 = 0 := by simp [L, middleTailLinearLoss]
  have hmono : Monotone W := middleTailLinearWeight_mono n hh.le
  have hD (t : ℝ) : HasDerivAt D (F t * W t) t := hasDerivAt_middleTailLinearGeom n h t
  have hL (t : ℝ) : HasDerivAt L (F t * N) t := hasDerivAt_middleTailLinearLoss n h t
  have hleft := sub_le_sub_of_derivatives hu (fun t _ ↦ (hL t).const_mul (W 0))
    (fun t _ ↦ (hD t).const_mul N) (fun t ht ↦ by
      have H := mul_le_mul_of_nonneg_left (hmono ht.1) (mul_nonneg hN (hF t ht.1))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using H)
  have hright := sub_le_sub_of_derivatives hu (fun t _ ↦ (hD t).const_mul N)
    (fun t _ ↦ (hL t).const_mul (W u)) (fun t ht ↦ by
      have H := mul_le_mul_of_nonneg_left (hmono ht.2) (mul_nonneg hN (hF t ht.1))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using H)
  change W 0 * L u ≤ N * D u ∧ N * D u ≤ W u * L u
  simpa only [hD₀, hL₀, mul_zero, sub_zero] using And.intro hleft hright

private theorem middleTailLinearWeight_zero (n : ℕ) (h : ℝ) :
    middleTailLinearWeight n h 0 = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 6 := by
  unfold middleTailLinearWeight
  simp only [mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * ((n + 1 - i : ℕ) : ℝ)) =
        (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * ((n - i : ℕ) : ℝ)) +
          ∑ i ∈ Finset.range n, ((i : ℝ) + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hin := (Finset.mem_range.mp hi).le
      rw [Nat.cast_sub (show i ≤ n + 1 by omega), Nat.cast_sub hin]
      push_cast
      ring
    rw [he, ih, sum_shifted_index]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
    ring

/-- The physical linear coefficient dominates the loss and has a larger logarithmic slope. -/
theorem middleTailLinear_geom_ge_and_logDeriv_ge {n : ℕ} (hn : 0 < n) {h u : ℝ}
    (hh : 0 < h) (hu : 0 < u) :
    let D := middleTailLinearGeom n h
    let L := middleTailLinearLoss n h
    0 < L u ∧ ((n : ℝ) + 2) / 3 * L u ≤ D u ∧
      deriv L u * D u ≤ deriv D u * L u := by
  let N := (n : ℝ) * ((n : ℝ) + 1) / 2
  let D := middleTailLinearGeom n h
  let L := middleTailLinearLoss n h
  let W := middleTailLinearWeight n h
  let F (t : ℝ) := h * (Real.exp (-(h * (n : ℝ) * t)) * (1 - Real.exp (-(h * t))))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp only [N]; positivity
  have hF (t : ℝ) (ht : 0 < t) : 0 < F t := by
    have he := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hh ht))
    exact mul_pos hh (mul_pos (Real.exp_pos _) (sub_pos.mpr he))
  have hD (t : ℝ) : HasDerivAt D (F t * W t) t := hasDerivAt_middleTailLinearGeom n h t
  have hL (t : ℝ) : HasDerivAt L (F t * N) t := hasDerivAt_middleTailLinearLoss n h t
  have hL₀ : L 0 = 0 := by simp [L, middleTailLinearLoss]
  have hLmono : StrictMonoOn L (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun t _ ↦ (hL t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hL t).deriv]
      exact mul_pos (hF t ht) hN
  have hLpos : 0 < L u := by rw [← hL₀]; exact hLmono le_rfl hu.le hu
  obtain ⟨hlo, hhi⟩ := middleTailLinear_ratio_comparison n hh hu.le
  change W 0 * L u ≤ N * D u at hlo
  change N * D u ≤ W u * L u at hhi
  have hW : W 0 = N * (((n : ℝ) + 2) / 3) := by
    rw [middleTailLinearWeight_zero]
    dsimp only [N]
    ring
  refine ⟨hLpos, (mul_le_mul_iff_left₀ hN).mp ?_, ?_⟩
  · rw [← mul_assoc, ← hW]
    exact hlo
  · rw [(hL u).deriv, (hD u).deriv, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hhi (hF u hu).le

/-- The physical coefficients in the separated kernel equal the geometric profiles. -/
theorem middleTailLinear_coefficients {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    let h := 3 / (p : ℝ)
    let n := p + 1
    upperTailLinearA1 h u = 2 * h * middleTailLinearGeom n h u ∧
      1 - upperTailLinearA h u = 2 * middleTailLinearLoss n h u := by
  let h := 3 / (p : ℝ)
  let n := p + 1
  let x := Real.exp (-(h * u))
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hx₁ : 0 < 1 - x := sub_pos.mpr (Real.exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (mul_pos hh hu)))
  have hG : 3 + h = (n : ℝ) * h := by
    dsimp only [h, n]
    push_cast
    field_simp [hp'.ne']
    ring
  have hK : 3 + 2 * h = ((n : ℝ) + 1) * h := by linarith only [hG]
  have hx (i : ℕ) : x ^ i = Real.exp (-(h * (i : ℝ) * u)) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hgn : Real.exp (-((3 + h) * u)) = x ^ n := by rw [hG, hx]; congr 1; ring
  have hkn : Real.exp (-((3 + 2 * h) * u)) = x ^ (n + 1) := by
    rw [hK, hx, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hgap : upperTailGap h u = (1 - x) / h := rfl
  have hgeom : (1 - x ^ (n + 1)) / upperTailGap h u =
      h * ∑ i ∈ Finset.range (n + 1), x ^ i := by
    rw [hgap, ← geom_sum_mul_neg x (n + 1)]
    field_simp [hh.ne', hx₁.ne']
  have hshift : (∑ i ∈ Finset.range n, Real.exp (-(h * ((i : ℝ) + 1) * u))) =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hx, Nat.cast_add, Nat.cast_one]
  change upperTailLinearA1 h u = 2 * h * middleTailLinearGeom n h u ∧
    1 - upperTailLinearA h u = 2 * middleTailLinearLoss n h u
  constructor
  · unfold upperTailLinearA1 middleTailLinearGeom
    rw [hkn, hG, hK, hgeom, hshift, Finset.sum_range_succ', pow_zero]
    rw [show Real.exp (-(h * ((n : ℝ) + 1) * u)) = x ^ (n + 1) by
      rw [hx, Nat.cast_add, Nat.cast_one]]
    ring
  · unfold upperTailLinearA middleTailLinearLoss
    rw [hgn, hG, hgap, ← hx n]
    rw [show Real.exp (-(h * ((n : ℝ) + 1) * u)) = x ^ (n + 1) by
      rw [hx, Nat.cast_add, Nat.cast_one], pow_succ]
    field_simp [hh.ne']
    ring

end RefinedBMV.PositiveCenter
