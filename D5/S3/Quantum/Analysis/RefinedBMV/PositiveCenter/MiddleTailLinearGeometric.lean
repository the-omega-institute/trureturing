/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailLinearGeometric
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive geometric sum for the ratio of the two linear correction derivatives. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailLinearCoefficients
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

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
      rw [← pow_add, hx (i + 1 + j), hx n]
      have he : Real.exp (-(h * ((i + 1 + j : ℕ) : ℝ) * u)) =
          Real.exp (-(h * (n : ℝ) * u)) * Real.exp (h * ((n - (i + 1 + j) : ℕ) : ℝ) * u) := by
        rw [← Real.exp_add]
        congr 1
        push_cast [Nat.cast_sub hijn]
        ring
      rw [he]
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
      (h * (Real.exp (-(h * (n : ℝ) * u)) * (1 - Real.exp (-(h * u)))) *
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
  have hD₀ : D 0 = 0 := by simp [D, middleTailLinearGeom] <;> ring
  have hL₀ : L 0 = 0 := by simp [L, middleTailLinearLoss] <;> ring
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
  have hL₀ : L 0 = 0 := by simp [L, middleTailLinearLoss] <;> ring
  have hLmono : StrictMonoOn L (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun t _ ↦ (hL t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hL t).deriv]
      exact mul_pos (hF t ht) hN
  have hLpos : 0 < L u := by rw [← hL₀]; exact hLmono self_mem_Ici hu.le hu
  obtain ⟨hlo, hhi⟩ := middleTailLinear_ratio_comparison n hh hu.le
  change W 0 * L u ≤ N * D u at hlo
  change N * D u ≤ W u * L u at hhi
  have hW : W 0 = N * (((n : ℝ) + 2) / 3) := by
    dsimp only [W]
    rw [middleTailLinearWeight_zero]
    dsimp only [N]
    ring
  refine ⟨hLpos, (mul_le_mul_iff_right₀ hN).mp ?_, ?_⟩
  · change N * (((n : ℝ) + 2) / 3 * L u) ≤ N * D u
    rwa [← mul_assoc, ← hW]
  · change deriv L u * D u ≤ deriv D u * L u
    calc
      _ = F u * (N * D u) := by rw [(hL u).deriv]; ring
      _ ≤ F u * (W u * L u) := mul_le_mul_of_nonneg_left hhi (hF u hu).le
      _ = _ := by rw [(hD u).deriv]; ring

/-- The loss keeps a logarithmic slope of at least `2/u - 2h(n+1)/3`. -/
theorem middleTailLinear_loss_logDeriv_ge {n : ℕ} (hn : 0 < n) {h u : ℝ}
    (hh : 0 < h) (hu : 0 < u) :
    2 / u - (2 / 3) * (h * ((n : ℝ) + 1)) ≤
      deriv (middleTailLinearLoss n h) u / middleTailLinearLoss n h u := by
  let N : ℝ := (n : ℝ) * ((n : ℝ) + 1) / 2
  let L := middleTailLinearLoss n h
  let r := h * ((n : ℝ) + 1)
  let w := r * u
  let a := h * N * (Real.exp (h * u) - 1) / u
  let F (s : ℝ) := (a / r ^ 2) * (1 - (1 + r * s) * Real.exp (-(r * s)))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp only [N]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hw : 0 < w := mul_pos hr hu
  have ha : 0 ≤ a := by
    have he := Real.one_le_exp_iff.mpr (mul_nonneg hh.le hu.le)
    dsimp only [a]
    exact div_nonneg (mul_nonneg (mul_nonneg hh.le hN.le) (sub_nonneg.mpr he)) hu.le
  have hL (s : ℝ) : HasDerivAt L (h * N * Real.exp (-(r * s)) * (Real.exp (h * s) - 1)) s := by
    apply (hasDerivAt_middleTailLinearLoss n h s).congr_deriv
    have he₁ : Real.exp (-(r * s)) * Real.exp (h * s) = Real.exp (-(h * (n : ℝ) * s)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [r]
      ring
    have he₂ : Real.exp (-(h * (n : ℝ) * s)) * Real.exp (-(h * s)) = Real.exp (-(r * s)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [r]
      ring
    have he : Real.exp (-(h * (n : ℝ) * s)) * (1 - Real.exp (-(h * s))) =
        Real.exp (-(r * s)) * (Real.exp (h * s) - 1) := by
      simp only [mul_sub, mul_one, he₁, he₂]
    rw [he]
    dsimp only [N]
    ring
  have hF (s : ℝ) : HasDerivAt F (a * s * Real.exp (-(r * s))) s := by
    have hs := ((hasDerivAt_id' s).const_mul r).const_add 1
    have he := hasDerivAt_upperTailLinearDecay r s
    apply ((((hs.mul he).const_sub 1).const_mul (a / r ^ 2))).congr_deriv
    field_simp [hr.ne']
    ring
  have hdom := sub_le_sub_of_derivatives hu.le (fun t _ ↦ hL t) (fun t _ ↦ hF t) (fun t ht ↦ by
    have hc : Real.exp (h * t) - 1 ≤ (Real.exp (h * u) - 1) / u * t := by
      rcases eq_or_lt_of_le ht.1 with ht₀ | ht₀
      · subst t
        simp
      · have H := ConvexOn.secant_mono convexOn_exp (Set.mem_univ (0 : ℝ))
          (Set.mem_univ (h * t)) (Set.mem_univ (h * u)) (mul_pos hh ht₀).ne'
          (mul_pos hh hu).ne' (mul_le_mul_of_nonneg_left ht.2 hh.le)
        simp only [Real.exp_zero, sub_zero] at H
        have H' := (div_le_div_iff₀ (mul_pos hh ht₀) (mul_pos hh hu)).mp H
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hu).mpr
        apply (mul_le_mul_iff_left₀ hh).mp
        nlinarith only [H']
    calc
      _ ≤ h * N * Real.exp (-(r * t)) * ((Real.exp (h * u) - 1) / u * t) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by dsimp only [a]; ring)
  have hL₀ : L 0 = 0 := by simp [L, middleTailLinearLoss] <;> ring
  have hF₀ : F 0 = 0 := by simp [F]
  rw [hL₀, hF₀, sub_zero, sub_zero] at hdom
  have hLpos := (middleTailLinear_geom_ge_and_logDeriv_ge hn hh hu).1
  change 0 < L u at hLpos
  apply (le_div_iff₀ hLpos).mpr
  change (2 / u - (2 / 3) * r) * L u ≤ deriv L u
  rw [(hL u).deriv]
  have hscale : u * (2 / u - (2 / 3) * r) = 2 - (2 / 3) * w := by
    dsimp only [w]
    field_simp [hu.ne'] <;> ring
  by_cases hbig : 3 ≤ w
  · have H : 2 / u - (2 / 3) * r ≤ 0 := by
      apply nonpos_of_mul_nonpos_right _ hu
      rw [hscale]
      linarith only [hbig]
    exact (mul_nonpos_of_nonpos_of_nonneg H hLpos.le).trans (by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))))
  · have hsmall : w / 3 < 1 := by linarith only [lt_of_not_ge hbig]
    have hremain := compactExp_sub_truncation_geometric_le (z := w) (R := w) (m := 2)
      (by decide) (by rw [abs_of_pos hw]) (by simpa using hsmall)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hremain
    have hge : Real.exp w - 1 - w ≤ w ^ 2 / 2 / (1 - w / 3) := by
      linarith only [(le_abs_self _).trans hremain]
    have hfactor : 0 ≤ 2 / u - (2 / 3) * r := by
      apply nonneg_of_mul_nonneg_right _ hu
      rw [hscale]
      linarith only [hsmall]
    calc
      _ ≤ (2 / u - (2 / 3) * r) * F u := mul_le_mul_of_nonneg_left hdom hfactor
      _ = ((2 / u - (2 / 3) * r) * (a / r ^ 2) * Real.exp (-w)) *
          (Real.exp w - 1 - w) := by
        have he : Real.exp (-w) * Real.exp w = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        dsimp only [F]
        change _ = _
        rw [show r * u = w by rfl]
        ring_nf at he ⊢
        rw [he]
        ring
      _ ≤ ((2 / u - (2 / 3) * r) * (a / r ^ 2) * Real.exp (-w)) *
          (w ^ 2 / 2 / (1 - w / 3)) := mul_le_mul_of_nonneg_left hge (by positivity)
      _ = _ := by
        have hw' : 1 - w / 3 ≠ 0 := (sub_pos.mpr hsmall).ne'
        have hw'' : 3 - u * r ≠ 0 := by
          apply ne_of_gt
          dsimp only [w] at hsmall
          nlinarith only [hsmall]
        dsimp only [w] at hw'
        dsimp only [w, a]
        field_simp [hr.ne', hu.ne', hw', hw''] <;> ring

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
    field_simp [hp'.ne'] <;> ring
  have hK : 3 + 2 * h = ((n : ℝ) + 1) * h := by linarith only [hG]
  have hx (i : ℕ) : x ^ i = Real.exp (-(h * (i : ℝ) * u)) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hgn : Real.exp (-((3 + h) * u)) = x ^ n := by rw [hG, hx]; congr 1; ring
  have hnext : Real.exp (-(h * ((n : ℝ) + 1) * u)) = x ^ (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (hx (n + 1)).symm
  have hkn : Real.exp (-((3 + 2 * h) * u)) = x ^ (n + 1) := by
    rw [hK, mul_comm ((n : ℝ) + 1) h]
    exact hnext
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
    rw [hnext]
    ring
  · unfold upperTailLinearA middleTailLinearLoss
    rw [hgn, hG, hgap, ← hx n]
    rw [hnext, pow_succ]
    field_simp [hh.ne']
    ring

/-- The physical gap weight exceeds the bound needed for the linear mixed derivative. -/
theorem middleTailLinear_gap_weight_gt {h d : ℝ} (hh : 0 < h) (hh₁ : h ≤ 3 / 11)
    (hd : 3 ≤ d) : (5 / 2 : ℝ) < (1 + h) * upperTailGap h d := by
  have hp : 0 < 1 - (3 / 2 : ℝ) * h := by linarith
  have hpoly := Real.sum_le_exp_of_nonneg (show 0 ≤ 3 * h by positivity) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hpoly
  have hfact : 0 < h * (1 - 3 * h) * (9 * h ^ 2 + 6 * h + 2) / 4 := by
    have ht : 0 < 1 - 3 * h := by linarith
    positivity
  have hle := mul_le_mul_of_nonneg_left hpoly hp.le
  have hscale : 1 + h < (1 - (3 / 2 : ℝ) * h) * Real.exp (3 * h) := by
    nlinarith only [hle, hfact]
  have hdiv := (div_lt_iff₀ (Real.exp_pos (3 * h))).mpr hscale
  have hexp : Real.exp (-(h * d)) ≤ (Real.exp (3 * h))⁻¹ := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hd hh.le])
  have hf : (1 + h) * Real.exp (-(h * d)) < 1 - (3 / 2 : ℝ) * h := by
    have hx := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 + h by positivity)
    exact hx.trans_lt (by simpa only [div_eq_mul_inv] using hdiv)
  unfold upperTailGap
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hh).mpr
  linarith only [show (1 + h) * (1 - Real.exp (-(h * d))) =
    1 + h - (1 + h) * Real.exp (-(h * d)) by ring, hf]

/-- The mixed derivative of the linear remainder has a strict negative margin from gap three. -/
theorem middleTailLinear_mixed_scalar_neg {L D L' D' y z j eta w c : ℝ}
    (hL : 0 < L) (hw : 0 < w) (hD : c * L ≤ D) (hderiv : L' * D ≤ D' * L)
    (hy : 1 ≤ y) (hj₀ : 0 ≤ j) (hj : j ≤ 1 / 3) (heta : eta ≤ 1 / 9)
    (hs : 1 / 2 ≤ z + L' / L) (hc : 5 / 2 < c * w) :
    let s := z + L' / L
    (-y * (z * D + D') + L * ((y + j) * (s + j) + eta) / w < 0) := by
  let s := z + L' / L
  have hy₀ : 0 < y := by linarith
  have hs₀ : 0 < s := by change (1 / 2 : ℝ) ≤ s at hs; linarith
  have hlow : L' / L * D ≤ D' := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hL).mpr hderiv
  have hmain : y * s * (c * L) ≤ y * (z * D + D') := calc
    _ ≤ y * s * D := mul_le_mul_of_nonneg_left hD (mul_nonneg hy₀.le hs₀.le)
    _ = y * (s * D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      change (z + L' / L) * D ≤ z * D + D'
      rw [add_mul]
      exact add_le_add (le_refl _) hlow) hy₀.le
  have hpair : (y + j) * (s + j) ≤ ((4 / 3) * y) * ((5 / 3) * s) := by
    have hyj : y + j ≤ (4 / 3) * y := by linarith only [hy, hj]
    have hsj : s + j ≤ (5 / 3) * s := by linarith only [hs, hj]
    exact mul_le_mul hyj hsj (add_nonneg hs₀.le hj₀) (by positivity)
  have hys : (1 / 2 : ℝ) ≤ y * s := by
    have H := mul_le_mul_of_nonneg_right hy hs₀.le
    linarith only [H, hs]
  have hcap : (y + j) * (s + j) + eta ≤ (22 / 9) * (y * s) := by
    have he : ((4 / 3 : ℝ) * y) * ((5 / 3) * s) = (20 / 9) * (y * s) := by ring
    rw [he] at hpair
    linarith only [hpair, heta, hys]
  have hstrict : (22 / 9 : ℝ) < c * w := lt_trans (by norm_num) hc
  have hmargin : L * ((22 / 9) * (y * s)) / w < y * s * (c * L) := by
    apply (div_lt_iff₀ hw).mpr
    have H := mul_lt_mul_of_pos_left hstrict (mul_pos hL (mul_pos hy₀ hs₀))
    convert H using 1 <;> ring
  have hend := ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcap hL.le) hw.le).trans_lt
    hmargin).trans_le hmain
  change -y * (z * D + D') + L * ((y + j) * (s + j) + eta) / w < 0
  linarith only [hend]

end RefinedBMV.PositiveCenter
