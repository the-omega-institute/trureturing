/- GID: D5/S3/Zeros/AltizioGeometricSumDisk
   generality: I
   mirror-B: D5/B/S3/Zeros/AltizioGeometricSumDisk
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The geometric-sum disk bound holds exactly in degrees five, six and seven. -/

/- result:
   proof_shape: content
   escape_witness: none (the module uses the external open-problem resolution basis).
   admission_basis: open-problem-resolution (#20656; Proved)
   Direct frozen dependencies: D5/S3/Analytic/Interpolation/UniformCoefficientBudget.coeffL1
   statement_id: sha256:2d8acbaa0d846f2071e9ad136ff4b66d44df5b3494f1fd80870a93b93637486b.
   Direct frozen dependencies: D5/S3/Weil/InterpolationJets/QuantitativeEvenSeed.quantitativeSeedRadius
   statement_id: sha256:1c9baa1bbb7514e6b83a1900f41ba68377377811de8b0564887bb6f26dcfd9c6.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20656
   The claim keeps the literal finite sum; private proofs apply geom_sum_mul.
   P and Q use Polynomial.dickson; the coefficient mass uses the existing coeffL1.
   boundary_coordinates: proof_shape: bind-only; consumers: boundary_power, boundary_defect, boundary_bound, point_coordinates.
   power_recurrence: proof_shape: bind-only; consumers: boundary_power.
   boundary_power: proof_shape: content; consumers: boundary_defect.
   boundary_defect: proof_shape: content; consumers: boundary_bound, excluded_witness.
   unit_intersection: proof_shape: bind-only; consumers: G_ne_zero.
   G_ne_zero: proof_shape: bind-only; consumers: disk_bound.
   positive_D: proof_shape: bind-only; consumers: boundary_bound.
   boundary_bound: proof_shape: content; consumers: disk_bound.
   disk_bound: proof_shape: content; consumers: result.
   Q_coeff: proof_shape: content; consumers: R_coeff.
   binomial_coeffs: proof_shape: bind-only; consumers: R_coeff.
   R_coeff: proof_shape: content; consumers: R_factor.
   mass_nonneg: proof_shape: bind-only; consumers: tiny_bounds.
   eval_bound: proof_shape: bind-only; consumers: negative_witness.
   R_factor: proof_shape: content; consumers: negative_witness.
   c_negative: proof_shape: bind-only; consumers: negative_witness.
   tiny_bounds: proof_shape: bind-only; consumers: negative_witness, excluded_witness.
   negative_witness: proof_shape: content; consumers: excluded_witness.
   Q_eval: proof_shape: bind-only; consumers: R_eval.
   R_eval: proof_shape: bind-only; consumers: excluded_witness.
   point_coordinates: proof_shape: bind-only; consumers: excluded_witness.
   excluded_witness: proof_shape: content; consumers: result.
   claim: proof_shape: not-applicable (definition);
   P: proof_shape: not-applicable (definition);
   D: proof_shape: not-applicable (definition);
   G: proof_shape: not-applicable (definition);
   Q: proof_shape: not-applicable (definition);
   a: proof_shape: not-applicable (definition);
   b: proof_shape: not-applicable (definition);
   R: proof_shape: not-applicable (definition);
   c: proof_shape: not-applicable (definition);
   point: proof_shape: not-applicable (definition);
-/

import D5.S3.Analytic.Interpolation.UniformCoefficientBudget
import D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed

open D5.S3.Analytic.Interpolation.UniformCoefficientBudget (coeffL1)

/-! Binding conventions for D. Altizio, "Zeros of Stern polynomials in the complex plane", arXiv:2511.03847v1
(5 November 2025).

* Section 2, Notation: "For all positive integers n, we introduce the (non-standard) notation
  (λ)_n := 1 + λ + ⋯ + λ^{n−1}". Here (z)_n is `∑ k ∈ Finset.range n, z ^ k`.
* Section 3: "B := B_1[2] = {|w − 2| ≤ 1}", the closed ball `Metric.closedBall 2 1`.
* Section 4.3, Remark 4: "One might suspect that |(z)_n| ≥ n|z| more generally whenever z ∈ B. … It seems that this
  inequality is true only for n = 5, 6, and 7, but we do not have a proof." -/

namespace D5.S3.Zeros.AltizioGeometricSumDisk

/-- Remark 4: for a positive integer `n`, `|(z)_n| ≥ n|z|` holds for every `z ∈ B` exactly when `n ∈ {5, 6, 7}`. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ((∀ z ∈ Metric.closedBall (2 : ℂ) 1, (n : ℝ) * ‖z‖ ≤ ‖∑ k ∈ Finset.range n, z ^ k‖) ↔
      n = 5 ∨ n = 6 ∨ n = 7)

end D5.S3.Zeros.AltizioGeometricSumDisk


namespace D5.S3.Zeros.AltizioGeometricSumDisk
open Complex
noncomputable section

private def P (n : ℕ) (u : ℝ) : ℝ :=
  (Polynomial.dickson 1 u n).eval ((u + 3) / 2)

private def D (n : ℕ) (u : ℝ) : ℝ := u ^ n + 1 - P n u - (n : ℝ)^2 * u * (u - 1) / 2

private def G (n : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range n, z ^ k

private lemma boundary_coordinates (z : ℂ) (hz : ‖z - 2‖ = 1) :
    1 ≤ ‖z‖^2 ∧ z.re = (‖z‖^2 + 3) / 4 ∧ ‖z - 1‖^2 = (‖z‖^2 - 1) / 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2) hz
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im] at h
  norm_num at h
  have hs : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hr : z.re = (‖z‖^2 + 3) / 4 := by nlinarith
  have hl : 1 ≤ ‖z‖^2 := by
    have ht : 2 ≤ ‖z‖ + ‖z - 2‖ := by
      calc
        (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
        _ = ‖z - (z - 2)‖ := by congr 1; ring
        _ ≤ ‖z‖ + ‖z - 2‖ := norm_sub_le _ _
    nlinarith [norm_nonneg z]
  refine ⟨hl, hr, ?_⟩
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, one_re, one_im,
    sub_zero]
  nlinarith

private lemma power_recurrence (z : ℂ) (n : ℕ) :
    2 * (z ^ (n + 2)).re =
      2 * z.re * (2 * (z ^ (n + 1)).re) - ‖z‖^2 * (2 * (z ^ n).re) := by
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  simp only [mul_re, mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma boundary_power (z : ℂ) (hz : ‖z - 2‖ = 1) (n : ℕ) :
    P n (‖z‖^2) = 2 * (z ^ n).re := by
  have hr := (boundary_coordinates z hz).2.1
  induction n using Nat.twoStepInduction with
  | zero => norm_num [P]
  | one => simp only [P, Polynomial.dickson_one, Polynomial.eval_X, pow_one]; linarith
  | more n ih0 ih1 =>
    simp only [P, Polynomial.dickson_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at ih0 ih1 ⊢
    rw [ih0, ih1, power_recurrence]
    rw [hr]
    ring

private lemma boundary_defect (z : ℂ) (hz : ‖z - 2‖ = 1) (n : ℕ) :
    D n (‖z‖^2) = ‖z - 1‖^2 * (‖G n z‖^2 - (n : ℝ)^2 * ‖z‖^2) := by
  have hg := congrArg (fun w : ℂ => ‖w‖^2) (geom_sum_mul z n)
  change ‖G n z * (z - 1)‖^2 = ‖z^n - 1‖^2 at hg
  rw [norm_mul, mul_pow] at hg
  have hp : ‖z^n - 1‖^2 = (‖z‖^2)^n + 1 - 2 * (z^n).re := by
    simpa [Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm]
      using Complex.normSq_sub (z^n) 1
  dsimp [D]
  rw [boundary_power z hz, ← hp, ← hg, (boundary_coordinates z hz).2.2]
  ring

private lemma unit_intersection (z : ℂ) (hz : ‖z - 2‖ ≤ 1) (hn : ‖z‖ = 1) : z = 1 := by
  have hb : ‖(2 : ℂ) - z‖ ≤ 1 := by rwa [norm_sub_rev]
  have ha : ‖(2 : ℂ) - z‖ = 1 := by
    apply le_antisymm hb
    have h := norm_sub_norm_le (2 : ℂ) z
    norm_num [hn] at h
    exact h
  have he : z = (2 : ℂ) - z :=
    eq_of_norm_eq_of_norm_add_eq (by rw [hn, ha]) (by
      rw [show z + ((2 : ℂ) - z) = 2 by ring, hn, ha]
      norm_num)
  linear_combination (norm := ring_nf) he / 2

private lemma G_ne_zero (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : ‖z - 2‖ ≤ 1) : G n z ≠ 0 := by
  intro hg
  have hp := geom_sum_mul z n
  change G n z * (z - 1) = z^n - 1 at hp
  rw [hg,zero_mul] at hp
  have hzpow : z^n = 1 := by exact sub_eq_zero.mp hp.symm
  have hzunit := Complex.norm_eq_one_of_pow_eq_one hzpow hn.ne'
  have hz1 := unit_intersection z hz hzunit
  subst z
  simp [G, hn.ne'] at hg

private lemma positive_D (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) (u : ℝ) (hu : 1 ≤ u) : 0 ≤ D n u := by
  have ht : 0 ≤ u - 1 := sub_nonneg_of_le hu
  rcases hn with rfl | rfl | rfl
  · have hc : 32 * D 5 u = (u-1)^3 * (340 + 160*(u-1) + 31*(u-1)^2) := by
      norm_num [D, P, Polynomial.dickson]
      ring
    have hpos : 0 ≤ (u-1)^3 * (340 + 160*(u-1) + 31*(u-1)^2) := by positivity
    linarith
  · have hc : 64 * D 6 u = (u-1)^2 * (48 + 1376*(u-1) + 984*(u-1)^2 + 384*(u-1)^3 + 63*(u-1)^4) := by
      norm_num [D, P, Polynomial.dickson]
      ring
    have hpos : 0 ≤ (u-1)^2 * (48 + 1376*(u-1) + 984*(u-1)^2 + 384*(u-1)^3 + 63*(u-1)^4) := by positivity
    linarith
  · have hc : 128 * D 7 u = (u-1)^3 * (4704 + 4592*(u-1) + 2716*(u-1)^2 + 896*(u-1)^3 + 127*(u-1)^4) := by
      norm_num [D, P, Polynomial.dickson]
      ring
    have hpos : 0 ≤ (u-1)^3 * (4704 + 4592*(u-1) + 2716*(u-1)^2 + 896*(u-1)^3 + 127*(u-1)^4) := by positivity
    linarith

private lemma boundary_bound (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) (z : ℂ) (hz : ‖z-2‖ = 1) :
    (n : ℝ) * ‖z‖ ≤ ‖G n z‖ := by
  by_cases hz1 : z = 1
  · subst z
    simp [G]
  have hd := positive_D n hn (‖z‖^2) (boundary_coordinates z hz).1
  rw [boundary_defect z hz n] at hd
  have hzpos : 0 < ‖z - 1‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))
  have hdiff := (mul_nonneg_iff_of_pos_left hzpos).mp hd
  have hnn : 0 ≤ (n : ℝ)*‖z‖ := by positivity
  nlinarith [norm_nonneg (G n z)]

private lemma disk_bound (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) (z : ℂ) (hz : z ∈ Metric.closedBall (2 : ℂ) 1) :
    (n : ℝ) * ‖z‖ ≤ ‖G n z‖ := by
  have hnpos : 0 < n := by rcases hn with rfl | rfl | rfl <;> omega
  have hnnpos : (0 : ℝ) < n := Nat.cast_pos'.mpr hnpos
  have hdiff : Differentiable ℂ (G n) := by
    unfold G
    fun_prop
  have hquot : DiffContOnCl ℂ (fun w : ℂ => w / G n w) (Metric.ball (2 : ℂ) 1) := by
    apply DiffContOnCl.mk_ball
    · intro w hw
      exact (differentiableAt_id.div (hdiff w)
        (G_ne_zero n hnpos w (by simpa [Metric.mem_ball, dist_eq_norm] using (Metric.mem_ball.mp hw).le))).differentiableWithinAt
    · exact continuousOn_id.div hdiff.continuous.continuousOn (fun w hw =>
        G_ne_zero n hnpos w (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw))
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hquot
    (C := (n : ℝ)⁻¹) (fun w hw => by
      have hw' : ‖w-2‖ = 1 := by
        have := Metric.frontier_ball_subset_sphere hw
        simpa [Metric.mem_sphere,dist_eq_norm] using this
      have hb := boundary_bound n hn w hw'
      have hgp : 0 < ‖G n w‖ := norm_pos_iff.mpr (G_ne_zero n hnpos w hw'.le)
      rw [norm_div, div_le_iff₀ hgp]
      exact (le_inv_mul_iff₀ hnnpos).mpr hb)
    (z := z) (by simpa [closure_ball (2 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz)
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (G_ne_zero n hnpos z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)))] at hmax
  exact (le_inv_mul_iff₀ hnnpos).mp hmax

end
end D5.S3.Zeros.AltizioGeometricSumDisk



namespace D5.S3.Zeros.AltizioGeometricSumDisk
open Polynomial
noncomputable section

private def Q (n : ℕ) : ℝ[X] :=
  (Polynomial.dickson 1 (1 + X : ℝ[X]) n).eval (2 + C (1/2) * X)

private def a (n : ℕ) : ℝ := (n : ℝ) * (2 - n) / 2
private def b (n : ℕ) : ℝ := (n : ℝ) * (n - 1) * (n - 3) * (n - 8) / 48

private def R (n : ℕ) : ℝ[X] := (1 + X)^n + 1 - Q n - C ((n : ℝ)^2 / 2) * (1 + X) * X

private def c (n : ℕ) : ℝ := -(n : ℝ)^2 * (n - 5) * (n - 7) / 48

private lemma Q_coeff (n : ℕ) :
    (Q n).coeff 0 = 2 ∧ (Q n).coeff 1 = a n ∧ (Q n).coeff 2 = b n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Q, a, b, Polynomial.dickson]
  | one => norm_num [Q, a, b, Polynomial.dickson]
  | more n ih0 ih1 =>
    simp only [Q, Polynomial.dickson_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at ih0 ih1 ⊢
    rcases ih0 with ⟨h00,h01,h02⟩
    rcases ih1 with ⟨h10,h11,h12⟩
    simp only [add_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_ofNat_mul, mul_assoc, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, h00,h01,h02,h10,h11,h12]
    dsimp [a,b]
    push_cast
    constructor
    · ring
    constructor <;> ring

private lemma binomial_coeffs (n : ℕ) :
    ((1 + X : ℝ[X])^n).coeff 0 = 1 ∧
    ((1 + X : ℝ[X])^n).coeff 1 = (n : ℝ) ∧
    ((1 + X : ℝ[X])^n).coeff 2 = (n : ℝ)*(n - 1)/2 := by
  simp only [Polynomial.coeff_one_add_X_pow, Nat.choose_zero_right, Nat.cast_one,
    Nat.choose_one_right, Nat.cast_choose_two, and_self]

private lemma R_coeff (n : ℕ) :
    (R n).coeff 0 = 0 ∧ (R n).coeff 1 = 0 ∧ (R n).coeff 2 = c n := by
  have hQ := Q_coeff n
  have hB := binomial_coeffs n
  simp only [R, add_mul, mul_add, mul_one, mul_assoc, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_X, Polynomial.coeff_one,
    Polynomial.coeff_X, hQ.1,hQ.2.1,hQ.2.2,hB.1,hB.2.1,hB.2.2]
  norm_num
  dsimp [a,b,c]
  constructor <;> ring

private lemma mass_nonneg (p : ℝ[X]) : 0 ≤ coeffL1 p := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma eval_bound (p : ℝ[X]) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |p.eval t| ≤ coeffL1 p := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht k)]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht ht1)

private lemma R_factor (n : ℕ) : R n = X^2 * (C (c n) + X * (R n).divX.divX.divX) := by
  have h0 := Polynomial.X_mul_divX_add (R n)
  have h1 := Polynomial.X_mul_divX_add (R n).divX
  have h2 := Polynomial.X_mul_divX_add (R n).divX.divX
  simp only [Polynomial.coeff_divX, (R_coeff n).1, (R_coeff n).2.1,
    (R_coeff n).2.2, zero_add, add_zero, Polynomial.C_0] at h0 h1 h2
  calc
    R n = X * (R n).divX := h0.symm
    _ = X * (X * (R n).divX.divX) := congrArg (fun p : ℝ[X] => X*p) h1.symm
    _ = X * (X * (X * (R n).divX.divX.divX + C (c n))) :=
      congrArg (fun p : ℝ[X] => X*(X*p)) h2.symm
    _ = X^2 * (C (c n) + X * (R n).divX.divX.divX) := by ring

private lemma c_negative (n : ℕ) (hn : 0 < n) (h : ¬(n = 5 ∨ n = 6 ∨ n = 7)) :
    c n ≤ -1/2 := by
  by_cases hn8 : n < 8
  · interval_cases n <;> norm_num [c] at *
  · have hn8' : (8 : ℝ) ≤ n := by exact_mod_cast (by omega : 8 ≤ n)
    have hn2 : (64 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    have hprod : (3 : ℝ) ≤ ((n : ℝ) - 5) * (n - 7) := by nlinarith
    have htotal := mul_le_mul hn2 hprod (by norm_num) (by positivity : 0 ≤ (n : ℝ)^2)
    dsimp [c]
    nlinarith

private lemma tiny_bounds (n : ℕ) :
    0 < D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX) ∧
    D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX) ≤ 1 ∧
    D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX) * coeffL1 (R n).divX.divX.divX < 1/4 := by
  have hm := mass_nonneg ((R n).divX.divX.divX)
  have hp : 0 < 4 * (coeffL1 (R n).divX.divX.divX + 1) := by positivity
  dsimp [D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius]
  refine ⟨by positivity, ?_, ?_⟩
  · exact (div_le_one hp).mpr (by linarith)
  · rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hp]
    linarith

private lemma negative_witness (n : ℕ) (hn : 0 < n) (h : ¬(n = 5 ∨ n = 6 ∨ n = 7)) :
    (R n).eval (D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX)) < 0 := by
  have ht := tiny_bounds n
  have hc := c_negative n hn h
  have he := eval_bound ((R n).divX.divX.divX)
    (D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX)) ht.1.le ht.2.1
  have hep := le_trans (le_abs_self _) he
  have hmul := mul_le_mul_of_nonneg_left hep ht.1.le
  conv_lhs => arg 2; rw [R_factor]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos ht.1) (by linarith)

end
end D5.S3.Zeros.AltizioGeometricSumDisk

namespace D5.S3.Zeros.AltizioGeometricSumDisk
noncomputable section
open Complex Polynomial
private lemma Q_eval (n : ℕ) (t : ℝ) : (Q n).eval t = P n (1+t) := by
  change (Polynomial.evalRingHom t)
    ((Polynomial.dickson 1 (1 + X : ℝ[X]) n).eval (2 + C (1/2) * X)) = _
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, Polynomial.map_dickson]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  ring

private lemma R_eval (n : ℕ) (t : ℝ) : (R n).eval t = D n (1+t) := by
  simp only [R,D,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Q_eval]
  ring

private def point (t : ℝ) : ℂ := ⟨(4+t)/4, Real.sqrt (t*(8-t))/4⟩

private lemma point_coordinates (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖point t - 2‖ = 1 ∧ ‖point t‖^2 = 1+t := by
  have hs := Real.sq_sqrt (show 0 ≤ t*(8-t) from mul_nonneg ht (by linarith))
  have hn : ‖point t - 2‖^2 = 1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    norm_num [point]
    nlinarith
  have hz : ‖point t - 2‖ = 1 := by
    nlinarith [norm_nonneg (point t - 2)]
  have hre := (boundary_coordinates (point t) hz).2.1
  change (4+t)/4 = (‖point t‖^2 + 3)/4 at hre
  exact ⟨hz, by linarith⟩

private lemma excluded_witness (n : ℕ) (hn : 0 < n) (h : ¬(n = 5 ∨ n = 6 ∨ n = 7)) :
    ∃ z ∈ Metric.closedBall (2 : ℂ) 1, ‖G n z‖ < (n : ℝ)*‖z‖ := by
  let z := point (D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
    (coeffL1 (R n).divX.divX.divX))
  have ht := tiny_bounds n
  have hz := point_coordinates
    (D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
      (coeffL1 (R n).divX.divX.divX)) ht.1.le ht.2.1
  have hd : D n (‖z‖^2) < 0 := by
    rw [show ‖z‖^2 = 1 +
      D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed.quantitativeSeedRadius
        (coeffL1 (R n).divX.divX.divX) from hz.2, ← R_eval]
    exact negative_witness n hn h
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_closedBall,dist_eq_norm]
    exact hz.1.le
  · rw [boundary_defect z hz.1 n] at hd
    have hgn : 0 ≤ ‖G n z‖ := norm_nonneg _
    have hnz : 0 ≤ (n : ℝ)*‖z‖ := by positivity
    apply lt_of_not_ge
    intro hle
    have hsq : 0 ≤ ‖G n z‖^2-(n : ℝ)^2*‖z‖^2 := by nlinarith
    have := mul_nonneg (sq_nonneg ‖z-1‖) hsq
    linarith

theorem result : claim := by
  intro n hn
  constructor
  · intro h
    by_contra he
    obtain ⟨z,hz,hlt⟩ := excluded_witness n hn he
    have := h z hz
    change (n : ℝ)*‖z‖ ≤ ‖G n z‖ at this
    exact (not_lt_of_ge this) hlt
  · intro he z hz
    exact disk_bound n he z hz



end
end D5.S3.Zeros.AltizioGeometricSumDisk
