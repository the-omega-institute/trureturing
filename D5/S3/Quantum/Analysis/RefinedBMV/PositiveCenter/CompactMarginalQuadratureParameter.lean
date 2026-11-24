/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMarginalQuadratureParameter
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parameter differentiation and signed remainders of the scaled marginal quadrature. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadrature
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Parameter derivatives of the regularized marginal and its exact closed-mesh quadrature. -/

noncomputable section

namespace RefinedBMV.PositiveCenter

open D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth (meshRemainder)
open SmallCorner

private def marginalQuadratureWeight (k : ℕ) : ℝ :=
  1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

private theorem marginalQuadratureWeight_abs_le (k : ℕ) :
    |marginalQuadratureWeight k| ≤ 1 := by
  unfold marginalQuadratureWeight
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr <| by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

private theorem contDiff_factorial_series {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, |w n| ≤ C) (t : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ ∑' n : ℕ, w n * t ^ n / n.factorial * x ^ n) := by
  let c (n : ℕ) := w n * t ^ n / n.factorial
  let p := FormalMultilinearSeries.ofScalars ℝ c
  have hr : p.radius = ⊤ := by
    refine p.radius_eq_top_of_summable_norm fun r ↦ ?_
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (|t| * (r : ℝ))).mul_left C)
    simp only [p, FormalMultilinearSeries.ofScalars_norm, c, Real.norm_eq_abs, abs_div, abs_mul,
      abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
    calc
      _ ≤ C * |t| ^ n / n.factorial * (r : ℝ) ^ n := by gcongr; exact hw n
      _ = _ := by ring
  have ha : AnalyticOnNhd ℝ p.sum Set.univ := by
    simpa only [hr, Metric.eball_top] using p.analyticOnNhd
  have hc : ContDiff ℝ ⊤ (FormalMultilinearSeries.ofScalarsSum (E := ℝ) c) := ha.contDiff
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul, c] using hc

private theorem compactClosedQuadrature_const_mul_sub (h c : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    compactClosedQuadrature h (fun x ↦ c * f x - g x) =
      c * compactClosedQuadrature h f - compactClosedQuadrature h g := by
  have hderiv (k : ℕ) (x : ℝ) :
      iteratedDeriv k (fun y ↦ c * f y - g y) x =
        c * iteratedDeriv k f x - iteratedDeriv k g x := by
    rw [iteratedDeriv_fun_sub, iteratedDeriv_const_mul_field]
    · exact (((contDiff_const (c := c)).mul hf).of_le le_top).contDiffAt
    · exact (hg.of_le le_top).contDiffAt
  unfold compactClosedQuadrature
  rw [intervalIntegral.integral_sub
    ((hf.continuous.const_mul c).intervalIntegrable _ _) (hg.continuous.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hderiv, hderiv, hderiv, hderiv]
  ring

private theorem compactClosedQuadrature_monomial_abs_le_geometric {h : ℝ} (hh : 0 ≤ h)
    (k : ℕ) :
    |compactClosedQuadrature h (fun x ↦ x ^ k)| ≤
      (3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ k := by
  have hd (j : ℕ) : (k.descFactorial j : ℝ) ≤ (j.factorial : ℝ) * 2 ^ k := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose k j).le.trans
      (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow k j))
  have h1 : (k : ℝ) ≤ 2 ^ k := by simpa using hd 1
  have hfac : (3 : ℕ).factorial = 6 := by decide
  have h3 : (k.descFactorial 3 : ℝ) ≤ 6 * 2 ^ k := by
    simpa only [hfac, Nat.cast_ofNat] using hd 3
  refine (compactClosedQuadrature_monomial_abs_le hh k).trans ?_
  calc
    _ ≤ (3 + h) * 2 ^ k +
        h ^ 2 / 6 * 2 ^ k * 2 ^ k + h ^ 4 / 360 * (6 * 2 ^ k) * 2 ^ k := by
      gcongr <;> norm_num
    _ ≤ (3 + h) * (2 ^ k * 2 ^ k) +
        h ^ 2 / 6 * 2 ^ k * 2 ^ k + h ^ 4 / 360 * (6 * 2 ^ k) * 2 ^ k := by
      have hone : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      gcongr
      exact le_mul_of_one_le_right (by positivity) hone
    _ = _ := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

private theorem summable_factorial_quadrature_series {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C * 4 ^ n) (t : ℝ) :
    Summable fun n : ℕ ↦ a n * t ^ n / n.factorial := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (4 * |t|)).mul_left C)
    fun n ↦ ?_
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
  calc
    _ ≤ (C * 4 ^ n) * |t| ^ n / n.factorial := by gcongr; exact ha n
    _ = _ := by ring

private def marginalQuadratureCoefficient (h : ℝ) (k : ℕ) : ℝ :=
  marginalQuadratureWeight k *
    ((2 + h) * compactClosedQuadrature h (fun x ↦ x ^ (k + 2)) -
      compactClosedQuadrature h (fun x ↦ x ^ (k + 3)))

private theorem marginalQuadratureCoefficient_abs_le {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    |marginalQuadratureCoefficient h k| ≤
      (16 * (6 + h) * (3 + h + h ^ 2 / 6 + h ^ 4 / 60)) * 4 ^ k := by
  let C := 3 + h + h ^ 2 / 6 + h ^ 4 / 60
  let Q (m : ℕ) := compactClosedQuadrature h (fun x ↦ x ^ m)
  have h23 : 0 ≤ 2 + h := by positivity
  have hdiff : |(2 + h) * Q (k + 2) - Q (k + 3)| ≤
      (2 + h) * (C * 4 ^ (k + 2)) + C * 4 ^ (k + 3) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg h23]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (compactClosedQuadrature_monomial_abs_le_geometric hh _) h23)
      (compactClosedQuadrature_monomial_abs_le_geometric hh _)
  change |marginalQuadratureWeight k * ((2 + h) * Q (k + 2) - Q (k + 3))| ≤ _
  rw [abs_mul]
  calc
    _ ≤ 1 * ((2 + h) * (C * 4 ^ (k + 2)) + C * 4 ^ (k + 3)) :=
      mul_le_mul (marginalQuadratureWeight_abs_le k) hdiff (abs_nonneg _) zero_le_one
    _ = _ := by dsimp only [C]; rw [pow_add, pow_add]; ring

private theorem compactClosedQuadrature_parameter_series {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    compactClosedQuadrature h
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) =
      ∑' n : ℕ, marginalQuadratureCoefficient h (j + n) * t ^ n / n.factorial := by
  let w (n : ℕ) := marginalQuadratureWeight (j + n)
  let f (k : ℕ) (x : ℝ) := ∑' n : ℕ, w n * t ^ n / n.factorial * x ^ (n + k)
  have hsmooth (k : ℕ) : ContDiff ℝ ⊤ (f k) := by
    have hf : f k = fun x ↦ (∑' n : ℕ, w n * t ^ n / n.factorial * x ^ n) * x ^ k := by
      funext x
      rw [← tsum_mul_right]
      exact tsum_congr fun n ↦ by simp only [pow_add, mul_assoc]
    rw [hf]
    exact (contDiff_factorial_series (fun n ↦ marginalQuadratureWeight_abs_le (j + n)) t).mul
      (by fun_prop)
  have hpoint :
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) =
        fun x ↦ (2 + h) * f (j + 2) x - f (j + 3) x := by
    funext x
    unfold regularizedMarginalIntegrand
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_regularizedMarginalRemainder_eq_tsum]
    have hbase : (∑' n : ℕ, (1 / ((((j + n : ℕ) : ℝ) + 1) *
        (((j + n : ℕ) : ℝ) + 2))) * (t ^ n / n.factorial) * x ^ (j + n + 2)) =
        f (j + 2) x := by
      refine tsum_congr fun n ↦ ?_
      rw [show j + n + 2 = n + (j + 2) by omega]
      simp only [w, marginalQuadratureWeight, mul_div_assoc]
    rw [hbase, sub_mul]
    congr 1
    dsimp only [f]
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ by
      rw [show n + (j + 3) = (n + (j + 2)) + 1 by omega, pow_succ]
      ring
  have hQ (k : ℕ) := compactClosedQuadrature_tsum h t k w
    (fun n ↦ marginalQuadratureWeight_abs_le (j + n))
  let A (k n : ℕ) := w n * t ^ n / n.factorial *
    compactClosedQuadrature h (fun x ↦ x ^ (n + k))
  have hsum (k : ℕ) : Summable (A k) := by
    let a (n : ℕ) := w n * compactClosedQuadrature h (fun x ↦ x ^ (n + k))
    have ha (n : ℕ) : |a n| ≤ ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ k) * 4 ^ n := by
      rw [abs_mul]
      calc
        _ ≤ 1 * ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ (n + k)) :=
          mul_le_mul (marginalQuadratureWeight_abs_le (j + n))
            (compactClosedQuadrature_monomial_abs_le_geometric hh _) (abs_nonneg _) zero_le_one
        _ = _ := by rw [pow_add]; ring
    have hterm (n : ℕ) : A k n = a n * t ^ n / n.factorial := by dsimp only [A, a]; ring
    rw [show A k = _ from funext hterm]
    exact summable_factorial_quadrature_series ha t
  rw [hpoint, compactClosedQuadrature_const_mul_sub h (2 + h) (hsmooth _) (hsmooth _),
    hQ, hQ]
  change (2 + h) * (∑' n, A (j + 2) n) - (∑' n, A (j + 3) n) = _
  rw [← tsum_mul_left, ← ((hsum (j + 2)).mul_left (2 + h)).tsum_sub (hsum (j + 3))]
  refine tsum_congr fun n ↦ ?_
  simp only [A, marginalQuadratureCoefficient, w,
    show n + (j + 2) = j + n + 2 by omega, show n + (j + 3) = j + n + 3 by omega]
  ring

private theorem hasDerivAt_factorial_quadrature_series {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C * 4 ^ n) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∑' n : ℕ, a (j + n) * s ^ n / n.factorial)
      (∑' n : ℕ, a (j + 1 + n) * t ^ n / n.factorial) t := by
  have hshift (k n : ℕ) : |a (k + n)| ≤ (C * 4 ^ k) * 4 ^ n := by
    simpa only [pow_add, mul_assoc] using ha (k + n)
  let g (n : ℕ) (s : ℝ) := a (j + n) * s ^ n / n.factorial
  let g' (n : ℕ) (s : ℝ) := match n with
    | 0 => 0
    | n + 1 => a (j + 1 + n) * s ^ n / n.factorial
  have hg (n : ℕ) (s : ℝ) : HasDerivAt (g n) (g' n s) s := by
    cases n with
    | zero => simpa [g, g'] using hasDerivAt_const s (a j)
    | succ n =>
      apply (((hasDerivAt_pow (n + 1) s).const_mul (a (j + (n + 1)))).div_const
        ((n + 1).factorial : ℝ)).congr_deriv
      simp only [g', Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
      rw [show j + (n + 1) = j + 1 + n by omega]
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hn]
  let R := |t| + 1
  let u (n : ℕ) : ℝ := match n with
    | 0 => 0
    | n + 1 => (C * 4 ^ (j + 1)) * ((4 * R) ^ n / n.factorial)
  have hu : Summable u := (summable_nat_add_iff 1).mp
    ((Real.summable_pow_div_factorial (4 * R)).mul_left _)
  have hC : 0 ≤ C := by simpa using (abs_nonneg (a 0)).trans (ha 0)
  have hdom (n : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo (-R) R) : ‖g' n s‖ ≤ u n := by
    cases n with
    | zero => simp [g', u]
    | succ n =>
      have habs := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      have hR : 0 ≤ R := by positivity
      simp only [g', u, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
      calc
        _ ≤ (C * 4 ^ (j + 1) * 4 ^ n) * R ^ n / n.factorial := by
          gcongr
          exact hshift _ _
        _ = _ := by ring
  have ht : t ∈ Set.Ioo (-R) R := by
    exact abs_lt.mp (lt_add_one |t|)
  have hbase : Summable (fun n ↦ g n t) := summable_factorial_quadrature_series (hshift j) t
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n s _ ↦ hg n s) hdom ht hbase ht
  have hs : Summable (fun n ↦ g' n t) := Summable.of_norm_bounded hu (fun n ↦ hdom n t ht)
  rw [hs.tsum_eq_zero_add, show g' 0 t = 0 by rfl, zero_add] at h
  exact h

private theorem hasDerivAt_compactClosedQuadrature_parameter {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s ↦ compactClosedQuadrature h
        (fun x ↦ iteratedDeriv j (fun r ↦ regularizedMarginalIntegrand h r x) s))
      (compactClosedQuadrature h
        (fun x ↦ iteratedDeriv (j + 1) (fun r ↦ regularizedMarginalIntegrand h r x) t)) t := by
  rw [funext (compactClosedQuadrature_parameter_series hh j),
    compactClosedQuadrature_parameter_series hh (j + 1)]
  exact hasDerivAt_factorial_quadrature_series (marginalQuadratureCoefficient_abs_le hh) j t

/-- Parameter differentiation commutes with the closed quadrature, including all
endpoint corrections and the regularized value at zero parameter. -/
theorem iteratedDeriv_compactMarginalQuadrature_eq_closed {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    iteratedDeriv j (compactMarginalQuadrature h) t =
      (2 / compactMarginalMeshDenominator h) * compactClosedQuadrature h
        (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) := by
  induction j generalizing t with
  | zero => simp only [iteratedDeriv_zero, compactMarginalQuadrature]
  | succ j ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact ((hasDerivAt_compactClosedQuadrature_parameter hh j t).const_mul _).deriv

open private hasDerivAt_compactZ_family from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical

/-- The three scaled marginal inputs in the short negative score equal their
closed quadratures plus the corresponding signed mesh remainders. -/
theorem compactScaledMarginal_eq_closed_add_remainder {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (s : ℝ) := (J * compactKappa p) * compactZ p s
    let Q (j : ℕ) := compactClosedQuadrature h
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t)
    q t = Q 0 + meshRemainder (-1) h p
      (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) ∧
    deriv q t = Q 1 + meshRemainder (-1) h p (compactMarginalRemainderFirst h t) ∧
    iteratedDeriv 2 q t = Q 2 + meshRemainder (-1) h p (compactMarginalRemainderSecond h t) := by
  let h : ℝ := 3 / (p : ℝ)
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (s : ℝ) := (J * compactKappa p) * compactZ p s
  let Q (j : ℕ) := compactClosedQuadrature h
    (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t)
  let base (s : ℝ) := compactKappa p * compactZ p s
  let error (s : ℝ) := base s - compactMarginalQuadrature h s
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hbase (k : ℕ) : ContDiff ℝ (k : ℕ) base := by
    rw [← WithTop.coe_natCast]
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    have heq : iteratedDeriv j base =
        fun s ↦ compactKappa p * integralMarginalDerivative p (compactKappa p) j s := by
      funext s
      change iteratedDeriv j (fun r ↦ compactKappa p * compactZ p r) s = _
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_compactZ_eq_integral hp]
    rw [heq]
    exact fun s ↦ ((hasDerivAt_compactZ_family hp j s).const_mul _).differentiableAt
  have hquad (k : ℕ) : ContDiff ℝ (k : ℕ) (compactMarginalQuadrature h) := by
    rw [← WithTop.coe_natCast]
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    rw [funext (iteratedDeriv_compactMarginalQuadrature_eq_closed hh j)]
    exact fun s ↦ ((hasDerivAt_compactClosedQuadrature_parameter hh j s).const_mul _).differentiableAt
  have hcancel (y : ℝ) : J * (2 / compactMarginalMeshDenominator h * y) = y := by
    have hden : compactMarginalMeshDenominator h ≠ 0 := by
      unfold compactMarginalMeshDenominator
      positivity
    rw [show J = compactMarginalMeshDenominator h / 2 by rfl]
    field_simp
  have hscaled (j : ℕ) : iteratedDeriv j q t = Q j + J * iteratedDeriv j error t := by
    have heq : q = fun s ↦ J * base s := by
      funext s
      exact mul_assoc J (compactKappa p) (compactZ p s)
    have hsub : iteratedDeriv j error t =
        iteratedDeriv j base t - iteratedDeriv j (compactMarginalQuadrature h) t :=
      iteratedDeriv_fun_sub (hbase j).contDiffAt (hquad j).contDiffAt
    rw [heq, iteratedDeriv_const_mul_field, hsub, iteratedDeriv_compactMarginalQuadrature_eq_closed hh,
      mul_sub, hcancel]
    dsimp only [Q]
    ring
  have h0 : error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) :=
    compactKappa_mul_compactZ_sub_quadrature hp t
  have h1 : deriv error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderFirst h t) :=
    (compactMarginalQuadrature_error_derivatives hp t).1
  have h2 : iteratedDeriv 2 error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderSecond h t) :=
    (compactMarginalQuadrature_error_derivatives hp t).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero, h0, hcancel, Q] using hscaled 0
  · simpa only [iteratedDeriv_one, h1, hcancel, Q] using hscaled 1
  · simpa only [h2, hcancel] using hscaled 2

end RefinedBMV.PositiveCenter
