/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Regularized
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The regularized correction for the actual zero-centered profile at small positive gaps. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Profile
import Mathlib.Analysis.Calculus.SmoothSeries

/-! A profile identity in which the radical has a regular limit at zero. -/

namespace RefinedBMV.FourSpectrumLift

noncomputable section

open Finset

/-- The positive series obtained by removing the fourth-order zero of the radicand. -/
def zeroCenterRegularizingSeries (h c : ℝ) : ℝ :=
  ∑' n, regularizingCoefficient h n * c ^ n

/-- The exponential difference quotient with its value filled in at zero. -/
def zeroCenterExpQuotient (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp x - 1) / x

/-- The regular quotient in the correction to the normalized geometric sum. -/
def zeroCenterRegularizedCorrection (h c : ℝ) : ℝ :=
  √(27 * (1 + h) * (1 + 2*h) * (1 + 3*h) * zeroCenterRegularizingSeries h c) /
    (3 * (1 + h) * zeroCenterExpQuotient (3*h*c))

private theorem correction_identity {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    let h : ℝ := 1 / p
    let d := 1 - Real.exp (-3*h*c)
    √(rationalizedRadicand c h) / ((p + 1 : ℝ) * d * Real.exp (-3*c/2)) =
      c * zeroCenterRegularizedCorrection h c := by
  let h : ℝ := 1 / p
  let M := 27 * (1 + h) * (1 + 2*h) * (1 + 3*h)
  let B := zeroCenterRegularizingSeries h c
  let t := 3*h*c
  let E := Real.exp (-(3/2 + 3*h)*c)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hP : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hRel : B =
      (Real.exp ((3+6*h)*c) * rationalizedRadicand c h) / (M * c^4) :=
    (hasSum_regularizing_series hc hh).tsum_eq
  have hE : E^2 * Real.exp ((3+6*h)*c) = 1 := by
    dsimp [E]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
    congr 1
    push_cast
    ring
  have hS : rationalizedRadicand c h = (c^2 * E)^2 * (M * B) := by
    have hB := (eq_div_iff (by dsimp [M]; positivity : M * c^4 ≠ 0)).mp hRel
    calc
      rationalizedRadicand c h =
          (E^2 * Real.exp ((3+6*h)*c)) * rationalizedRadicand c h := by rw [hE, one_mul]
      _ = E^2 * (B * (M * c^4)) := by rw [hB]; ring
      _ = _ := by ring
  have hE' : E = Real.exp (-t) * Real.exp (-3*c/2) := by
    dsimp [E, t]
    rw [← Real.exp_add]
    congr 1
    ring
  have hD : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hN : (p + 1 : ℝ) * h = 1 + h := by
    dsimp [h]
    field_simp
  change √(rationalizedRadicand c h) /
      ((p + 1 : ℝ) * (1 - Real.exp (-3*h*c)) * Real.exp (-3*c/2)) = _
  rw [show -3*h*c = -t by dsimp [t]; ring, hS, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by dsimp [E]; positivity : 0 ≤ c^2 * E), hD, hE']
  unfold zeroCenterRegularizedCorrection zeroCenterExpQuotient
  change _ = c * (√(M * B) / (3 * (1+h) * (if t = 0 then 1 else (Real.exp t - 1) / t)))
  rw [ite_eq_right ht.ne', ← hN]
  have ht' : t = 3*h*c := rfl
  field_simp [ht.ne', hP.ne', hh.ne', (Real.exp_pos _).ne']
  rw [ht']
  ring

/-- On positive gaps the actual profile is the normalized geometric sum
minus the gap times the regularized correction. -/
theorem zeroProfile_eq_regularized {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    zeroProfile p c =
      (∑ j ∈ Finset.range (p + 1), Real.exp (-3*c/(p : ℝ)) ^ j) /
        ((p + 1 : ℝ) * Real.exp (-3*c/2)) -
      c * zeroCenterRegularizedCorrection (1 / (p : ℝ)) c := by
  let h : ℝ := 1 / p
  let q := Real.exp (-3*h*c)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    change -3*h*c < 0
    nlinarith [mul_pos hh hc])
  have hg : (1-q) * (∑ j ∈ Finset.range (p + 1), q ^ j) =
      1 - Real.exp (-3*(1+h)*c) := by
    have hq : q ^ (p+1) = Real.exp (-3*(1+h)*c) := by
      dsimp [q, h]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      <;> ring
    rw [← hq]
    linear_combination -(geom_sum_mul q (p+1))
  rw [zeroProfile_eq_rationalized hp hc]
  change (1 - Real.exp (-3*(1+h)*c) - √(rationalizedRadicand c h)) /
    ((p + 1 : ℝ) * (1-q) * Real.exp (-3*c/2)) = _
  rw [sub_div, correction_identity hp hc, ← hg]
  congr 1
  have hq' : -3*c/(p : ℝ) = -3*h*c := by dsimp [h]; ring
  rw [hq']
  change (1-q) * (∑ j ∈ Finset.range (p+1), q^j) /
    ((p+1 : ℝ) * (1-q) * Real.exp (-3*c/2)) =
    (∑ j ∈ Finset.range (p+1), q^j) / ((p+1 : ℝ) * Real.exp (-3*c/2))
  field_simp [(sub_pos.mpr hq1).ne']

#print axioms zeroProfile_eq_regularized


def regularizingDerivativeCoefficient (h : ℝ) (k n : ℕ) : ℝ :=
  ((n+k).factorial : ℝ) / (n.factorial : ℝ) * regularizingCoefficient h (n+k)

/-- The series for the `k`th derivative of the regularizing factor. -/
def zeroCenterRegularizingDerivative (h : ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  ∑' n, regularizingDerivativeCoefficient h k n * c^n

private theorem regularizingDerivativeCoefficient_succ (h : ℝ) (k n : ℕ) :
    regularizingDerivativeCoefficient h (k+1) n =
      (n+1 : ℝ) * regularizingDerivativeCoefficient h k (n+1) := by
  unfold regularizingDerivativeCoefficient
  rw [show n+(k+1) = n+1+k by omega, Nat.factorial_succ n, Nat.cast_mul, Nat.cast_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hs : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem regularizingDerivativeCoefficient_nonneg {h : ℝ} (hh : 0 ≤ h)
    (k n : ℕ) :
    0 ≤ regularizingDerivativeCoefficient h k n := by
  unfold regularizingDerivativeCoefficient
  exact mul_nonneg (by positivity) (regularizingCoefficient_nonneg hh _)

private theorem cast_add_one_le_two_pow (n : ℕ) : (n+1 : ℝ) ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hnon : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith

private def regularizingDerivativeMajorant (k : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  ((k+1 : ℝ) * 9^k) * ((18*R)^n / (n.factorial : ℝ))

private theorem regularizingDerivativeMajorant_summable (k : ℕ) (R : ℝ) :
    Summable (regularizingDerivativeMajorant k R) :=
  (Real.summable_pow_div_factorial (18*R)).mul_left _

private theorem bound_regularizingDerivative {h x R : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1)
    (hx : |x| ≤ R) (k n : ℕ) :
    ‖regularizingDerivativeCoefficient h k n * x^n‖ ≤ regularizingDerivativeMajorant k R n := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hx
  have hcoeff := regularizingCoefficient_le hh hh' (n+k)
  have hnk : ((n+k : ℕ) : ℝ) + 1 ≤ (k+1 : ℝ) * 2^n := by
    push_cast
    have hp := mul_le_mul_of_nonneg_left (cast_add_one_le_two_pow n) (by positivity : 0 ≤ (k+1 : ℝ))
    have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnkfac : ((n+k).factorial : ℝ) ≠ 0 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (regularizingDerivativeCoefficient_nonneg hh _ _)]
  calc
    _ ≤ regularizingDerivativeCoefficient h k n * R^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _)
        (regularizingDerivativeCoefficient_nonneg hh _ _)
    _ ≤ (((n+k : ℕ) : ℝ) + 1) * 9^(n+k) / n.factorial * R^n := by
      unfold regularizingDerivativeCoefficient
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (((n+k).factorial : ℝ) / (n.factorial : ℝ)) *
            ((((n+k : ℕ) : ℝ) + 1) * 9^(n+k) / ((n+k).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hcoeff (by positivity)
        _ = _ := by field_simp
    _ ≤ ((k+1 : ℝ) * 2^n) * 9^(n+k) / n.factorial * R^n := by
      gcongr
    _ = _ := by
      unfold regularizingDerivativeMajorant
      rw [pow_add, show (18 : ℝ) = 2*9 by norm_num, mul_pow, mul_pow]
      ring

private theorem summable_regularizingDerivative {h x R : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1)
    (hx : |x| ≤ R) (k : ℕ) :
    Summable (fun n ↦ regularizingDerivativeCoefficient h k n * x^n) :=
  .of_norm_bounded (regularizingDerivativeMajorant_summable k R)
    (bound_regularizingDerivative hh hh' hx k)

private def regularizingDerivativeTerm (h : ℝ) (k : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => regularizingDerivativeCoefficient h (k+1) n * x^n

private theorem regularizingDerivativeTerm_hasDerivAt (h : ℝ) (k n : ℕ) (x : ℝ) :
    HasDerivAt (fun y ↦ regularizingDerivativeCoefficient h k n * y^n)
      (regularizingDerivativeTerm h k x n) x := by
  cases n with
  | zero =>
    simpa [regularizingDerivativeTerm] using
      hasDerivAt_const x (regularizingDerivativeCoefficient h k 0)
  | succ n =>
    have hp := ((hasDerivAt_id x).pow (n+1)).const_mul (regularizingDerivativeCoefficient h k (n+1))
    simp only [Nat.cast_succ, Nat.add_sub_cancel, id_eq, mul_one] at hp
    change HasDerivAt (fun y ↦ regularizingDerivativeCoefficient h k (n+1) * y^(n+1))
      (regularizingDerivativeCoefficient h (k+1) n * x^n) x
    rw [regularizingDerivativeCoefficient_succ]
    convert hp using 1 <;> first | rfl | ring

/-- On a neighborhood of the entire small-gap rectangle, differentiation
shifts the regularizing series by one order. -/
theorem hasDerivAt_zeroCenterRegularizingDerivative {h c : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1)
    (hc : |c| < 2) (k : ℕ) :
    HasDerivAt (zeroCenterRegularizingDerivative h k)
      (zeroCenterRegularizingDerivative h (k+1) c) c := by
  let u : ℕ → ℝ := fun n ↦ match n with
    | 0 => 0
    | n+1 => regularizingDerivativeMajorant (k+1) 2 n
  have hs : Summable u := (summable_nat_add_iff 1).1 (regularizingDerivativeMajorant_summable _ 2)
  have hS (x : ℝ) (hx : x ∈ Set.Ioo (-2 : ℝ) 2) : |x| ≤ 2 := (abs_lt.mpr hx).le
  have hb (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ioo (-2 : ℝ) 2) :
      ‖regularizingDerivativeTerm h k x n‖ ≤ u n := by
    cases n with
    | zero => simp [u, regularizingDerivativeTerm]
    | succ n => exact bound_regularizingDerivative hh hh' (hS x hx) (k+1) n
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo
    (convex_Ioo (-2 : ℝ) 2).isPreconnected
    (fun n x _ ↦ regularizingDerivativeTerm_hasDerivAt h k n x) hb
    (by norm_num : (0 : ℝ) ∈ Set.Ioo (-2 : ℝ) 2)
    (summable_regularizingDerivative hh hh' (by norm_num : |(0 : ℝ)| ≤ 2) k)
    (abs_lt.mp hc)
  have hsum := summable_regularizingDerivative hh hh' hc.le (k+1)
  have hsum' : Summable (regularizingDerivativeTerm h k c) := (summable_nat_add_iff 1).1 hsum
  rw [hsum'.tsum_eq_zero_add, show regularizingDerivativeTerm h k c 0 = 0 from rfl,
    zero_add] at hd
  exact hd

/-- The original positive series is order zero in the derivative family. -/
theorem zeroCenterRegularizingDerivative_zero (h : ℝ) :
    zeroCenterRegularizingDerivative h 0 = zeroCenterRegularizingSeries h := by
  funext c
  unfold zeroCenterRegularizingDerivative zeroCenterRegularizingSeries
  congr 1
  funext n
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  simp [regularizingDerivativeCoefficient, hf]

#print axioms hasDerivAt_zeroCenterRegularizingDerivative

private theorem factorial_quotient_le_pow (n k : ℕ) :
    ((n+k).factorial : ℝ) / (n.factorial : ℝ) ≤ ((n+k : ℕ) : ℝ)^k := by
  induction k with
  | zero =>
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    simp [hn]
  | succ k ih =>
    rw [Nat.add_succ, Nat.factorial_succ, Nat.cast_mul, mul_div_assoc, pow_succ]
    have hmono : ((n+k : ℕ) : ℝ)^k ≤ ((n+k+1 : ℕ) : ℝ)^k := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.le_succ (n+k)
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (ih.trans hmono) (show 0 ≤ ((n+k+1 : ℕ) : ℝ) by positivity)

private theorem regularizing_weighted_summable {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1) :
    Summable (fun n : ℕ ↦ ((n+81 : ℕ) : ℝ)^4 * regularizingCoefficient h (n+81)) := by
  have hs := summable_regularizingDerivative (R := 16) hh hh' (x := 16)
    (by norm_num : |(16 : ℝ)| ≤ 16) 0
  have hs' : Summable (fun n : ℕ ↦ regularizingCoefficient h n * (16 : ℝ)^n) := by
    have he (n : ℕ) : regularizingDerivativeCoefficient h 0 n = regularizingCoefficient h n := by
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      simp [regularizingDerivativeCoefficient, hf]
    simpa only [he] using hs
  have hle (n : ℕ) : (n : ℝ)^4 ≤ (16 : ℝ)^n := by
    calc
      _ ≤ ((2 : ℝ)^n)^4 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [cast_add_one_le_two_pow n]
      _ = _ := by rw [← pow_mul, mul_comm n, pow_mul]; norm_num
  apply (summable_nat_add_iff
    (f := fun n : ℕ ↦ (n : ℝ)^4 * regularizingCoefficient h n) 81).2
  refine Summable.of_nonneg_of_le (fun n ↦
      mul_nonneg (by positivity) (regularizingCoefficient_nonneg hh n)) ?_ hs'
  intro n
  exact (mul_le_mul_of_nonneg_right (hle n) (regularizingCoefficient_nonneg hh n)).trans_eq
    (mul_comm _ _)

/-- The first eighty-one coefficients bound the regularizing factor and its
first two derivatives, with a common strict error bound on the small-gap box. -/
theorem zeroCenterRegularizingDerivative_bounds {h c : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1)
    (hc : 0 ≤ c) (hc' : c ≤ 1) {k : ℕ} (hk : k ≤ 2) :
    let v := ∑ n ∈ range (81-k), regularizingDerivativeCoefficient h k n * c^n
    v ≤ zeroCenterRegularizingDerivative h k c ∧
      zeroCenterRegularizingDerivative h k c < v + (2 : ℝ)⁻¹ ^ 100 := by
  let N := 81-k
  let f (n : ℕ) := regularizingDerivativeCoefficient h k n * c^n
  let majorant (n : ℕ) := ((n+81 : ℕ) : ℝ)^4 * regularizingCoefficient h (n+81)
  have hf : Summable f := summable_regularizingDerivative (R := 2) hh hh'
    (by rw [abs_of_nonneg hc]; linarith) k
  have htail : Summable (fun n ↦ f (n+N)) := (summable_nat_add_iff N).2 hf
  have hm : Summable majorant := regularizing_weighted_summable hh hh'
  have hpos (n : ℕ) : 0 ≤ f n :=
    mul_nonneg (regularizingDerivativeCoefficient_nonneg hh _ _) (pow_nonneg hc _)
  have hupper (n : ℕ) : f (n+N) ≤ majorant n := by
    dsimp only [f, majorant]
    have he : n+N+k = n+81 := by dsimp [N]; omega
    calc
      _ ≤ regularizingDerivativeCoefficient h k (n+N) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hc hc')
          (regularizingDerivativeCoefficient_nonneg hh _ _)
      _ ≤ _ := by
        rw [mul_one, regularizingDerivativeCoefficient, he]
        refine mul_le_mul_of_nonneg_right ?_ (regularizingCoefficient_nonneg hh _)
        have hr := factorial_quotient_le_pow (n+N) k
        rw [he] at hr
        refine hr.trans ?_
        exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n+81 by omega)) (by omega)
  have hlow : 0 ≤ ∑' n, f (n+N) := tsum_nonneg (fun n ↦ hpos (n+N))
  have hcomp : (∑' n, f (n+N)) < (2 : ℝ)⁻¹ ^ 100 := by
    refine (htail.tsum_le_tsum hupper hm).trans_lt ?_
    simpa [majorant] using compact_series_weighted_remainder hh hh' zero_le_one le_rfl
  change (∑ n ∈ range N, f n) ≤ (∑' n, f n) ∧
    (∑' n, f n) < (∑ n ∈ range N, f n) + (2 : ℝ)⁻¹ ^ 100
  rw [← hf.sum_add_tsum_nat_add N]
  exact ⟨le_add_of_nonneg_right hlow, add_lt_add_right hcomp _⟩

#print axioms zeroCenterRegularizingDerivative_bounds

end
end RefinedBMV.FourSpectrumLift
