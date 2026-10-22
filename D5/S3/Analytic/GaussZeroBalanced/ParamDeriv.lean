/- GID: D5/S3/Analytic/GaussZeroBalanced/ParamDeriv
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/ParamDeriv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Parameter differentiation, mixed derivatives and the sharp first Gauss quotient classification. -/

import D5.S3.Analytic.GaussZeroBalanced.Series
import D5.S3.Analytic.GaussZeroBalanced.Comparison
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped BigOperators
open scoped Topology
open D5.S3.Analytic.GaussZeroBalanced.Defs
open D5.S3.Analytic.GaussZeroBalanced.Series

namespace D5.S3.Analytic.GaussZeroBalanced.ParamDeriv

/-! The parameter quotient rule separates numerator and denominator derivatives. -/
theorem hasDerivAt_f_param_of_gauss {a b x dN dD : ℝ}
    (hN : HasDerivAt (fun β : ℝ => gauss a β (a + β + 1) x) dN b)
    (hD : HasDerivAt (fun β : ℝ => gauss a β (a + β) x) dD b)
    (hD0 : gauss a b (a + b) x ≠ 0) :
    HasDerivAt (fun β : ℝ => f a β x)
      ((dN * gauss a b (a + b) x -
          gauss a b (a + b + 1) x * dD) /
        (gauss a b (a + b) x) ^ 2) b := by
  change HasDerivAt
    ((fun β : ℝ => gauss a β (a + β + 1) x) /
      (fun β : ℝ => gauss a β (a + β) x)) _ b
  exact hN.div hD hD0

/-! Differentiating the Riccati relation is a local algebraic step.  The
identity is stated for arbitrary functions; this keeps the parameter-series
argument separate from the calculus used by the classification. -/
theorem parameter_riccati_deriv {a b x : ℝ} {F K : ℝ → ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : x ≠ 1)
    (hF : HasDerivAt F (deriv F b) b)
    (hK : HasDerivAt K (deriv K b) b)
    (hEq : ∀ᶠ β : ℝ in 𝓝 b,
      x * K β = (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2) :
    x * deriv K b +
        ((a + b) + 2 * (a * b / (a + b)) * (x / (1 - x)) * F b) * deriv F b =
      (1 - F b) - (a ^ 2 / (a + b) ^ 2) * (x / (1 - x)) * (F b) ^ 2 := by
  have hab : a + b ≠ 0 := by positivity
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hc : HasDerivAt (fun β : ℝ => a + β) 1 b := by
    convert (hasDerivAt_const b a).add (hasDerivAt_id b) using 1
    · funext β
      rfl
    · norm_num
  have h1F : HasDerivAt (fun β : ℝ => 1 - F β) (-deriv F b) b := by
    convert (hasDerivAt_const b (1 : ℝ)).sub hF using 1
    ring
  have hleft : HasDerivAt (fun β : ℝ => x * K β) (x * deriv K b) b :=
    hK.const_mul x
  have hcoef : HasDerivAt (fun β : ℝ => a * β / (a + β))
      (a ^ 2 / (a + b) ^ 2) b := by
    have hn : HasDerivAt (fun β : ℝ => a * β) a b := by
      convert (hasDerivAt_const b a).mul (hasDerivAt_id b) using 1
      · funext β
        rfl
      · ring
    have hd := hn.div hc hab
    convert hd using 1
    field_simp <;> ring
  have hsq : HasDerivAt (fun β => (F β) ^ 2) (2 * F b * deriv F b) b := by
    convert hF.pow 2 using 1 <;> ring
  have hright : HasDerivAt
      (fun β => (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2)
      ((1 - F b) - (a + b) * deriv F b -
        (a ^ 2 / (a + b) ^ 2) * (x / (1 - x)) * (F b) ^ 2 -
        (a * b / (a + b)) * (x / (1 - x)) * (2 * F b * deriv F b)) b := by
    have hp := hc.mul h1F
    have hq := (hcoef.const_mul (x / (1 - x))).mul hsq
    have hs := hp.sub hq
    convert hs using 1
    · funext β
      dsimp
      ring
    · ring
  have heq : (fun β => x * K β) =ᶠ[𝓝 b]
      (fun β => (a + β) * (1 - F β) -
        (a * β / (a + β)) * (x / (1 - x)) * (F β) ^ 2) :=
    hEq
  have hder := hleft.congr_of_eventuallyEq heq.symm
  have hder' := hder.deriv
  rw [hright.deriv] at hder'
  linear_combination -hder'

private def binomialCoeff (a : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval a / (n.factorial : ℝ)

private lemma coefficient_product (a b s : ℝ) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b (a + b + s) n =
      binomialCoeff a n * ∏ j ∈ Finset.range n, (b + j) / (a + b + s + j) := by
  induction n with
  | zero => simp [ordinaryHypergeometricCoefficient, binomialCoeff]
  | succ n ih =>
    simp only [ordinaryHypergeometricCoefficient, binomialCoeff, div_eq_mul_inv] at ih ⊢
    simp only [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, mul_inv_rev, Finset.prod_range_succ]
    calc
      _ = ((n : ℝ) + 1)⁻¹ * (a + n) *
          ((n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval a *
          (ascPochhammer ℝ n).eval b * ((ascPochhammer ℝ n).eval (a+b+s))⁻¹) *
          ((b+n) * (a+b+s+n)⁻¹) := by ring
      _ = _ := by rw [ih]; ring

private lemma ratio_param {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a + s) (j : ℕ) :
    HasDerivAt (fun β : ℝ => (β+j)/(a+β+s+j))
      ((a+s)/(a+b+s+j)^2) b ∧
    0 ≤ (b+j)/(a+b+s+j) ∧ (b+j)/(a+b+s+j) ≤ 1 ∧
    0 ≤ (a+s)/(a+b+s+j)^2 ∧ (a+s)/(a+b+s+j)^2 ≤ 1/b := by
  have hc : 0 < a+b+s+j := by have hj := Nat.cast_nonneg (α := ℝ) j; linarith
  have hd : HasDerivAt (fun β : ℝ => a+β+s+j) 1 b := by
    simpa only [id_eq] using (((hasDerivAt_id b).const_add a).add_const s).add_const (j : ℝ)
  have hn := (hasDerivAt_id b).add_const (j : ℝ)
  refine ⟨?_, by positivity, (div_le_one hc).2 (by linarith), (div_pos hs (sq_pos_of_pos hc)).le, ?_⟩
  · convert hn.div hd hc.ne' using 1
    · rfl
    · dsimp; ring
  · apply (div_le_div_iff₀ (sq_pos_of_pos hc) hb).2
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [sq_nonneg (a+s+j), mul_nonneg (show 0 ≤ a+s+j by have hj := Nat.cast_nonneg (α := ℝ) j; linarith) hb.le]

private lemma product_param {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a + s) (n : ℕ) :
    let d := ∑ i ∈ Finset.range n,
      (∏ j ∈ (Finset.range n).erase i, (b+j)/(a+b+s+j)) *
        ((a+s)/(a+b+s+i)^2)
    HasDerivAt (fun β : ℝ => ∏ j ∈ Finset.range n, (β+j)/(a+β+s+j)) d b ∧
      0 ≤ d ∧ d ≤ (n : ℝ)/b := by
  dsimp
  refine ⟨?_, Finset.sum_nonneg (fun i _ => mul_nonneg
    (Finset.prod_nonneg (fun j _ => (ratio_param ha hb hs j).2.1))
    (ratio_param ha hb hs i).2.2.2.1), ?_⟩
  · simpa only [smul_eq_mul] using HasDerivAt.fun_finsetProd
      (u := Finset.range n) (fun i _ => (ratio_param ha hb hs i).1)
  · calc
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ)/b := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ 1 * ((a+s)/(a+b+s+i)^2) :=
            mul_le_mul_of_nonneg_right
              (Finset.prod_le_one₀ (fun j _ => (ratio_param ha hb hs j).2.1)
                (fun j _ => (ratio_param ha hb hs j).2.2.1))
              (ratio_param ha hb hs i).2.2.2.1
          _ ≤ 1/b := by simpa using (ratio_param ha hb hs i).2.2.2.2
      _ = _ := by simp [div_eq_mul_inv]

private lemma coefficient_param {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a + s) (n : ℕ) :
    HasDerivAt (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n)
      (deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b) b ∧
    0 ≤ deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b ∧
    deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b ≤
      (n : ℝ) * binomialCoeff a n / b := by
  have hp := product_param ha hb hs n
  have hnon : 0 ≤ binomialCoeff a n := by
    unfold binomialCoeff
    exact (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
  have h := hp.1.const_mul (binomialCoeff a n)
  simp only [← coefficient_product] at h
  refine ⟨h.congr_deriv h.deriv.symm, ?_, ?_⟩
  · rw [h.deriv]
    exact mul_nonneg hnon hp.2.1
  · rw [h.deriv]
    calc
      _ ≤ binomialCoeff a n * ((n : ℝ)/b) := mul_le_mul_of_nonneg_left hp.2.2 hnon
      _ = _ := by ring

private lemma summable_binomial (a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hr1 : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^k * binomialCoeff a n * r^n) := by
  let p := ordinaryHypergeometricSeries ℝ a 1 1
  have hrad : p.radius = 1 := by
    apply ordinaryHypergeometricSeries_radius_eq_one
    intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    exact ⟨by linarith, by linarith, by linarith⟩
  let rN : NNReal := ⟨r, hr⟩
  have hlt : (rN : ENNReal) < p.radius := by
    rw [hrad]
    exact_mod_cast hr1
  obtain ⟨ρ, hρ, C, hC, hbound⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius (r := rN) hlt
  have heq (n : ℕ) : ‖p n‖ = binomialCoeff a n := by
    have hn0 : (n.factorial : ℝ) ≠ 0 := by positivity
    have hp0 := (ascPochhammer_pos n a ha).le
    simp only [p, ordinaryHypergeometricSeries, FormalMultilinearSeries.ofScalars_norm]
    simp only [ordinaryHypergeometricCoefficient, ascPochhammer_eval_one]
    rw [mul_inv_cancel_right₀ hn0]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hp0)]
    simp [binomialCoeff, div_eq_mul_inv, mul_comm]
  have hs := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := ρ) k
    (by simpa [Real.norm_eq_abs, abs_of_pos hρ.1] using hρ.2)).mul_left C
  apply Summable.of_nonneg_of_le (fun n => by
    have : 0 ≤ binomialCoeff a n := (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
    positivity) _ hs
  intro n
  calc
    _ = (n : ℝ)^k * (binomialCoeff a n * r^n) := by ring
    _ ≤ (n : ℝ)^k * (C * ρ^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := hbound n
      change ‖p n‖ * r^n ≤ C * ρ^n at hh
      rw [heq] at hh
      exact hh
    _ = _ := by ring

/-- Parameter differentiation of the zero-balanced Gauss series and its lower-parameter shifts. -/
theorem hasDerivAt_gauss_param {a b s x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a+s) (hx : |x| < 1) :
    HasDerivAt (fun β : ℝ => gauss a β (a+β+s) x)
      (∑' n : ℕ, deriv (fun β : ℝ =>
        ordinaryHypergeometricCoefficient a β (a+β+s) n) b * x^n) b := by
  let C : ℕ → ℝ → ℝ := fun n β => ordinaryHypergeometricCoefficient a β (a+β+s) n
  let d : ℕ → ℝ → ℝ := fun n β => deriv (C n) β * x^n
  have hsum : Summable (fun n : ℕ => C n b * x^n) := by
    let p := ordinaryHypergeometricSeries ℝ a b (a+b+s)
    have hr : p.radius = 1 := by
      apply ordinaryHypergeometricSeries_radius_eq_one
      intro n
      have hn := Nat.cast_nonneg (α := ℝ) n
      exact ⟨by linarith, by linarith, by linarith⟩
    have hm : x ∈ Metric.eball (0:ℝ) p.radius := by
      rw [hr]
      simpa [Metric.mem_eball, edist_dist, Real.dist_eq, ENNReal.ofReal_lt_one] using hx
    simpa only [p, C, ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] using p.summable hm
  have hu : Summable (fun n : ℕ => (n : ℝ) * binomialCoeff a n / (b/2) * |x|^n) := by
    convert (summable_binomial a |x| ha (abs_nonneg x) hx 1).mul_left (1/(b/2)) using 1
    ext n
    simp only [pow_one]
    ring
  have hd : HasDerivAt (fun β => ∑' n, C n β * x^n) (∑' n, d n b) b := by
    apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
      (convex_Ioo (b/2) (2*b)).isPreconnected
      (t := Ioo (b/2) (2*b)) (y₀ := b)
    · intro n β hβ
      exact ((coefficient_param ha (by linarith [hβ.1] : 0 < β) hs n).1).mul_const (x^n)
    · intro n β hβ
      have hβ0 : 0 < β := by linarith [hβ.1]
      have hdβ := coefficient_param ha hβ0 hs n
      change ‖deriv (C n) β * x^n‖ ≤ _
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hdβ.2.1, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg x) n)
      calc
        _ ≤ (n : ℝ) * binomialCoeff a n / β := hdβ.2.2
        _ ≤ (n : ℝ) * binomialCoeff a n / (b/2) := by
          apply div_le_div_of_nonneg_left _ (by linarith) hβ.1.le
          exact mul_nonneg (Nat.cast_nonneg n)
            (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
    · constructor <;> linarith
    · exact hsum
    · constructor <;> linarith
  simpa only [gauss, ordinaryHypergeometric_eq_tsum, smul_eq_mul, C, d,
    ordinaryHypergeometricCoefficient] using hd

/-- Parameter differentiation of the contiguous quotient, with its convergent-series derivative. -/
theorem hasDerivAt_f_param {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (fun β : ℝ => f a β x) (deriv (fun β : ℝ => f a β x) b) b := by
  have hxabs : |x| < 1 := by simpa [abs_of_nonneg hx] using hx1
  have hN := hasDerivAt_gauss_param (s := 1) ha hb (by linarith) hxabs
  have hD := hasDerivAt_gauss_param (s := 0) ha hb (by simpa using ha) hxabs
  simp only [add_zero] at hD
  have h := hasDerivAt_f_param_of_gauss hN hD (gauss_pos ha hb (by linarith) hx hx1).ne'
  exact h.congr_deriv h.deriv.symm

private lemma summable_derivative_majorant {a L r : ℝ} (ha : 0 < a)
    (hL : 0 < L) (hr : 0 < r) (hr1 : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) * ((n : ℝ)^k * binomialCoeff a n / L) * r^(n-1)) := by
  have heq (n : ℕ) :
      (n : ℝ) * ((n : ℝ)^k * binomialCoeff a n / L) * r^(n-1) =
        (n : ℝ)^(k+1) * binomialCoeff a n * r^n / (L*r) := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
      <;> ring
  simp_rw [heq]
  exact (summable_binomial a r ha hr.le hr1 (k+1)).div_const (L*r)

private lemma hasDerivAt_controlled_series {a L x : ℝ} {v : ℕ → ℝ}
    (ha : 0 < a) (hL : 0 < L) (k : ℕ)
    (hv : ∀ n, |v n| ≤ (n : ℝ)^k * binomialCoeff a n / L)
    (hx : |x| < 1) :
    HasDerivAt (fun z : ℝ => ∑' n : ℕ, v n * z^n)
      (∑' n : ℕ, (n : ℝ) * v n * x^(n-1)) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  apply hasDerivAt_tsum_of_isPreconnected
    (summable_derivative_majorant ha hL hr hr1 k) isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected (t := Ioo (-r) r) (y₀ := 0) (y := x)
    (g := fun n z => v n * z^n)
    (g' := fun n z => (n : ℝ) * v n * z^(n-1))
  · intro n z _
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_pow n z).const_mul (v n)
  · intro n z hz
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hv n) (Nat.cast_nonneg n)
    · exact pow_le_pow_left₀ (abs_nonneg z) (abs_lt.mpr hz).le _
    · positivity
    · have hp : 0 ≤ binomialCoeff a n :=
        (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
      positivity
  · exact ⟨by linarith, hr⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp only [zero_pow hn0, mul_zero]
  · exact abs_lt.mp hxr

private lemma coefficient_bound {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a+s) (n : ℕ) :
    |ordinaryHypergeometricCoefficient a b (a+b+s) n| ≤ binomialCoeff a n := by
  rw [coefficient_product, abs_mul]
  have hp : 0 ≤ binomialCoeff a n :=
    (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
  have hp0 : 0 ≤ ∏ j ∈ Finset.range n, (b+j)/(a+b+s+j) :=
    Finset.prod_nonneg (fun j _ => (ratio_param ha hb hs j).2.1)
  rw [abs_of_nonneg hp, abs_of_nonneg hp0]
  calc
    _ ≤ binomialCoeff a n * 1 := mul_le_mul_of_nonneg_left
      (Finset.prod_le_one₀ (fun j _ => (ratio_param ha hb hs j).2.1)
        (fun j _ => (ratio_param ha hb hs j).2.2.1)) hp
    _ = _ := mul_one _

private lemma hasDerivAt_gauss_series {a b s x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a+s) (hx : |x| < 1) :
    HasDerivAt (gauss a b (a+b+s))
      (∑' n : ℕ, (n : ℝ) * ordinaryHypergeometricCoefficient a b (a+b+s) n * x^(n-1)) x := by
  have h := hasDerivAt_controlled_series (v := fun n => ordinaryHypergeometricCoefficient a b (a+b+s) n) (L := 1) ha zero_lt_one 0
    (fun n => by simpa only [pow_zero, one_mul, div_one] using coefficient_bound ha hb hs n) hx
  change HasDerivAt (fun z : ℝ => gauss a b (a+b+s) z) _ x
  simpa only [gauss, ordinaryHypergeometric_eq_tsum, smul_eq_mul,
    ordinaryHypergeometricCoefficient] using h

/-- The parameter derivative of the Gauss series, as a power series in its argument. -/
noncomputable def gaussParam (a b s x : ℝ) : ℝ :=
  ∑' n : ℕ, deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b * x^n

/-- Differentiation of the parameter-derivative series in the argument. -/
theorem hasDerivAt_gaussParam {a b s x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a+s) (hx : |x| < 1) :
    HasDerivAt (gaussParam a b s)
      (∑' n : ℕ, (n : ℝ) *
        deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b * x^(n-1)) x := by
  exact hasDerivAt_controlled_series (v := fun n => deriv (fun β : ℝ => ordinaryHypergeometricCoefficient a β (a+β+s) n) b) ha hb 1 (fun n => by
    rw [abs_of_nonneg (coefficient_param ha hb hs n).2.1, pow_one]
    exact (coefficient_param ha hb hs n).2.2) hx

/-- The mixed derivative series also differentiates the argument derivative in the parameter. -/
theorem hasDerivAt_gauss_mixed {a b s x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < a+s) (hx : |x| < 1) :
    HasDerivAt (fun β : ℝ => deriv (gauss a β (a+β+s)) x)
      (deriv (gaussParam a b s) x) b := by
  let C : ℕ → ℝ → ℝ := fun n β => ordinaryHypergeometricCoefficient a β (a+β+s) n
  let d : ℕ → ℝ → ℝ := fun n β => (n : ℝ) * deriv (C n) β * x^(n-1)
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hsum : Summable (fun n : ℕ => (n : ℝ) * C n b * x^(n-1)) := by
    apply Summable.of_norm_bounded (summable_derivative_majorant ha zero_lt_one hr hr1 0)
    intro n
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    apply mul_le_mul
    · simpa only [pow_zero, one_mul, div_one, C] using mul_le_mul_of_nonneg_left (coefficient_bound ha hb hs n) (Nat.cast_nonneg (α := ℝ) n)
    · exact pow_le_pow_left₀ (abs_nonneg x) hxr.le _
    · positivity
    · have hp : 0 ≤ binomialCoeff a n :=
        (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
      positivity
  have hd : HasDerivAt (fun β => ∑' n : ℕ, (n : ℝ) * C n β * x^(n-1))
      (∑' n : ℕ, d n b) b := by
    apply hasDerivAt_tsum_of_isPreconnected
      (summable_derivative_majorant ha (by linarith : 0 < b/2) hr hr1 1)
      isOpen_Ioo (convex_Ioo (b/2) (2*b)).isPreconnected
      (t := Ioo (b/2) (2*b)) (y₀ := b)
    · intro n β hβ
      exact (((coefficient_param ha (by linarith [hβ.1]) hs n).1).const_mul (n : ℝ)).mul_const _
    · intro n β hβ
      have hβ0 : 0 < β := by linarith [hβ.1]
      have hc := coefficient_param ha hβ0 hs n
      change ‖(n : ℝ) * deriv (C n) β * x^(n-1)‖ ≤ _
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
        C, abs_of_nonneg hc.2.1, pow_one]
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact hc.2.2.trans (div_le_div_of_nonneg_left
          (mul_nonneg (Nat.cast_nonneg n)
            (div_pos (ascPochhammer_pos n a ha) (by positivity)).le)
          (by linarith) hβ.1.le)
      · exact pow_le_pow_left₀ (abs_nonneg x) hxr.le _
      · positivity
      · have hp : 0 ≤ binomialCoeff a n :=
          (div_pos (ascPochhammer_pos n a ha) (by positivity)).le
        positivity
    · constructor <;> linarith
    · exact hsum
    · constructor <;> linarith
  have heq : (fun β : ℝ => deriv (gauss a β (a+β+s)) x) =ᶠ[𝓝 b]
      (fun β : ℝ => ∑' n : ℕ, (n : ℝ) * C n β * x^(n-1)) := by
    filter_upwards [Ioi_mem_nhds hb] with β hβ
    exact (hasDerivAt_gauss_series ha hβ hs hx).deriv
  rw [(hasDerivAt_gaussParam ha hb hs hx).deriv]
  exact hd.congr_of_eventuallyEq heq

/-- The parameter and argument derivatives of the contiguous quotient commute, including at zero. -/
theorem hasDerivAt_f_mixed {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (fun z : ℝ => deriv (fun β : ℝ => f a β z) b)
      (deriv (fun β : ℝ => deriv (f a β) x) b) x ∧
      HasDerivAt (fun β : ℝ => deriv (f a β) x)
        (deriv (fun z : ℝ => deriv (fun β : ℝ => f a β z) b) x) b := by
  have hxabs : |x| < 1 := by simpa [abs_of_nonneg hx] using hx1
  let N := gauss a b (a+b+1)
  let D := gauss a b (a+b)
  let Nb := gaussParam a b 1
  let Db := gaussParam a b 0
  have hN := (hasDerivAt_gauss_series (s := 1) ha hb (by linarith) hxabs).differentiableAt.hasDerivAt
  have hD := (hasDerivAt_gauss_series (s := 0) ha hb (by simpa using ha) hxabs).differentiableAt.hasDerivAt
  simp only [add_zero] at hD
  have hNb := (hasDerivAt_gaussParam (s := 1) ha hb (by linarith) hxabs).differentiableAt.hasDerivAt
  have hDb := (hasDerivAt_gaussParam (s := 0) ha hb (by simpa using ha) hxabs).differentiableAt.hasDerivAt
  have hD0 : D x ≠ 0 := (gauss_pos ha hb (by linarith) hx hx1).ne'
  have hdx := ((hNb.mul hD).sub (hN.mul hDb)).div (hD.pow 2) (pow_ne_zero 2 hD0)
  have heqX : (fun z : ℝ => deriv (fun β : ℝ => f a β z) b) =ᶠ[𝓝 x]
      (fun z => (Nb z * D z - N z * Db z) / (D z)^2) := by
    have hunit : ∀ᶠ z in 𝓝 x, |z| < 1 :=
      (continuous_abs.tendsto x).eventually (Iio_mem_nhds hxabs)
    have hnon : ∀ᶠ z in 𝓝 x, D z ≠ 0 := hD.continuousAt.eventually_ne hD0
    filter_upwards [hunit, hnon] with z hz hz0
    have hNp := hasDerivAt_gauss_param (s := 1) ha hb (by linarith) hz
    have hDp := hasDerivAt_gauss_param (s := 0) ha hb (by simpa using ha) hz
    simp only [add_zero] at hDp
    simpa only [Nb, Db, N, D, gaussParam, add_zero] using
      (hasDerivAt_f_param_of_gauss hNp hDp hz0).deriv
  have hNp : HasDerivAt (fun β : ℝ => gauss a β (a+β+1) x) (Nb x) b :=
    hasDerivAt_gauss_param (s := 1) ha hb (by linarith) hxabs
  have hDp : HasDerivAt (fun β : ℝ => gauss a β (a+β) x) (Db x) b := by
    simpa only [Db, gaussParam, add_zero] using
      hasDerivAt_gauss_param (s := 0) ha hb (by simpa using ha) hxabs
  have hNxp := hasDerivAt_gauss_mixed (s := 1) ha hb (by linarith) hxabs
  have hDxp := hasDerivAt_gauss_mixed (s := 0) ha hb (by simpa using ha) hxabs
  simp only [add_zero] at hDxp
  have hdb := ((hNxp.mul hDp).sub (hNp.mul hDxp)).div (hDp.pow 2) (pow_ne_zero 2 hD0)
  have heqB : (fun β : ℝ => deriv (f a β) x) =ᶠ[𝓝 b]
      (fun β => (deriv (gauss a β (a+β+1)) x * gauss a β (a+β) x -
        gauss a β (a+β+1) x * deriv (gauss a β (a+β)) x) / (gauss a β (a+β) x)^2) := by
    filter_upwards [Ioi_mem_nhds hb] with β hβ
    exact (Series.hasDerivAt_f ha hβ hx hx1).deriv
  have hdX := hdx.congr_of_eventuallyEq heqX
  have hdB := hdb.congr_of_eventuallyEq heqB
  have hcross : HasDerivAt (fun z : ℝ => deriv (fun β : ℝ => f a β z) b)
      (deriv (fun β : ℝ => deriv (f a β) x) b) x := by
    convert hdX using 1
    rw [hdB.deriv]
    dsimp only [N, D, Nb, Db, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    field_simp
    <;> ring
  refine ⟨hcross, ?_⟩
  rw [hcross.deriv]
  exact hdB.differentiableAt.hasDerivAt

/-- The parameter derivative vanishes at the series origin. -/
theorem deriv_f_param_zero (a b : ℝ) : deriv (fun β : ℝ => f a β 0) b = 0 := by
  simp only [f_zero, deriv_const]

/-- The initial slope of the parameter derivative. -/
theorem hasDerivAt_f_param_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => deriv (fun β : ℝ => f a β x) b)
      (a * (b^2 - a*(a+1)) / ((a+b)^2 * (a+b+1)^2)) 0 := by
  have hab : a+b ≠ 0 := by positivity
  have hab1 : a+b+1 ≠ 0 := by positivity
  have hc : HasDerivAt (fun β : ℝ => a+β) 1 b := by
    simpa only [id_eq] using (hasDerivAt_id b).const_add a
  have hd := (((hasDerivAt_id b).const_mul a).div (hc.mul (hc.add_const 1))
    (mul_ne_zero hab hab1)).neg
  have heq : (fun β : ℝ => deriv (f a β) 0) =ᶠ[𝓝 b]
      (fun β : ℝ => -(a*β/((a+β)*(a+β+1)))) := by
    filter_upwards [Ioi_mem_nhds hb] with β hβ
    exact deriv_f_zero ha hβ
  have hder := hd.congr_of_eventuallyEq heq
  have hm := (hasDerivAt_f_mixed ha hb (x := 0) (by norm_num) (by norm_num)).1
  rw [hder.deriv] at hm
  convert hm using 1
  dsimp
  field_simp
  <;> ring

/-- The Riccati equation differentiated in its upper parameter. -/
theorem parameter_equation {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Ioo (0:ℝ) 1) :
    let h := fun z : ℝ => deriv (fun β : ℝ => f a β z) b
    x * deriv h x +
      ((a+b) + 2*(a*b/(a+b))*(x/(1-x))*f a b x) * h x =
      (1-f a b x) - (a^2/(a+b)^2)*(x/(1-x))*(f a b x)^2 := by
  have hm := hasDerivAt_f_mixed ha hb hx.1.le hx.2
  have heq : ∀ᶠ β : ℝ in 𝓝 b,
      x * deriv (f a β) x = (a+β)*(1-f a β x) -
        (a*β/(a+β))*(x/(1-x))*(f a β x)^2 := by
    filter_upwards [Ioi_mem_nhds hb] with β hβ
    exact riccati ha hβ hx.1 hx.2
  have hid := parameter_riccati_deriv ha hb (ne_of_lt hx.2)
    (hasDerivAt_f_param ha hb hx.1.le hx.2) hm.2.differentiableAt.hasDerivAt heq
  rw [← hm.1.deriv] at hid
  exact hid

/-- The parameter derivative of the quotient in the first classification. -/
theorem hasDerivAt_quot_param {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (fun β : ℝ => quot a β x)
      (deriv (fun β : ℝ => f a β x) b / (1-x)) b := by
  have h := (hasDerivAt_f_param ha hb hx hx1).div_const (1-x)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hb] with β hβ
  exact quot_eq ha hβ hx hx1

private lemma deriv_f_param_neg {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hthreshold : b^2 ≤ a*(a+1)) (hx : x ∈ Ioo (0:ℝ) 1) :
    deriv (fun β : ℝ => f a β x) b < 0 := by
  let h := fun z : ℝ => deriv (fun β : ℝ => f a β z) b
  let R : ℝ := (x+1)/2
  let P := fun z : ℝ => (a+b) + 2*(a*b/(a+b))*(z/(1-z))*f a b z
  have hR0 : 0 < R := by dsimp [R]; linarith [hx.1]
  have hR1 : R < 1 := by dsimp [R]; linarith [hx.2]
  have hxR : x ∈ Ioo (0:ℝ) R := ⟨hx.1, by dsimp [R]; linarith [hx.2]⟩
  have hq : a*b/((a+b)*(a+b+1)) ≤ a^2/(a+b)^2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < (a+b)*(a+b+1))
      (by positivity : 0 < (a+b)^2)).2
    nlinarith [mul_nonneg (show 0 ≤ a*(a+b) by positivity) (sub_nonneg.mpr hthreshold)]
  have hcont : ContinuousOn (fun z => -h z) (Icc 0 R) := by
    intro z hz
    exact ((hasDerivAt_f_mixed ha hb hz.1 (hz.2.trans_lt hR1)).1.continuousAt.neg).continuousWithinAt
  have hd : ∀ z ∈ Ioo (0:ℝ) R,
      HasDerivAt (fun w => -h w) (deriv (fun w => -h w) z) z := by
    intro z hz
    exact ((hasDerivAt_f_mixed ha hb hz.1.le (hz.2.trans hR1)).1.neg).differentiableAt.hasDerivAt
  have hP : ∀ z ∈ Ioo (0:ℝ) R, 0 < P z := by
    intro z hz
    have hz1 := hz.2.trans hR1
    have hf := f_pos ha hb hz.1.le hz1
    have ht : 0 < z/(1-z) := div_pos hz.1 (by linarith)
    dsimp [P]
    positivity
  have hi : ∀ z ∈ Ioo (0:ℝ) R,
      0 < z * deriv (fun w => -h w) z + P z * (-h z) := by
    intro z hz
    have hz1 := hz.2.trans hR1
    have hf := f_pos ha hb hz.1.le hz1
    have ht : 0 < (z/(1-z))*(f a b z)^2 := by
      have ht' : 0 < z/(1-z) := div_pos hz.1 (by linarith)
      positivity
    have hcert := Comparison.certificate ha hb ⟨hz.1, hz1⟩
    have hstrict := (div_lt_iff₀ ht).1 (hcert.trans_le hq)
    have hid := parameter_equation ha hb ⟨hz.1, hz1⟩
    have hneg : deriv (fun w => -h w) z = -deriv h z := by
      exact ((hasDerivAt_f_mixed ha hb hz.1.le hz1).1.neg).deriv.trans
        (congrArg Neg.neg (hasDerivAt_f_mixed ha hb hz.1.le hz1).1.deriv.symm)
    rw [hneg]
    change 0 < z * -deriv h z + P z * -h z
    change z * deriv h z + P z * h z = _ at hid
    nlinarith [hstrict, hid]
  have hpos := Comparison.singular_comparison hR0
    (u := fun z => -h z) (P := P) (by simp [h, deriv_f_param_zero]) hcont hd hP hi x hxR
  dsimp [h] at hpos
  linarith

/-- The first parameter classification of the zero-balanced Gauss quotient. -/
theorem clause1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((∀ x ∈ Ioo (0:ℝ) 1, deriv (fun β : ℝ => quot a β x) b < 0) ↔
      b ≤ Real.sqrt (a*(a+1))) := by
  rw [Real.le_sqrt hb.le (by positivity)]
  constructor
  · intro hneg
    by_contra hbad
    have hbad' : a*(a+1) < b^2 := lt_of_not_ge hbad
    let h := fun x : ℝ => deriv (fun β : ℝ => f a β x) b
    have h0 : h 0 = 0 := deriv_f_param_zero a b
    have hn : ∀ x ∈ Ioo (0:ℝ) 1, h x < 0 := by
      intro x hx
      have hq := hneg x hx
      rw [(hasDerivAt_quot_param ha hb hx.1.le hx.2).deriv] at hq
      exact neg_of_div_neg_left hq (by linarith [hx.2])
    have hmax : IsMaxOn h (Icc (0:ℝ) (1/2)) 0 := by
      intro z hz
      rw [h0]
      rcases eq_or_lt_of_le hz.1 with (rfl | hz0)
      · exact h0.le
      · exact (hn z ⟨hz0, by linarith [hz.2]⟩).le
    have ht : (1/2:ℝ) - 0 ∈ posTangentConeAt (Icc (0:ℝ) (1/2)) 0 := by
      apply sub_mem_posTangentConeAt_of_segment_subset
      rw [segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1/2)]
    have hz := hasDerivAt_f_param_zero ha hb
    have hnon := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
      hz.hasFDerivAt.hasFDerivWithinAt ht
    have hnon' : (a*(b^2-a*(a+1))/((a+b)^2*(a+b+1)^2))*(1/2:ℝ) ≤ 0 := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hnon
    have hp : 0 < a*(b^2-a*(a+1))/((a+b)^2*(a+b+1)^2) := by
      apply div_pos (mul_pos ha (sub_pos.mpr hbad'))
      positivity
    nlinarith
  · intro hthreshold x hx
    rw [(hasDerivAt_quot_param ha hb hx.1.le hx.2).deriv]
    exact div_neg_of_neg_of_pos (deriv_f_param_neg ha hb hthreshold hx) (by linarith [hx.2])

end D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
