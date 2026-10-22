/- GID: D5/S3/Analytic/GaussZeroBalanced/ParamDeriv
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/ParamDeriv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Parameter quotient differentiation and the differentiated Riccati identity. -/

import D5.S3.Analytic.GaussZeroBalanced.Series
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped BigOperators
open scoped Topology
open D5.S3.Analytic.GaussZeroBalanced.Defs
open D5.S3.Analytic.GaussZeroBalanced.Series

namespace D5.S3.Analytic.GaussZeroBalanced.ParamDeriv

/-! The quotient rule in the parameter is isolated so that the two Gauss
parameter series can be supplied by the eventual termwise parameter proof. -/
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
    (hEq : ∀ β : ℝ,
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
    Filter.Eventually.of_forall (fun β => hEq β)
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

end D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
