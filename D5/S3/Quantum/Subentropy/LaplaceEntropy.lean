/- GID: D5/S3/Quantum/Subentropy/LaplaceEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/LaplaceEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.NegMulLog]
   utility: none
   digest: Convergent resolvent representation of finite entropy Jensen gaps. -/

import D5.S3.Quantum.Subentropy.UniformIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod

/-! Finite entropy differences from convergent reciprocal differences. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Quantum.Subentropy.LaplaceEntropy

private theorem reciprocal_difference (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 1 / (t + a) - 1 / (t + b)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), 1 / (t + a) - 1 / (t + b)) = Real.log b - Real.log a := by
  rcases le_total a b with hab | hba
  · exact UniformIntegrals.reciprocal_difference a b ha hab
  · obtain ⟨hi, hv⟩ := UniformIntegrals.reciprocal_difference b a hb hba
    have heq : (fun t : ℝ => 1 / (t + a) - 1 / (t + b)) =
        -(fun t : ℝ => 1 / (t + b) - 1 / (t + a)) := by
      funext t
      simp
    rw [heq]
    refine ⟨hi.neg, ?_⟩
    change (∫ t in Ioi (0 : ℝ), -(1 / (t + b) - 1 / (t + a))) = _
    rw [integral_neg, hv]
    ring

private theorem entropy_resolvent_term (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => x * (1 / (t + a) - 1 / (t + x))) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), x * (1 / (t + a) - 1 / (t + x))) =
        x * Real.log x - x * Real.log a := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp
  · obtain ⟨hi, hv⟩ := reciprocal_difference a x ha h
    refine ⟨hi.const_mul x, ?_⟩
    rw [integral_const_mul, hv]
    ring

/-- The Jensen difference for `x log x` is an absolutely convergent resolvent
integral. Zero entries are permitted, and weights need not be strictly positive. -/
theorem entropy_jensen_resolvent {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx : ∀ i, 0 ≤ x i) :
    let a := ∑ i, p i * x i
    IntegrableOn (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i)))
        (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), a / (t + a) - ∑ i, p i * (x i / (t + x i))) =
        ∑ i, p i * (x i * Real.log (x i)) - a * Real.log a := by
  classical
  dsimp only
  let a : ℝ := ∑ i, p i * x i
  change IntegrableOn (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i))) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), a / (t + a) - ∑ i, p i * (x i / (t + x i))) =
      ∑ i, p i * (x i * Real.log (x i)) - a * Real.log a
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hx i)
  rcases ha.eq_or_lt with ha | ha
  · have hterms : ∀ i, p i * x i = 0 := by
      intro i
      have hh := Finset.single_le_sum (s := Finset.univ) (fun j _ => mul_nonneg (hp j) (hx j))
        (Finset.mem_univ i)
      change p i * x i ≤ a at hh
      rw [← ha] at hh
      exact le_antisymm hh (mul_nonneg (hp i) (hx i))
    have hfun : (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i))) = 0 := by
      funext t
      simp only [← ha, zero_div, Pi.zero_apply, zero_sub]
      rw [Finset.sum_eq_zero (fun i _ => by rw [← mul_div_assoc, hterms i, zero_div])]
      simp
    change IntegrableOn (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i))) (Ioi 0) ∧ _
    rw [hfun]
    constructor
    · exact integrable_zero _ _ _
    · simp only [integral_zero, ← ha, Real.log_zero, zero_mul]
      rw [Finset.sum_eq_zero (fun i _ => by rw [← mul_assoc, hterms i, zero_mul])]
      simp
  · have hi : ∀ i, IntegrableOn
        (fun t : ℝ => p i * (x i * (1 / (t + a) - 1 / (t + x i)))) (Ioi 0) :=
      fun i => ((entropy_resolvent_term a (x i) ha (hx i)).1).const_mul (p i)
    have heq : (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i))) =
        fun t => ∑ i, p i * (x i * (1 / (t + a) - 1 / (t + x i))) := by
      funext t
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp only [← mul_assoc, ← Finset.sum_mul, a, div_eq_mul_inv, one_mul]
      · apply Finset.sum_congr rfl
        intro i _
        ring
    change IntegrableOn (fun t : ℝ => a / (t + a) - ∑ i, p i * (x i / (t + x i))) (Ioi 0) ∧ _
    rw [heq]
    refine ⟨integrable_finsetSum Finset.univ (fun i _ => hi i), ?_⟩
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    calc
      ∑ i, (∫ t in Ioi (0 : ℝ), p i * (x i * (1 / (t + a) - 1 / (t + x i)))) =
          ∑ i, p i * (x i * Real.log (x i) - x i * Real.log a) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul, (entropy_resolvent_term a (x i) ha (hx i)).2]
      _ = _ := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        congr 1
        simp only [← mul_assoc, ← Finset.sum_mul, a]


private theorem exponential_integral (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => Real.exp (-(r*s))) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), Real.exp (-(r*s))) = 1/r := by
  refine ⟨?_, ?_⟩
  · simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0
  · simpa [neg_mul] using integral_exp_mul_Ioi (a := -r) (by linarith) 0

private def laplaceGap {ι : Type*} [Fintype ι] (p x : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (-s * x i) - Real.exp (-s * ∑ i, p i * x i)

private theorem laplaceGap_nonneg {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (s : ℝ) :
    0 ≤ laplaceGap p x s := by
  classical
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := p)
    (p := fun i => -s * x i) (fun i _ => hp i) hs (fun i _ => Set.mem_univ _)
  have heq : ∑ i, p i * (-s * x i) = -s * ∑ i, p i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [smul_eq_mul] at h
  rw [heq] at h
  exact sub_nonneg.mpr h

private theorem resolvent_laplace {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hx : ∀ i, 0 ≤ x i) (t : ℝ) (ht : 0 < t) :
    let a := ∑ i, p i * x i
    IntegrableOn (fun s : ℝ => t * Real.exp (-(t*s)) * laplaceGap p x s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), t * Real.exp (-(t*s)) * laplaceGap p x s) =
        a / (t+a) - ∑ i, p i * (x i / (t+x i)) := by
  classical
  let a : ℝ := ∑ i, p i * x i
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hx i)
  have heq : (fun s : ℝ => t * Real.exp (-(t*s)) * laplaceGap p x s) =
      fun s => (∑ i, (t*p i) * Real.exp (-((t+x i)*s))) -
        t * Real.exp (-((t+a)*s)) := by
    funext s
    dsimp only [laplaceGap]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [show -((t+x i)*s) = -(t*s) + -s*x i by ring, Real.exp_add]
      ring
    · rw [show -((t+a)*s) = -(t*s) + -s*a by ring, Real.exp_add]
      dsimp [a]
      ring
  have hi : ∀ i, IntegrableOn
      (fun s : ℝ => (t*p i) * Real.exp (-((t+x i)*s))) (Ioi 0) :=
    fun i => ((exponential_integral (t+x i) (by linarith [hx i])).1).const_mul _
  have hi0 := ((exponential_integral (t+a) (by linarith)).1).const_mul t
  dsimp only
  change IntegrableOn (fun s : ℝ => t * Real.exp (-(t*s)) * laplaceGap p x s) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), t * Real.exp (-(t*s)) * laplaceGap p x s) =
      a / (t+a) - ∑ i, p i * (x i / (t+x i))
  rw [heq]
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hi i)).sub hi0, ?_⟩
  rw [integral_sub (integrable_finsetSum Finset.univ (fun i _ => hi i)) hi0,
    integral_finsetSum Finset.univ (fun i _ => hi i), integral_const_mul,
    (exponential_integral (t+a) (by linarith)).2]
  have hterm : ∀ i, (∫ s in Ioi (0 : ℝ), (t*p i) * Real.exp (-((t+x i)*s))) =
      p i - p i * (x i/(t+x i)) := by
    intro i
    rw [integral_const_mul, (exponential_integral (t+x i) (by linarith [hx i])).2]
    have hden : t+x i ≠ 0 := by linarith [hx i]
    field_simp
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, hs]
  have hden : t+a ≠ 0 := by linarith
  field_simp
  ring


/-- A nonnegative Laplace integral represents the finite entropy Jensen gap,
including zero entries. All exchanges of integration use an integrable,
nonnegative product kernel. -/
theorem entropy_jensen_laplace {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hx : ∀ i, 0 ≤ x i) :
    let a := ∑ i, p i * x i
    IntegrableOn
      (fun s : ℝ => (∑ i, p i * Real.exp (-s*x i) - Real.exp (-s*a)) / s^2)
        (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ),
        (∑ i, p i * Real.exp (-s*x i) - Real.exp (-s*a)) / s^2) =
        ∑ i, p i * (x i * Real.log (x i)) - a * Real.log a := by
  classical
  let a : ℝ := ∑ i, p i * x i
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ × ℝ → ℝ := fun u => u.1 * Real.exp (-(u.1*u.2)) * laplaceGap p x u.2
  have hg := entropy_jensen_resolvent p x hp hx
  change Integrable
      (fun s : ℝ => laplaceGap p x s / s^2) ν ∧
    (∫ s, laplaceGap p x s / s^2 ∂ν) =
      ∑ i, p i * (x i * Real.log (x i)) - a * Real.log a
  have hnonneg (t s : ℝ) (ht : 0 < t) : 0 ≤ f (t,s) :=
    mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le) (laplaceGap_nonneg p x hp hs s)
  have hprod : Integrable f (ν.prod ν) := by
    refine (integrable_prod_iff (by dsimp [f, laplaceGap]; fun_prop)).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (resolvent_laplace p x hp hs hx t ht).1
    · refine hg.1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have heq : (∫ s, ‖f (t,s)‖ ∂ν) = ∫ s, f (t,s) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => Real.norm_of_nonneg (hnonneg t s ht)
      rw [heq]
      exact (resolvent_laplace p x hp hs hx t ht).2.symm
  have heval : ∀ s ∈ Ioi (0 : ℝ),
      (∫ t, f (t,s) ∂ν) = laplaceGap p x s / s^2 := by
    intro s hs'
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 2) (r := s) (by norm_num) hs'
    have hgamma2 : Real.Gamma 2 = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    simp only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two, hgamma2, mul_one] at hgamma
    have heq : (fun t : ℝ => f (t,s)) =
        fun t => laplaceGap p x s * (t * Real.exp (-(s*t))) := by
      funext t
      dsimp [f]
      rw [mul_comm s t]
      ring
    rw [heq, integral_const_mul]
    change laplaceGap p x s * (∫ t in Ioi (0 : ℝ), t * Real.exp (-(s*t))) = _
    rw [hgamma]
    ring
  have hcongr : (fun s => ∫ t, f (t,s) ∂ν) =ᵐ[ν]
      fun s => laplaceGap p x s / s^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs'
    exact heval s hs'
  refine ⟨hprod.integral_prod_right.congr hcongr, ?_⟩
  rw [← integral_congr_ae hcongr, ← integral_integral_swap hprod]
  calc
    (∫ t, ∫ s, f (t,s) ∂ν ∂ν) =
        ∫ t, a/(t+a) - ∑ i, p i * (x i/(t+x i)) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (resolvent_laplace p x hp hs hx t ht).2
    _ = _ := hg.2

end D5.S3.Quantum.Subentropy.LaplaceEntropy
