/- GID: D5/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A resolvable finite-difference signal charges one common endpoint stopping moment. -/

import D5.S3.Estimation.SequentialDecisionRisk.BernoulliStoppedCoefficientBudget
import D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.BernoulliCommonEndpointCharge
open SeededBernoulliStoppedMoment BernoulliStoppedCoefficientBudget
variable {Seed : Type*} [MeasurableSpace Seed]

local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p))
local notation "Trunc" => fun (M : Seed × (ℕ → Bool) → WithTop ℕ) (n : ℕ)
  (ω : Seed × (ℕ → Bool)) => (min (M ω) (n : WithTop ℕ)).untopD 0
local notation "MomentC" => fun m : ℕ =>
  (((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m * (2 : ℝ) ^ (2 * m))
local notation "Diff" => fun (r : ℕ) (t : ℝ) (f : ℝ → ℝ) =>
  ∑ i ∈ range (r + 1), (-1 : ℝ) ^ (r - i) * (r.choose i : ℝ) * f (t + i * t)
local notation "Rate" => fun (p₀ : unitInterval) (γ h : ℝ) =>
  Set.projIcc 0 1 zero_le_one ((p₀ : ℝ) + h * γ)
local notation "GeoBudget" => fun (a : ℝ) (m : ℕ) =>
  (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) + (1 - (2 : ℝ) ^ (a - (m : ℝ)))⁻¹
local notation "EndpointCost" => fun (a : ℝ) (t : WithTop ℕ) =>
  if t = ⊤ then (⊤ : ℝ≥0∞) else ENNReal.ofReal (((t.untopD 0 : ℕ) : ℝ) ^ a)
local notation "DerivC" => fun (m : ℕ) (σ : ℝ) =>
  (2 * m).factorial * σ ^ (2 * m) * (2 * MomentC m + 1)

private lemma difference_eq_fwdDiff (r : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    Diff r t f = (fwdDiff t)^[r] f t := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]

private lemma difference_error_bound (r : ℕ) (t K : ℝ) (f g : ℝ → ℝ)
    (he : ∀ i ∈ range (r + 1), |f (t + i * t) - g (t + i * t)| ≤ K) :
    |Diff r t f - Diff r t g| ≤ (2 : ℝ) ^ r * K := by
  have hsub : Diff r t f - Diff r t g =
      ∑ i ∈ range (r + 1), (-1 : ℝ) ^ (r - i) * (r.choose i : ℝ) *
        (f (t + i * t) - g (t + i * t)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsub]
  calc
    _ ≤ ∑ i ∈ range (r + 1), |(-1 : ℝ) ^ (r - i) * (r.choose i : ℝ) *
        (f (t + i * t) - g (t + i * t))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) * K := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (he i hi) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose r

private lemma common_endpoint_local_budget
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (n m : ℕ) (hm : 0 < m) (γ h : ℝ) (hp : (p₀ : ℝ) + h * γ = (p : ℝ))
    (f : Seed × (ℕ → Bool) → ℝ)
    (hf : StronglyMeasurable[(truncation_stopping hM n).measurableSpace] f)
    (hfb : ∀ ω, |f ω| ≤ 1) (σ : ℝ) (hσ : 0 ≤ σ)
    (hscore : |γ / ((p : ℝ) * (1 - (p : ℝ)))| ≤ σ)
    (hw : |((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
      Real.sqrt (n : ℝ) ≤ (2 * MomentC m + 1)⁻¹) :
    |iteratedDeriv (2 * m) (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x)) h| ≤
      2 * DerivC m σ * ∫ ω, (Trunc M n ω : ℝ) ^ m ∂Law ν p₀ ∧
    (n : ℝ) ^ m * (Law ν p).real {ω | (n : WithTop ℕ) < M ω} ≤
      2 * ∫ ω, (Trunc M n ω : ℝ) ^ m ∂Law ν p₀ := by
  let τ := Trunc M n
  have ht := truncation_stopping hM n
  have hn := fun ω => truncation_le (M ω) n
  have hmeas := hM.measurable.mono hM.measurableSpace_le le_rfl
  have hI := truncated_moment_integrable (Law ν p) M hmeas n m
  have hI₀ := truncated_moment_integrable (Law ν p₀) M hmeas n m
  have hnonneg : ∀ ω, 0 ≤ (τ ω : ℝ) ^ m := fun ω => by positivity
  have hmoment := (bernoulli_stopped_moment_bound ν p₀ p h₀ h₁ τ ht n hn hm hw).2
  have hderiv := bernoulli_stopped_affine_derivative_budget ν p hp₀ hp₁ τ ht n hn hm
    γ (p₀ : ℝ) h hp f hf hfb
  have hfactor : (2 * m).factorial *
      |γ / ((p : ℝ) * (1 - (p : ℝ)))| ^ (2 * m) * (2 * MomentC m + 1) ≤ DerivC m σ := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hscore _) (Nat.cast_nonneg _)
  have hD : 0 ≤ DerivC m σ := by positivity
  have hVi : 0 ≤ ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p := integral_nonneg hnonneg
  have hV₀ : 0 ≤ ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p₀ := integral_nonneg hnonneg
  have hderivReal : |iteratedDeriv (2 * m)
      (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x)) h| ≤
      ((2 * m).factorial * |γ / ((p : ℝ) * (1 - (p : ℝ)))| ^ (2 * m) *
        (2 * MomentC m + 1)) * ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p := by
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnonneg),
      ← ENNReal.ofReal_mul (by positivity)] at hderiv
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hVi)).mp hderiv
  have htail := truncation_tail_bound (Law ν p) M hmeas n m
  rw [← ofReal_measureReal (μ := Law ν p),
    ← ENNReal.ofReal_mul (by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnonneg)] at htail
  have htailReal := (ENNReal.ofReal_le_ofReal_iff hVi).mp htail
  refine ⟨hderivReal.trans ?_, htailReal.trans hmoment⟩
  calc
    _ ≤ DerivC m σ * (2 * ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p₀) :=
      mul_le_mul hfactor hmoment hVi hD
    _ = _ := by ring

/-- Once a finite-difference signal is resolved, one bounded stopped output
charges a fixed amount to its own zero-perturbation endpoint. The signal and
finite-difference calculus interfaces are stated separately from the
Bernoulli law and its stopping-time estimates. -/
theorem bernoulli_one_scale_common_endpoint_charge
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (a ρ γ σ δ S : ℝ) (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hS : 0 < S)
    (f : Seed × (ℕ → Bool) → ℝ)
    (hf : StronglyMeasurable[(truncation_stopping hM n).measurableSpace] f)
    (hfb : ∀ ω, |f ω| ≤ 1) (G : ℝ → ℝ)
    (hrate : ∀ h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))),
      0 < (p₀ : ℝ) + h * γ ∧ (p₀ : ℝ) + h * γ < 1)
    (hscore : ∀ h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))),
      |γ / ((Rate p₀ γ h : ℝ) * (1 - (Rate p₀ γ h : ℝ)))| ≤ σ)
    (hwindow : ∀ h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))),
      |((Rate p₀ γ h : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
        Real.sqrt (n : ℝ) ≤ (2 * MomentC m + 1)⁻¹)
    (herror : ∀ h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))),
      |G h - ∫ ω, f ω ∂Law ν (Rate p₀ γ h)| ≤
        δ + (Law ν (Rate p₀ γ h)).real {ω | (n : WithTop ℕ) < M ω})
    (hsignal : S * (n : ℝ) ^ (-a) ≤ |Diff (2 * m) (ρ / Real.sqrt (n : ℝ)) G|)
    (hcalculus : ∀ U : ℝ, 0 ≤ U →
      (∀ h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
        ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))),
        |iteratedDeriv (2 * m) (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x)) h| ≤ U) →
      |Diff (2 * m) (ρ / Real.sqrt (n : ℝ))
        (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x))| ≤
        (ρ / Real.sqrt (n : ℝ)) ^ (2 * m) * U)
    (hδ : δ * (n : ℝ) ^ a ≤ S / (2 : ℝ) ^ (2 * m + 1)) :
    S / (2 * (2 * DerivC m σ * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1))) ≤
      (n : ℝ) ^ (a - (m : ℝ)) * ∫ ω, (Trunc M n ω : ℝ) ^ m ∂Law ν p₀ := by
  let t := ρ / Real.sqrt (n : ℝ)
  let V := ∫ ω, (Trunc M n ω : ℝ) ^ m ∂Law ν p₀
  let D := DerivC m σ
  let A := 2 * D * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)
  let g := fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnPow : 0 < (n : ℝ) ^ m := pow_pos hnR m
  have hV : 0 ≤ V := integral_nonneg (fun ω => by positivity)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hlocal : ∀ h ∈ Set.Icc t ((2 * m + 1 : ℕ) * t),
      |iteratedDeriv (2 * m) g h| ≤ 2 * D * V ∧
      (n : ℝ) ^ m * (Law ν (Rate p₀ γ h)).real {ω | (n : WithTop ℕ) < M ω} ≤ 2 * V := by
    intro h hh
    have hr := hrate h hh
    have hp : (Rate p₀ γ h : ℝ) = (p₀ : ℝ) + h * γ :=
      congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one) ⟨hr.1.le, hr.2.le⟩)
    exact common_endpoint_local_budget ν p₀ (Rate p₀ γ h) h₀ h₁
      (by rw [hp]; exact hr.1) (by rw [hp]; exact hr.2) M hM n m hm γ h hp.symm
      f hf hfb σ hσ (hscore h hh) (hwindow h hh)
  have hpoints : ∀ i ∈ range (2 * m + 1), t + i * t ∈ Set.Icc t ((2 * m + 1 : ℕ) * t) := by
    intro i hi
    have hiR : (i : ℝ) + 1 ≤ (2 * m + 1 : ℕ) := by exact_mod_cast mem_range.mp hi
    have ht : 0 ≤ t := div_nonneg hρ.le (Real.sqrt_nonneg _)
    constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg i) ht,
      mul_le_mul_of_nonneg_right hiR ht]
  have herr : ∀ i ∈ range (2 * m + 1), |G (t + i * t) - g (t + i * t)| ≤
      δ + 2 * V / (n : ℝ) ^ m := by
    intro i hi
    apply (herror _ (hpoints i hi)).trans
    apply add_le_add le_rfl
    exact (le_div_iff₀ hnPow).mpr (by simpa only [mul_comm] using (hlocal _ (hpoints i hi)).2)
  have hdiff := difference_error_bound (2 * m) t (δ + 2 * V / (n : ℝ) ^ m) G g herr
  have hgd := hcalculus (2 * D * V) (by positivity) (fun h hh => (hlocal h hh).1)
  have hscale : t ^ (2 * m) = ρ ^ (2 * m) / (n : ℝ) ^ m := by
    dsimp [t]
    simp_rw [div_pow, pow_mul, Real.sq_sqrt hnR.le]
  have hbound : S * (n : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (2 * m) * δ + A * V / (n : ℝ) ^ m := by
    calc
      _ ≤ |Diff (2 * m) t G| := hsignal
      _ ≤ |Diff (2 * m) t G - Diff (2 * m) t g| + |Diff (2 * m) t g| := by
        simpa only [sub_zero] using abs_sub_le (Diff (2 * m) t G) (Diff (2 * m) t g) 0
      _ ≤ (2 : ℝ) ^ (2 * m) * (δ + 2 * V / (n : ℝ) ^ m) + t ^ (2 * m) * (2 * D * V) :=
        add_le_add hdiff hgd
      _ = _ := by rw [hscale]; dsimp [A]; rw [pow_succ]; ring
  have hnormalized : S ≤ (2 : ℝ) ^ (2 * m) * δ * (n : ℝ) ^ a +
      A * ((n : ℝ) ^ (a - (m : ℝ)) * V) := by
    have h := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hnR.le a)
    rw [mul_assoc S, ← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero, mul_one] at h
    calc
      S ≤ ((2 : ℝ) ^ (2 * m) * δ + A * V / (n : ℝ) ^ m) * (n : ℝ) ^ a := h
      _ = _ := by
        rw [Real.rpow_sub_natCast (ne_of_gt hnR), div_eq_mul_inv]
        ring
  have hsmall : (2 : ℝ) ^ (2 * m) * δ * (n : ℝ) ^ a ≤ S / 2 := by
    have h := mul_le_mul_of_nonneg_left hδ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * m))
    rw [pow_succ] at h
    calc
      (2 : ℝ) ^ (2 * m) * δ * (n : ℝ) ^ a =
          (2 : ℝ) ^ (2 * m) * (δ * (n : ℝ) ^ a) := by ring
      _ ≤ (2 : ℝ) ^ (2 * m) * (S / ((2 : ℝ) ^ (2 * m) * 2)) := h
      _ = S / 2 := by field_simp
  apply (div_le_iff₀ (mul_pos (by norm_num) hA)).mpr
  nlinarith

/-- A finite family of resolved windows is paid by a single endpoint
fractional cost of the same stopping rule. Infinite endpoint cost is
included in the statement. -/
theorem bernoulli_finite_dyadic_common_endpoint_charge
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (m : ℕ) (a ρ γ σ δ S : ℝ) (ha : 0 < a) (ham : a < (m : ℝ))
    (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hS : 0 < S) (J : ℕ)
    (f : ℕ → Seed × (ℕ → Bool) → ℝ)
    (hf : ∀ j, StronglyMeasurable[(truncation_stopping hM (2 ^ j)).measurableSpace] (f j))
    (hfb : ∀ j ω, |f j ω| ≤ 1) (G : ℝ → ℝ)
    (hrate : ∀ j < J, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      0 < (p₀ : ℝ) + h * γ ∧ (p₀ : ℝ) + h * γ < 1)
    (hscore : ∀ j < J, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      |γ / ((Rate p₀ γ h : ℝ) * (1 - (Rate p₀ γ h : ℝ)))| ≤ σ)
    (hwindow : ∀ j < J, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      |((Rate p₀ γ h : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
        Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤ (2 * MomentC m + 1)⁻¹)
    (herror : ∀ j < J, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      |G h - ∫ ω, f j ω ∂Law ν (Rate p₀ γ h)| ≤
        δ + (Law ν (Rate p₀ γ h)).real {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω})
    (hsignal : ∀ j < J, S * ((2 ^ j : ℕ) : ℝ) ^ (-a) ≤
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) G|)
    (hcalculus : ∀ j < J, ∀ U : ℝ, 0 ≤ U →
      (∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
        ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
        |iteratedDeriv (2 * m) (fun x : ℝ => ∫ ω, f j ω ∂Law ν (Rate p₀ γ x)) h| ≤ U) →
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
        (fun x : ℝ => ∫ ω, f j ω ∂Law ν (Rate p₀ γ x))| ≤
        (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2 * m) * U)
    (hδ : ∀ j < J, δ * ((2 ^ j : ℕ) : ℝ) ^ a ≤ S / (2 : ℝ) ^ (2 * m + 1)) :
    ENNReal.ofReal ((J : ℝ) * (S /
      (2 * (2 * DerivC m σ * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1))))) ≤
      ENNReal.ofReal (GeoBudget a m) * ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀ := by
  have hm : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    rw [hz, Nat.cast_zero] at ham
    linarith
  let z := S / (2 * (2 * DerivC m σ * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)))
  let W := fun j : ℕ => ((2 : ℝ) ^ (a - (m : ℝ))) ^ j
  have hmeas := hM.measurable.mono hM.measurableSpace_le le_rfl
  have hW : ∀ j, 0 ≤ W j := fun j => by dsimp [W]; positivity
  have hcharges : ∀ j ∈ range J, ENNReal.ofReal z ≤ ENNReal.ofReal (W j) *
      ∫⁻ ω, ENNReal.ofReal ((Trunc M (2 ^ j) ω : ℝ) ^ m) ∂Law ν p₀ := by
    intro j hj
    have hjJ := mem_range.mp hj
    have hc := bernoulli_one_scale_common_endpoint_charge ν p₀ h₀ h₁ M hM (2 ^ j)
      (by positivity) m hm a ρ γ σ δ S hρ hσ hS (f j) (hf j) (hfb j) G
      (hrate j hjJ) (hscore j hjJ) (hwindow j hjJ) (herror j hjJ)
      (hsignal j hjJ) (hcalculus j hjJ) (hδ j hjJ)
    have hw : ((2 ^ j : ℕ) : ℝ) ^ (a - (m : ℝ)) = W j := by
      dsimp [W]
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
        mul_comm (j : ℝ), Real.rpow_mul_natCast (by norm_num)]
    rw [hw] at hc
    rw [← ofReal_integral_eq_lintegral_ofReal
      (truncated_moment_integrable (Law ν p₀) M hmeas (2 ^ j) m)
      (ae_of_all _ (fun ω => by positivity)), ← ENNReal.ofReal_mul (hW j)]
    exact ENNReal.ofReal_le_ofReal hc
  calc
    _ = ∑ _j ∈ range J, ENNReal.ofReal z := by
      rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg J)]
      simp [z]
    _ ≤ ∑ j ∈ range J, ENNReal.ofReal (W j) *
        ∫⁻ ω, ENNReal.ofReal ((Trunc M (2 ^ j) ω : ℝ) ^ m) ∂Law ν p₀ := sum_le_sum hcharges
    _ ≤ _ := endpoint_budget_finite (Law ν p₀) M hmeas a m ha ham J

private lemma resolvable_dyadic_scale_count (a T δ : ℝ) (ha : 0 < a)
    (hT : 0 < T) (hT1 : T ≤ 1) (hδ : 0 < δ) (hδT : δ < T ^ 2) :
    let J := Nat.floor (Real.log (T / δ) / (a * Real.log 2)) + 1
    (∀ j < J, δ * ((2 ^ j : ℕ) : ℝ) ^ a ≤ T) ∧
      Real.log δ⁻¹ / (2 * a * Real.log 2) ≤ (J : ℝ) := by
  let L := Real.log (T / δ)
  let x := L / (a * Real.log 2)
  let J := Nat.floor x + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < a * Real.log 2 := mul_pos ha hlog2
  have hδT' : δ < T := hδT.trans_le (by nlinarith)
  have hL : 0 < L := Real.log_pos ((one_lt_div hδ).mpr hδT')
  have hx : 0 ≤ x := (div_pos hL hden).le
  constructor
  · intro j hj
    change j < Nat.floor x + 1 at hj
    have hjfloor : j ≤ Nat.floor x := by omega
    have hjcast : (j : ℝ) ≤ Nat.floor x := by exact_mod_cast hjfloor
    have hjx : (j : ℝ) ≤ x := hjcast.trans (Nat.floor_le hx)
    have hje : (j : ℝ) * a * Real.log 2 ≤ L := by
      simpa only [mul_assoc] using (le_div_iff₀ hden).mp hjx
    have hjlogb : (j : ℝ) * a ≤ Real.logb 2 (T / δ) := by
      rw [Real.logb]
      exact (le_div_iff₀ hlog2).mpr hje
    have he := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (div_pos hT hδ)).mp hjlogb
    have hp : ((2 ^ j : ℕ) : ℝ) ^ a = (2 : ℝ) ^ ((j : ℝ) * a) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast_mul (by norm_num)]
    calc
      _ ≤ δ * (T / δ) := by rw [hp]; exact mul_le_mul_of_nonneg_left he hδ.le
      _ = T := by field_simp
  · have hlogδ := Real.log_lt_log hδ hδT
    rw [Real.log_pow] at hlogδ
    norm_num only [Nat.cast_ofNat] at hlogδ
    have hhalf : Real.log δ⁻¹ / 2 ≤ L := by
      dsimp [L]
      rw [Real.log_inv, Real.log_div hT.ne' hδ.ne']
      linarith
    calc
      _ = (Real.log δ⁻¹ / 2) / (a * Real.log 2) := by field_simp
      _ ≤ x := div_le_div_of_nonneg_right hhalf hden.le
      _ ≤ (J : ℝ) := by
        dsimp [J]
        simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le

private lemma bernoulli_factory_local_window (p₀ : unitInterval)
    (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) (C ρ θ : ℝ)
    (hC : 1 ≤ C) (hρ : 0 < ρ) (hθ : 0 < θ) (m n : ℕ) (hn : 0 < n)
    (hρsmall : (2 * m + 1 : ℕ) * ρ ≤ (1 / 4 : ℝ))
    (hρwindow : (2 * m + 1 : ℕ) * ρ ≤ (1 - (p₀ : ℝ)) * θ)
    (h : ℝ) (hh : h ∈ Set.Icc (ρ / Real.sqrt (n : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ)))) :
    h ∈ Set.Ioc 0 (1 / 4 : ℝ) ∧
    (0 < (p₀ : ℝ) + h * (-(p₀ : ℝ) / C) ∧
      (p₀ : ℝ) + h * (-(p₀ : ℝ) / C) < 1) ∧
    (|(-(p₀ : ℝ) / C) /
        ((Rate p₀ (-(p₀ : ℝ) / C) h : ℝ) *
          (1 - (Rate p₀ (-(p₀ : ℝ) / C) h : ℝ)))| ≤ 4 / (1 - (p₀ : ℝ))) ∧
    |((Rate p₀ (-(p₀ : ℝ) / C) h : ℝ) - (p₀ : ℝ)) /
        ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| * Real.sqrt (n : ℝ) ≤ θ := by
  have hC0 : 0 < C := by linarith
  have hd : 0 < 1 - (p₀ : ℝ) := sub_pos.mpr h₁
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by linarith
  have hH : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhpos : 0 < h := (div_pos hρ hsqrt).trans_le hh.1
  have hh0 : 0 ≤ h := hhpos.le
  have hh1 : h ≤ (1 / 4 : ℝ) := hh.2.trans
    ((mul_le_mul_of_nonneg_left (div_le_self hρ.le hsqrt1) hH).trans hρsmall)
  have hratio0 : 0 ≤ h / C := div_nonneg hh0 hC0.le
  have hratio1 : h / C ≤ 1 / 4 := (div_le_self hh0 hC).trans hh1
  let p := (p₀ : ℝ) + h * (-(p₀ : ℝ) / C)
  have hpform : p = (p₀ : ℝ) * (1 - h / C) := by dsimp [p]; ring
  have hplow : (p₀ : ℝ) / 4 ≤ p := by rw [hpform]; nlinarith
  have hp0 : 0 < p := (div_pos h₀ (by norm_num)).trans_le hplow
  have hple : p ≤ (p₀ : ℝ) := by rw [hpform]; nlinarith
  have hp1 : p < 1 := hple.trans_lt h₁
  have hp : (Rate p₀ (-(p₀ : ℝ) / C) h : ℝ) = p :=
    congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one) ⟨hp0.le, hp1.le⟩)
  refine ⟨⟨hhpos, hh1⟩, ⟨hp0, hp1⟩, ?_, ?_⟩
  · rw [hp, abs_div, abs_div, abs_neg, abs_of_nonneg h₀.le, abs_of_nonneg hC0.le,
      abs_of_nonneg (mul_pos hp0 (sub_pos.mpr hp1)).le]
    apply (div_le_iff₀ (mul_pos hp0 (sub_pos.mpr hp1))).mpr
    have hv : (p₀ : ℝ) / 4 * (1 - (p₀ : ℝ)) ≤ p * (1 - p) :=
      mul_le_mul hplow (by linarith) hd.le hp0.le
    calc
      _ ≤ (p₀ : ℝ) := div_le_self h₀.le hC
      _ = (4 / (1 - (p₀ : ℝ))) * ((p₀ : ℝ) / 4 * (1 - (p₀ : ℝ))) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (div_nonneg (by norm_num) hd.le)
  · rw [hp]
    have heq : (p - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) =
        -h / (C * (1 - (p₀ : ℝ))) := by
      dsimp [p]
      field_simp
      ring
    rw [heq, abs_div, abs_neg, abs_of_nonneg hh0,
      abs_of_nonneg (mul_pos hC0 hd).le]
    have hhscaled : h * Real.sqrt (n : ℝ) ≤ (2 * m + 1 : ℕ) * ρ := by
      have ht := mul_le_mul_of_nonneg_right hh.2 hsqrt.le
      calc
        _ ≤ ((2 * m + 1 : ℕ) * (ρ / Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) := ht
        _ = _ := by field_simp
    calc
      _ = (h * Real.sqrt (n : ℝ)) / (C * (1 - (p₀ : ℝ))) := by ring
      _ ≤ ((2 * m + 1 : ℕ) * ρ) / (C * (1 - (p₀ : ℝ))) :=
        div_le_div_of_nonneg_right hhscaled (mul_pos hC0 hd).le
      _ ≤ ((1 - (p₀ : ℝ)) * θ) / (C * (1 - (p₀ : ℝ))) :=
        div_le_div_of_nonneg_right hρwindow (mul_pos hC0 hd).le
      _ = θ / C := by field_simp
      _ ≤ θ := div_le_self hθ.le hC

/-- A uniform family of resolvable stopped-output windows gives a logarithmic
lower bound on the common endpoint fractional cost. The finite-difference
and output approximation contracts remain explicit hypotheses. -/
private theorem logarithmic_charge_of_output_windows
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (m : ℕ) (a ρ C δ S : ℝ) (ha : 0 < a) (ham : a < (m : ℝ))
    (hC : 1 ≤ C) (hρ : 0 < ρ) (hS : 0 < S)
    (hρsmall : (2 * m + 1 : ℕ) * ρ ≤ (1 / 4 : ℝ))
    (hρwindow : (2 * m + 1 : ℕ) * ρ ≤ (1 - (p₀ : ℝ)) * (2 * MomentC m + 1)⁻¹)
    (hδ0 : 0 < δ)
    (hδsmall : δ < (min (1 / 2 : ℝ) (S / (2 : ℝ) ^ (2 * m + 1))) ^ 2)
    (f : ℕ → Seed × (ℕ → Bool) → ℝ)
    (hf : ∀ j, StronglyMeasurable[(truncation_stopping hM (2 ^ j)).measurableSpace] (f j))
    (hfb : ∀ j ω, |f j ω| ≤ 1) (G : ℝ → ℝ)
    (herror : ∀ j, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      |G h - ∫ ω, f j ω ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)| ≤
        δ + (Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)).real {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω})
    (hsignal : ∀ j, S * ((2 ^ j : ℕ) : ℝ) ^ (-a) ≤
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) G|)
    (hcalculus : ∀ j, ∀ U : ℝ, 0 ≤ U →
      (∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
        ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
        |iteratedDeriv (2 * m)
          (fun x : ℝ => ∫ ω, f j ω ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) x)) h| ≤ U) →
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
        (fun x : ℝ => ∫ ω, f j ω ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) x))| ≤
        (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2 * m) * U)
    : ENNReal.ofReal ((S /
      (4 * (2 * DerivC m (4 / (1 - (p₀ : ℝ))) * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)) *
        GeoBudget a m * a * Real.log 2)) * Real.log δ⁻¹) ≤
      ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀ := by
  let γ := -(p₀ : ℝ) / C
  let σ := 4 / (1 - (p₀ : ℝ))
  have hσ : 0 ≤ σ := div_nonneg (by norm_num) (sub_pos.mpr h₁).le
  have hθ : 0 < (2 * MomentC m + 1)⁻¹ := by positivity
  have hw : ∀ j, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      (0 < (p₀ : ℝ) + h * γ ∧ (p₀ : ℝ) + h * γ < 1) ∧
      |γ / ((Rate p₀ γ h : ℝ) * (1 - (Rate p₀ γ h : ℝ)))| ≤ σ ∧
      |((Rate p₀ γ h : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
        Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤ (2 * MomentC m + 1)⁻¹ := by
    intro j h hh
    exact (bernoulli_factory_local_window p₀ h₀ h₁ C ρ _ hC hρ hθ m (2 ^ j)
      (by positivity) hρsmall hρwindow h hh).2
  let T := min (1 / 2 : ℝ) (S / (2 : ℝ) ^ (2 * m + 1))
  let J := Nat.floor (Real.log (T / δ) / (a * Real.log 2)) + 1
  let A := 2 * DerivC m σ * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)
  let z := S / (2 * A)
  let K := S / (4 * A * GeoBudget a m * a * Real.log 2)
  have hT : 0 < T := lt_min (by norm_num) (div_pos hS (by positivity))
  have hT1 : T ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcount := resolvable_dyadic_scale_count a T δ ha hT hT1 hδ0 hδsmall
  have hδj : ∀ j < J, δ * ((2 ^ j : ℕ) : ℝ) ^ a ≤ S / (2 : ℝ) ^ (2 * m + 1) := by
    intro j hj
    exact (hcount.1 j hj).trans (min_le_right _ _)
  have hbudget := bernoulli_finite_dyadic_common_endpoint_charge ν p₀ h₀ h₁ M hM m
    a ρ γ σ δ S ha ham hρ hσ hS J f hf hfb G
    (fun j hj h hh => (hw j h hh).1) (fun j hj h hh => (hw j h hh).2.1)
    (fun j hj h hh => (hw j h hh).2.2)
    (fun j hj => herror j) (fun j hj => hsignal j) (fun j hj => hcalculus j) hδj
  have hA : 0 < A := by dsimp [A]; positivity
  have hz : 0 < z := div_pos hS (mul_pos (by norm_num) hA)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
  have hq := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
    (show a - (m : ℝ) < 0 by linarith)
  have hG : 0 < GeoBudget a m := by positivity
  have hcompare : GeoBudget a m * (K * Real.log δ⁻¹) ≤ (J : ℝ) * z := by
    calc
      _ = (Real.log δ⁻¹ / (2 * a * Real.log 2)) * z := by
        dsimp [K, z]
        field_simp [ne_of_gt hA, ne_of_gt hG, ha.ne', hlog2.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount.2 hz.le
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr hG) ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal (GeoBudget a m * (K * Real.log δ⁻¹)) :=
      (ENNReal.ofReal_mul hG.le).symm
    _ ≤ ENNReal.ofReal ((J : ℝ) * z) := ENNReal.ofReal_le_ofReal hcompare
    _ ≤ _ := hbudget

private lemma truncated_output_measurable
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (s : Set (Seed × (ℕ → Bool))) (hs : MeasurableSet[hM.measurableSpace] s) (n : ℕ) :
    MeasurableSet[(truncation_stopping hM n).measurableSpace]
      (s ∩ {ω | M ω ≤ (n : WithTop ℕ)}) := by
  have hh := (hM.measurableSet_inter_le_const_iff s n).mp
    (hs.inter (hM.measurableSet_le' n))
  rw [IsStoppingTime.measurableSet] at hh ⊢
  refine ⟨hh.1, fun i => ?_⟩
  convert hh.2 i using 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, truncation_cast]
  rfl

private lemma truncated_output_error
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Ω → WithTop ℕ) (hM : Measurable M) (s : Set Ω) (hs : MeasurableSet s)
    (n : ℕ) (G δ : ℝ) (herror : |G - μ.real s| ≤ δ) :
    |G - ∫ ω, (s ∩ {ω | M ω ≤ (n : WithTop ℕ)}).indicator (fun _ => (1 : ℝ)) ω ∂μ| ≤
      δ + μ.real {ω | (n : WithTop ℕ) < M ω} := by
  let t := {ω | M ω ≤ (n : WithTop ℕ)}
  have ht : MeasurableSet t := measurableSet_le hM measurable_const
  change |G - ∫ ω, (s ∩ t).indicator (1 : Ω → ℝ) ω ∂μ| ≤ _
  rw [integral_indicator_one (hs.inter ht)]
  have hpartition := measureReal_inter_add_sdiff (μ := μ) (s := s) ht
  have hdiff : μ.real (s \ t) ≤ μ.real {ω | (n : WithTop ℕ) < M ω} :=
    measureReal_mono (by
      intro ω hω
      exact lt_of_not_ge (show ¬ M ω ≤ (n : WithTop ℕ) from hω.2))
  have hnonneg : 0 ≤ μ.real (s \ t) := measureReal_nonneg
  calc
    _ = |(G - μ.real s) + μ.real (s \ t)| := by congr 1; linarith
    _ ≤ |G - μ.real s| + |μ.real (s \ t)| := abs_add_le _ _
    _ ≤ δ + μ.real {ω | (n : WithTop ℕ) < M ω} := by
      rw [abs_of_nonneg hnonneg]
      exact add_le_add herror hdiff

/-- One stopped output event, accurate under every parameter law, yields
logarithmic cost at the common zero-perturbation endpoint. The positive
signal and finite-difference calculus contracts are explicit interfaces. -/
theorem bernoulli_logarithmic_common_endpoint_charge
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (m : ℕ) (a ρ C δ S : ℝ) (ha : 0 < a) (ham : a < (m : ℝ))
    (hC : 1 ≤ C) (hρ : 0 < ρ) (hS : 0 < S)
    (hρsmall : (2 * m + 1 : ℕ) * ρ ≤ (1 / 4 : ℝ))
    (hρwindow : (2 * m + 1 : ℕ) * ρ ≤ (1 - (p₀ : ℝ)) * (2 * MomentC m + 1)⁻¹)
    (hδ0 : 0 < δ)
    (hδsmall : δ < (min (1 / 2 : ℝ) (S / (2 : ℝ) ^ (2 * m + 1))) ^ 2)
    (s : Set (Seed × (ℕ → Bool))) (hs : MeasurableSet[hM.measurableSpace] s)
    (G : ℝ → ℝ)
    (haccuracy : ∀ h ∈ Set.Ioc 0 (1 / 4 : ℝ),
      |G h - (Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)).real s| ≤ δ)
    (hsignal : ∀ j, S * ((2 ^ j : ℕ) : ℝ) ^ (-a) ≤
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) G|)
    (hcalculus : ∀ j, ∀ U : ℝ, 0 ≤ U →
      (∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
        ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
        |iteratedDeriv (2 * m) (fun x : ℝ => ∫ ω,
          (s ∩ {ω | M ω ≤ ((2 ^ j : ℕ) : WithTop ℕ)}).indicator (fun _ => (1 : ℝ)) ω
          ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) x)) h| ≤ U) →
      |Diff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) (fun x : ℝ => ∫ ω,
        (s ∩ {ω | M ω ≤ ((2 ^ j : ℕ) : WithTop ℕ)}).indicator (fun _ => (1 : ℝ)) ω
        ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) x))| ≤
        (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2 * m) * U)
    : ENNReal.ofReal ((S /
      (4 * (2 * DerivC m (4 / (1 - (p₀ : ℝ))) * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)) *
        GeoBudget a m * a * Real.log 2)) * Real.log δ⁻¹) ≤
      ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀ := by
  classical
  let f := fun (j : ℕ) =>
    (s ∩ {ω | M ω ≤ ((2 ^ j : ℕ) : WithTop ℕ)}).indicator (fun _ => (1 : ℝ))
  have hf : ∀ j, StronglyMeasurable[(truncation_stopping hM (2 ^ j)).measurableSpace] (f j) :=
    fun j => stronglyMeasurable_const.indicator (truncated_output_measurable M hM s hs (2 ^ j))
  have hfb : ∀ j ω, |f j ω| ≤ 1 := by
    intro j ω
    dsimp [f]
    by_cases hω : ω ∈ s ∩ {ω | M ω ≤ ((2 ^ j : ℕ) : WithTop ℕ)}
    · rw [Set.indicator_of_mem hω]; norm_num
    · rw [Set.indicator_of_notMem hω]; norm_num
  have hmeas := hM.measurable.mono hM.measurableSpace_le le_rfl
  have herr : ∀ j, ∀ h ∈ Set.Icc (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      ((2 * m + 1 : ℕ) * (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))),
      |G h - ∫ ω, f j ω ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)| ≤
        δ + (Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)).real
          {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω} := by
    intro j h hh
    have hlocal := bernoulli_factory_local_window p₀ h₀ h₁ C ρ
      ((2 * MomentC m + 1)⁻¹) hC hρ (by positivity) m (2 ^ j)
      (by positivity) hρsmall hρwindow h hh
    exact truncated_output_error _ M hmeas s (hM.measurableSpace_le _ hs) (2 ^ j)
      (G h) δ (haccuracy h hlocal.1)
  exact logarithmic_charge_of_output_windows ν p₀ h₀ h₁ M hM m a ρ C δ S ha ham
    hC hρ hS hρsmall hρwindow hδ0 hδsmall f hf hfb G herr hsignal hcalculus

/-- The noninteger-power target alone supplies the signal. Finite stopped
observations supply the smoothness needed for the difference budget, so neither
of these is an additional hypothesis. All scales charge the same endpoint law. -/
theorem bernoulli_power_target_logarithmic_endpoint
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (B C β ρ : ℝ) (m : ℕ) (hβ : 0 < β) (hβint : ∀ j : ℕ, β ≠ j)
    (hm : β / 2 < (m : ℝ)) (hC : 1 ≤ C) (hρ : 0 < ρ)
    (hρsmall : (2 * m + 1 : ℕ) * ρ ≤ (1 / 4 : ℝ))
    (hρwindow : (2 * m + 1 : ℕ) * ρ ≤ (1 - (p₀ : ℝ)) * (2 * MomentC m + 1)⁻¹)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδsmall : δ < (min (1 / 2 : ℝ)
      ((ρ ^ β * |(fwdDiff (1 : ℝ))^[2 * m] (fun u : ℝ => u ^ β) 1| / 16) /
        (2 : ℝ) ^ (2 * m + 1))) ^ 2)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (s : Set (Seed × (ℕ → Bool))) (hs : MeasurableSet[hM.measurableSpace] s)
    (haccuracy : ∀ h ∈ Set.Ioc 0 (1 / 4 : ℝ),
      |((1 - h / C) / (2 * B) - h ^ β / 16) -
        (Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)).real s| ≤ δ) :
    ENNReal.ofReal (((ρ ^ β *
      |(fwdDiff (1 : ℝ))^[2 * m] (fun u : ℝ => u ^ β) 1| / 16) /
      (4 * (2 * DerivC m (4 / (1 - (p₀ : ℝ))) * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)) *
        GeoBudget (β / 2) m * (β / 2) * Real.log 2)) * Real.log δ⁻¹) ≤
      ∫⁻ ω, EndpointCost (β / 2) (M ω) ∂Law ν p₀ := by
  classical
  have hm0 : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    rw [hz, Nat.cast_zero] at hm
    linarith
  have hR : 2 ≤ 2 * m := by omega
  have hsignal := NonintegerForwardDifferenceSignal.target_signal_scaled
    B C β ρ (2 * m) hR hρ hβint
  apply bernoulli_logarithmic_common_endpoint_charge ν p₀ h₀ h₁ M hM m (β / 2)
    ρ C δ _ (by positivity) hm hC hρ hsignal.1 hρsmall hρwindow hδ0 hδsmall
    s hs (fun h : ℝ => (1 - h / C) / (2 * B) - h ^ β / 16) haccuracy
  · intro j
    rw [difference_eq_fwdDiff (2 * m) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
      (fun h : ℝ => (1 - h / C) / (2 * B) - h ^ β / 16)]
    exact (hsignal.2 ((2 ^ j : ℕ) : ℝ) (by positivity)).ge
  · intro j U hU hD
    let n : ℕ := 2 ^ j
    let t := ρ / Real.sqrt (n : ℝ)
    let τ := fun ω => Trunc M n ω
    let f := (s ∩ {ω | M ω ≤ (n : WithTop ℕ)}).indicator (fun _ => (1 : ℝ))
    let γ := -(p₀ : ℝ) / C
    have ht : 0 < t := div_pos hρ (Real.sqrt_pos.mpr (by positivity))
    have hf : StronglyMeasurable[(truncation_stopping hM n).measurableSpace] f :=
      stronglyMeasurable_const.indicator (truncated_output_measurable M hM s hs n)
    have hfb : ∀ ω, |f ω| ≤ 1 := by
      intro ω
      dsimp [f]
      by_cases hω : ω ∈ s ∩ {ω | M ω ≤ (n : WithTop ℕ)}
      · rw [Set.indicator_of_mem hω]; norm_num
      · rw [Set.indicator_of_notMem hω]; norm_num
    have hinterval : t + (2 * m : ℕ) * t = (2 * m + 1 : ℕ) * t := by
      push_cast
      ring
    change |Diff (2 * m) t (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x))| ≤
      t ^ (2 * m) * U
    rw [difference_eq_fwdDiff (2 * m) t (fun x : ℝ => ∫ ω, f ω ∂Law ν (Rate p₀ γ x))]
    apply NonintegerForwardDifferenceSignal.abs_fwd_diff_iter_le _ (2 * m) ht
    · intro k hk y hy
      rw [hinterval] at hy
      have hlocal := bernoulli_factory_local_window p₀ h₀ h₁ C ρ
        ((2 * MomentC m + 1)⁻¹) hC hρ (by positivity) m n
        (by dsimp [n]; positivity) hρsmall hρwindow y hy
      let p := Rate p₀ γ y
      have hp : (p₀ : ℝ) + y * γ = (p : ℝ) :=
        (congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one)
          ⟨hlocal.2.1.1.le, hlocal.2.1.2.le⟩)).symm
      exact bernoulli_stopped_affine_iterated_differentiable ν p
        (by rw [← hp]; exact hlocal.2.1.1) (by rw [← hp]; exact hlocal.2.1.2)
        τ (truncation_stopping hM n) n (fun ω => truncation_le (M ω) n)
        γ (p₀ : ℝ) y hp f hf hfb k
    · intro y hy
      rw [hinterval] at hy
      exact hD y hy

/-- Constants are chosen before the seed law, error and stopping rule. Accuracy
for the noninteger-power target forces logarithmic worst-world fractional cost
on the legal positive-parameter interval, including infinite cost. -/
theorem bernoulli_power_target_logarithmic_uniform_cost
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (B C β : ℝ) (m : ℕ) (hβ : 0 < β) (hβint : ∀ j : ℕ, β ≠ j)
    (hm : β / 2 < (m : ℝ)) (hC : 1 ≤ C) :
    ∃ k : ℝ, 0 < k ∧ ∃ δ₀ : ℝ, δ₀ ∈ Set.Ioo 0 1 ∧
      ∀ (ν : Measure Seed), IsProbabilityMeasure ν →
      ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      ∀ (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
        (s : Set (Seed × (ℕ → Bool))), MeasurableSet[hM.measurableSpace] s →
      (∀ h ∈ Set.Ioc 0 (1 / 4 : ℝ),
        |((1 - h / C) / (2 * B) - h ^ β / 16) -
          (Law ν (Rate p₀ (-(p₀ : ℝ) / C) h)).real s| ≤ δ) →
      ENNReal.ofReal (k * Real.log δ⁻¹) ≤
        ⨆ h : {h : ℝ // h ∈ Set.Ioc 0 (1 / 4 : ℝ)},
          ∫⁻ ω, EndpointCost (β / 2) (M ω)
            ∂Law ν (Rate p₀ (-(p₀ : ℝ) / C) h.1) := by
  have ha : 0 < β / 2 := by positivity
  let θ := (2 * MomentC m + 1)⁻¹
  let H : ℝ := (2 * m + 1 : ℕ)
  let ρ : ℝ := min (1 / 4 : ℝ) ((1 - (p₀ : ℝ)) * θ) / H
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hρ : 0 < ρ := div_pos (lt_min (by norm_num)
    (mul_pos (sub_pos.mpr h₁) hθ)) hH
  have hρeq : H * ρ = min (1 / 4 : ℝ) ((1 - (p₀ : ℝ)) * θ) := by
    dsimp [ρ]
    field_simp
  have hρsmall : H * ρ ≤ (1 / 4 : ℝ) := hρeq.trans_le (min_le_left _ _)
  have hρwindow : H * ρ ≤ (1 - (p₀ : ℝ)) * θ := hρeq.trans_le (min_le_right _ _)
  let S := ρ ^ β * |(fwdDiff (1 : ℝ))^[2 * m] (fun u : ℝ => u ^ β) 1| / 16
  let A := 2 * DerivC m (4 / (1 - (p₀ : ℝ))) * ρ ^ (2 * m) + (2 : ℝ) ^ (2 * m + 1)
  let T := min (1 / 2 : ℝ) (S / (2 : ℝ) ^ (2 * m + 1))
  let k := S / (4 * A * GeoBudget (β / 2) m * (β / 2) * Real.log 2)
  have hS : 0 < S := div_pos (mul_pos (Real.rpow_pos_of_pos hρ _)
    (NonintegerForwardDifferenceSignal.unit_signal_pos β (2 * m) hβint)) (by norm_num)
  have hT : 0 < T := lt_min (by norm_num) (div_pos hS (by positivity))
  have hTle : T ≤ 1 / 2 := min_le_left _ _
  have hδ₀ : T ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
  have hq := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
    (show β / 2 - (m : ℝ) < 0 by linarith)
  have hGeo : 0 < GeoBudget (β / 2) m := by positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0 < k := div_pos hS (by positivity)
  refine ⟨k, hk, T ^ 2, hδ₀, ?_⟩
  intro ν hν δ hδ M hM s hs haccuracy
  have := hν
  have hbound := bernoulli_power_target_logarithmic_endpoint ν p₀ h₀ h₁ B C β ρ m
    hβ hβint hm hC hρ hρsmall hρwindow δ hδ.1 hδ.2 M hM s hs haccuracy
  apply hbound.trans
  let p := fun j : ℕ => Rate p₀ (-(p₀ : ℝ) / C) (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ))
  have hw : ∀ j, (ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ∈ Set.Ioc 0 (1 / 4 : ℝ) ∧
      |((p j : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
        Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤ θ := by
    intro j
    let t := ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ)
    have ht : 0 < t := div_pos hρ (Real.sqrt_pos.mpr (by positivity))
    have hH1 : (1 : ℝ) ≤ H := by
      dsimp [H]
      exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
    have hi : t ∈ Set.Icc t (H * t) := ⟨le_rfl, by nlinarith⟩
    have hh := bernoulli_factory_local_window p₀ h₀ h₁ C ρ θ hC hρ hθ m (2 ^ j)
      (by positivity) hρsmall hρwindow t hi
    exact ⟨hh.1, hh.2.2.2⟩
  have hb := bernoulli_common_endpoint_budget ν p₀ h₀ h₁ p M hM (β / 2) m ha hm
    (fun j => (hw j).2)
  apply hb.2.2.2.1
  intro j
  exact le_iSup_of_le ⟨ρ / Real.sqrt ((2 ^ j : ℕ) : ℝ), (hw j).1⟩ le_rfl

end D5.S3.Estimation.SequentialDecisionRisk.BernoulliCommonEndpointCharge
