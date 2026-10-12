/- GID: D5/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A resolvable finite-difference signal charges one common endpoint stopping moment. -/

import D5.S3.Estimation.SequentialDecisionRisk.BernoulliStoppedCoefficientBudget
import Mathlib.Data.Nat.Choose.Sum

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

end D5.S3.Estimation.SequentialDecisionRisk.BernoulliCommonEndpointCharge
