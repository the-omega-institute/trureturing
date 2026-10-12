/- GID: D5/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/BernoulliStoppedCoefficientBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even stopped Bernoulli likelihood coefficients retain random stopping-time budgets. -/

import D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.BernoulliStoppedCoefficientBudget
open SeededBernoulliStoppedMoment
variable {Seed : Type*} [MeasurableSpace Seed]

local notation "Elem" => fun (k : ℕ) (v : Fin k → ℝ) (r : ℕ) =>
  MvPolynomial.aeval v (MvPolynomial.esymm (Fin k) ℝ r)
local notation "PowerSum" => fun (k : ℕ) (v : Fin k → ℝ) (r : ℕ) =>
  ∑ i, v i ^ r
local notation "Bit" => fun (p : unitInterval) (i : ℕ) (ω : Seed × (ℕ → Bool)) =>
  (if ω.2 i then (1 : ℝ) else 0) - (p : ℝ)
local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p))
local notation "MomentC" => fun m : ℕ =>
  (((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m * (2 : ℝ) ^ (2 * m))

private lemma elem_bound_of_power_sums (k : ℕ) (v : Fin k → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hP : ∀ j : ℕ, 0 < j → |PowerSum k v j| ≤ x ^ j) (r : ℕ) :
    |Elem k v r| ≤ x ^ r := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r = 0
    · subst r
      simp [MvPolynomial.esymm_zero]
    have hr0 : 0 < r := Nat.pos_of_ne_zero hr
    let I := (Finset.antidiagonal r).filter (fun a => a.1 < r)
    have hnew : (r : ℝ) * Elem k v r = (-1 : ℝ) ^ (r + 1) *
        ∑ a ∈ I, (-1 : ℝ) ^ a.1 * Elem k v a.1 * PowerSum k v a.2 := by
      have h := congrArg (MvPolynomial.aeval v) (MvPolynomial.mul_esymm_eq_sum (Fin k) ℝ r)
      simpa [MvPolynomial.psum, map_sum, map_mul, map_pow, I] using h
    have hcard : I.card ≤ r := by
      calc
        I.card ≤ (range r).card := by
          apply card_le_card_of_injOn (f := Prod.fst)
          · intro a ha
            exact mem_range.mpr (mem_filter.mp ha).2
          · intro a ha b hb hab
            have ha' := Finset.mem_antidiagonal.mp (mem_filter.mp ha).1
            have hb' := Finset.mem_antidiagonal.mp (mem_filter.mp hb).1
            apply Prod.ext hab
            omega
        _ = r := card_range r
    have hterm : ∀ a ∈ I, |(-1 : ℝ) ^ a.1 * Elem k v a.1 * PowerSum k v a.2| ≤ x ^ r := by
      intro a ha
      have ha0 := (mem_filter.mp ha).2
      have hab := Finset.mem_antidiagonal.mp (mem_filter.mp ha).1
      have ha2 : 0 < a.2 := by omega
      calc
        _ = |Elem k v a.1| * |PowerSum k v a.2| := by
          rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        _ ≤ x ^ a.1 * x ^ a.2 :=
          mul_le_mul (ih a.1 ha0) (hP a.2 ha2) (abs_nonneg _) (pow_nonneg hx _)
        _ = x ^ r := by rw [← pow_add, hab]
    have hineq : (r : ℝ) * |Elem k v r| ≤ (r : ℝ) * x ^ r := by
      calc
        _ = |∑ a ∈ I, (-1 : ℝ) ^ a.1 * Elem k v a.1 * PowerSum k v a.2| := by
          have h := congrArg abs hnew
          simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ r from Nat.cast_nonneg r), abs_pow,
            abs_neg, abs_one, one_pow, one_mul] using h
        _ ≤ ∑ a ∈ I, |(-1 : ℝ) ^ a.1 * Elem k v a.1 * PowerSum k v a.2| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ I, x ^ r := sum_le_sum hterm
        _ = (I.card : ℝ) * x ^ r := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hx _)
    exact (mul_le_mul_iff_right₀ (by exact_mod_cast hr0 : (0 : ℝ) < r)).1 hineq

private lemma even_elem_bound (k : ℕ) (v : Fin k → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (m : ℕ) (hm : 0 < m) :
    |Elem k v (2 * m)| ≤ |∑ i, v i| ^ (2 * m) + (k : ℝ) ^ m := by
  classical
  by_cases hk : k = 0
  · subst k
    have he : MvPolynomial.esymm (Fin 0) ℝ (2 * m) = 0 := by
      unfold MvPolynomial.esymm
      rw [Finset.powersetCard_eq_empty.mpr (by simp; omega)]
      simp
    simp [he, hm.ne']
  let x := max |∑ i, v i| (Real.sqrt (k : ℝ))
  have hx : 0 ≤ x := (abs_nonneg _).trans (le_max_left _ _)
  have hx1 : 1 ≤ x := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    have hs : (1 : ℝ) ≤ Real.sqrt (k : ℝ) :=
      Real.one_le_sqrt.mpr hk1
    exact hs.trans (le_max_right _ _)
  have hp : ∀ j : ℕ, 0 < j → |PowerSum k v j| ≤ x ^ j := by
    intro j hj
    by_cases hj1 : j = 1
    · subst j
      simpa only [pow_one] using (le_max_left |∑ i, v i| (Real.sqrt (k : ℝ)))
    have hj2 : 2 ≤ j := by omega
    have hb : |PowerSum k v j| ≤ (k : ℝ) := by
      calc
        _ ≤ ∑ i : Fin k, |v i ^ j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin k, (1 : ℝ) := by
          apply sum_le_sum
          intro i hi
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hv i)
        _ = k := by simp
    calc
      _ ≤ (k : ℝ) := hb
      _ = (Real.sqrt (k : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg k)).symm
      _ ≤ x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) _
      _ ≤ x ^ j := pow_le_pow_right₀ hx1 hj2
  have h := elem_bound_of_power_sums k v x hx hp (2 * m)
  have hsplit : x ^ (2 * m) ≤ |∑ i, v i| ^ (2 * m) + (k : ℝ) ^ m := by
    by_cases hs : Real.sqrt (k : ℝ) ≤ |∑ i, v i|
    · dsimp [x]
      rw [max_eq_left hs]
      exact le_add_of_nonneg_right (by positivity)
    · dsimp [x]
      rw [max_eq_right (le_of_not_ge hs), pow_mul, Real.sq_sqrt (Nat.cast_nonneg k)]
      exact le_add_of_nonneg_left (by positivity)
  exact h.trans hsplit

private lemma product_deriv_zero (k : ℕ) (v : Fin k → ℝ) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => ∏ i, (1 + t * v i)) 0 =
      (r.factorial : ℝ) * Elem k v r := by
  classical
  have hpoly : (fun t : ℝ => ∏ i, (1 + t * v i)) =
      fun t => ∑ s ∈ (univ : Finset (Fin k)).powerset,
        t ^ s.card * ∏ i ∈ s, v i := by
    funext t
    rw [prod_one_add]
    apply sum_congr rfl
    intro s hs
    rw [prod_mul_distrib, prod_const]
  rw [hpoly, iteratedDeriv_fun_sum (by intro s hs; fun_prop)]
  simp_rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
  simp only [Nat.cast_ite, Nat.cast_zero]
  change (∑ s ∈ (univ : Finset (Fin k)).powerset,
    (if r = s.card then (s.card.factorial : ℝ) else 0) * ∏ i ∈ s, v i) = _
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
  rw [mul_sum, powersetCard_eq_filter, sum_filter]
  apply sum_congr rfl
  intro s hs
  by_cases h : s.card = r
  · simp [h]
  · simp [h, Ne.symm h]

private lemma elem_scale (k : ℕ) (v : Fin k → ℝ) (q : ℝ) (r : ℕ) :
    Elem k (fun i => q * v i) r = q ^ r * Elem k v r := by
  classical
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  simpa only [smul_eq_mul, Multiset.map_map, Function.comp_def] using
    (Multiset.pow_smul_esymm q r ((univ : Finset (Fin k)).val.map v)).symm

/-- Every even likelihood coefficient at a bounded Bernoulli stopping time
is paid by the same stopping-time moment. The estimate applies to arbitrary
independent private seeds and has no deterministic-horizon factor. -/
theorem bernoulli_stopped_even_coefficient_budget
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m) :
    (∫⁻ ω, ENNReal.ofReal |Elem (τ ω) (fun i : Fin (τ ω) => Bit p₀ i.1 ω) (2 * m)| ∂Law ν p₀) ≤
      ENNReal.ofReal (2 * MomentC m + 1) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
  have ht : Measurable τ := by
    simpa using (hτ.measurable.mono hτ.measurableSpace_le le_rfl).untopD 0
  have htm : Measurable (fun ω => (τ ω : ℝ) ^ m) :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht).pow_const _
  have hti : Integrable (fun ω => (τ ω : ℝ) ^ m) (Law ν p₀) :=
    ⟨htm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := (n : ℝ) ^ m)
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast hτn ω))⟩
  have hb : ∀ i ω, |Bit p₀ i ω| ≤ 1 := centered_bit_bound p₀
  have hpoint : ∀ ω, |Elem (τ ω) (fun i : Fin (τ ω) => Bit p₀ i.1 ω) (2 * m)| ≤
      |∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m) + (τ ω : ℝ) ^ m := by
    intro ω
    have h := even_elem_bound (τ ω) (fun i : Fin (τ ω) => Bit p₀ i.1 ω)
      (fun i => hb i.1 ω) m hm
    rw [Fin.sum_univ_eq_sum_range (fun i => Bit p₀ i ω)] at h
    exact h
  have hscore : (∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m))
      ∂Law ν p₀) ≤ ENNReal.ofReal (2 * MomentC m) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hti (ae_of_all _ (fun ω => by positivity)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * MomentC m)]
    exact bernoulli_stopped_score_moment ν p₀ h₀ h₁ τ hτ n hτn hm
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m)) +
        ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_add (by positivity :
        0 ≤ |∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m)) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpoint ω)
    _ = (∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m)) ∂Law ν p₀) +
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ :=
      lintegral_add_right _ htm.ennreal_ofReal
    _ ≤ ENNReal.ofReal (2 * MomentC m) *
        (∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀) +
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := add_le_add hscore le_rfl
    _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_one, add_mul, one_mul]

/-- A bounded output multiplier and a fixed parameter slope preserve the
even-derivative budget of the stopped likelihood polynomial. -/
theorem bernoulli_stopped_even_derivative_budget
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m)
    (q : ℝ) (f : Seed × (ℕ → Bool) → ℝ) (hf : ∀ ω, |f ω| ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal |f ω * iteratedDeriv (2 * m)
      (fun t : ℝ => ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω))) 0| ∂Law ν p₀) ≤
      ENNReal.ofReal ((2 * m).factorial * |q| ^ (2 * m) * (2 * MomentC m + 1)) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
  have hcoeff := bernoulli_stopped_even_coefficient_budget ν p₀ h₀ h₁ τ hτ n hτn hm
  let d : ℝ := (2 * m).factorial * |q| ^ (2 * m)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal d *
        ENNReal.ofReal |Elem (τ ω) (fun i : Fin (τ ω) => Bit p₀ i.1 ω) (2 * m)|
        ∂Law ν p₀ := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [product_deriv_zero, elem_scale, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (2 * m).factorial from Nat.cast_nonneg _), abs_pow]
      rw [← ENNReal.ofReal_mul hd]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 1 * ((2 * m).factorial * (|q| ^ (2 * m) *
            |Elem (τ ω) (fun i : Fin (τ ω) => Bit p₀ i.1 ω) (2 * m)|)) :=
          mul_le_mul_of_nonneg_right (hf ω) (by positivity)
        _ = _ := by dsimp [d]; ring
    _ = ENNReal.ofReal d *
        ∫⁻ ω, ENNReal.ofReal |Elem (τ ω)
          (fun i : Fin (τ ω) => Bit p₀ i.1 ω) (2 * m)| ∂Law ν p₀ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal d * (ENNReal.ofReal (2 * MomentC m + 1) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀) :=
      mul_le_mul_right hcoeff _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hd]


end D5.S3.Estimation.SequentialDecisionRisk.BernoulliStoppedCoefficientBudget

