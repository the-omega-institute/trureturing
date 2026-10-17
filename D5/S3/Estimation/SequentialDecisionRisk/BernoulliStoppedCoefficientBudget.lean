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
open scoped BigOperators ENNReal Topology
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

private lemma product_expansion (k : ℕ) (v : Fin k → ℝ) :
    (fun t : ℝ => ∏ i, (1 + t * v i)) =
      fun t => ∑ s ∈ (univ : Finset (Fin k)).powerset,
        t ^ s.card * ∏ i ∈ s, v i := by
  classical
  funext t
  rw [prod_one_add]
  apply sum_congr rfl
  intro s hs
  rw [prod_mul_distrib, prod_const]

private lemma product_deriv_zero (k : ℕ) (v : Fin k → ℝ) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => ∏ i, (1 + t * v i)) 0 =
      (r.factorial : ℝ) * Elem k v r := by
  classical
  have hpoly := product_expansion k v
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

private lemma integrable_product_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (v : Fin n → Ω → ℝ) (hv : ∀ i, Measurable (v i))
    (b : ℝ) (hvb : ∀ i ω, |v i ω| ≤ b)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1)
    (s : Finset (Fin n)) : Integrable (fun ω => f ω * ∏ i ∈ s, v i ω) μ := by
  let C := fun (s : Finset (Fin n)) (ω : Ω) => f ω * ∏ i ∈ s, v i ω
  refine ⟨(hf.mul (s.measurable_prod (fun i hi => hv i))).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := b ^ s.card) (ae_of_all _ (fun ω => ?_))⟩
  change ‖f ω * ∏ i ∈ s, v i ω‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_prod]
  calc
    _ ≤ 1 * ∏ _i ∈ s, b := mul_le_mul (hfb ω)
      (Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hvb i ω))
      (prod_nonneg (fun i hi => abs_nonneg _)) (by norm_num)
    _ = _ := by simp

private lemma integral_product_expansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (v : Fin n → Ω → ℝ) (hv : ∀ i, Measurable (v i))
    (b : ℝ) (hvb : ∀ i ω, |v i ω| ≤ b)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1) :
    (fun t : ℝ => ∫ ω, f ω * ∏ i, (1 + t * v i ω) ∂μ) =
      fun t => ∑ s ∈ (univ : Finset (Fin n)).powerset,
        t ^ s.card * ∫ ω, f ω * ∏ i ∈ s, v i ω ∂μ := by
  classical
  let C := fun (s : Finset (Fin n)) (ω : Ω) => f ω * ∏ i ∈ s, v i ω
  have hCi : ∀ s, Integrable (C s) μ :=
    integrable_product_coefficient μ n v hv b hvb f hf hfb
  funext t
  calc
    _ = ∫ ω, ∑ s ∈ (univ : Finset (Fin n)).powerset, t ^ s.card * C s ω ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro ω
      change f ω * (∏ i, (1 + t * v i ω)) =
        ∑ s ∈ (univ : Finset (Fin n)).powerset, t ^ s.card * C s ω
      rw [congrFun (product_expansion n (fun i => v i ω)) t, mul_sum]
      apply sum_congr rfl
      intro s hs
      dsimp [C]
      ring
    _ = ∑ s ∈ (univ : Finset (Fin n)).powerset,
        ∫ ω, t ^ s.card * C s ω ∂μ :=
      integral_finsetSum _ (fun s hs => (hCi s).const_mul _)
    _ = _ := by simp_rw [integral_const_mul]; rfl

private lemma contDiff_integral_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (v : Fin n → Ω → ℝ) (hv : ∀ i, Measurable (v i))
    (b : ℝ) (hvb : ∀ i ω, |v i ω| ≤ b)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1) :
    ContDiff ℝ ⊤ (fun t : ℝ => ∫ ω, f ω * ∏ i, (1 + t * v i ω) ∂μ) := by
  rw [integral_product_expansion μ n v hv b hvb f hf hfb]
  fun_prop

private lemma integral_iteratedDeriv_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n r : ℕ)
    (v : Fin n → Ω → ℝ) (hv : ∀ i, Measurable (v i))
    (b : ℝ) (hvb : ∀ i ω, |v i ω| ≤ b)
    (f : Ω → ℝ) (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1) :
    iteratedDeriv r (fun t : ℝ => ∫ ω, f ω * ∏ i, (1 + t * v i ω) ∂μ) 0 =
      ∫ ω, f ω * iteratedDeriv r (fun t : ℝ => ∏ i, (1 + t * v i ω)) 0 ∂μ := by
  classical
  let C := fun (s : Finset (Fin n)) (ω : Ω) => f ω * ∏ i ∈ s, v i ω
  have hCi : ∀ s, Integrable (C s) μ :=
    integrable_product_coefficient μ n v hv b hvb f hf hfb
  have hF := integral_product_expansion μ n v hv b hvb f hf hfb
  have hD : (fun ω => f ω * iteratedDeriv r
      (fun t : ℝ => ∏ i, (1 + t * v i ω)) 0) =
      fun ω => ∑ s ∈ (univ : Finset (Fin n)).powerset,
        iteratedDeriv r (fun t : ℝ => t ^ s.card) 0 * C s ω := by
    funext ω
    rw [product_expansion, iteratedDeriv_fun_sum (by intro s hs; fun_prop)]
    simp_rw [iteratedDeriv_mul_const_field]
    rw [mul_sum]
    apply sum_congr rfl
    intro s hs
    dsimp [C]
    ring
  rw [hF, hD, iteratedDeriv_fun_sum (by intro s hs; fun_prop),
    integral_finsetSum _ (fun s hs => (hCi s).const_mul _)]
  simp_rw [iteratedDeriv_mul_const_field, integral_const_mul]
  rfl

omit [MeasurableSpace Seed] in
private lemma padded_product (τ : Seed × (ℕ → Bool) → ℕ) (n : ℕ)
    (hτn : ∀ ω, τ ω ≤ n) (v : ℕ → Seed × (ℕ → Bool) → ℝ) (t : ℝ)
    (ω : Seed × (ℕ → Bool)) :
    (∏ i : Fin n, (1 + t * if i.1 < τ ω then v i.1 ω else 0)) =
      ∏ i : Fin (τ ω), (1 + t * v i.1 ω) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 + t * if i < τ ω then v i ω else 0),
    Fin.prod_univ_eq_prod_range (fun i => 1 + t * v i ω)]
  calc
    _ = ∏ i ∈ range (τ ω), (1 + t * if i < τ ω then v i ω else 0) := by
      symm
      apply prod_subset (range_mono (hτn ω))
      intro i hin hi
      simp [not_lt.mpr (Nat.le_of_not_gt (fun h => hi (mem_range.mpr h)))]
    _ = _ := prod_congr rfl (fun i hi => by simp [mem_range.mp hi])

private lemma stopped_padding_measurable
    (p₀ : unitInterval) (τ : Seed × (ℕ → Bool) → ℕ) (ht : Measurable τ)
    (q : ℝ) (i : ℕ) :
    Measurable (fun ω => if i < τ ω then q * Bit p₀ i ω else 0) := by
  apply Measurable.ite (measurableSet_lt measurable_const ht) _ measurable_const
  apply Measurable.const_mul
  exact ((Measurable.of_discrete : Measurable (fun b : Bool =>
    (if b then (1 : ℝ) else 0) - (p₀ : ℝ))).comp
    ((measurable_pi_apply i).comp measurable_snd))

omit [MeasurableSpace Seed] in
private lemma stopped_padding_bound
    (p₀ : unitInterval) (τ : Seed × (ℕ → Bool) → ℕ) (q : ℝ)
    (i : ℕ) (ω : Seed × (ℕ → Bool)) :
    |if i < τ ω then q * Bit p₀ i ω else 0| ≤ |q| := by
  change |if i < τ ω then q * Bit p₀ i ω else 0| ≤ |q|
  split_ifs with hi
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (centered_bit_bound p₀ i ω) (abs_nonneg q)).trans_eq
      (mul_one _)
  · simp

private lemma contDiff_stopped_output
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p₀ : unitInterval)
    (τ : Seed × (ℕ → Bool) → ℕ) (ht : Measurable τ)
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) (q : ℝ)
    (f : Seed × (ℕ → Bool) → ℝ) (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1) :
    ContDiff ℝ ⊤ (fun t : ℝ => ∫ ω, f ω *
      ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω)) ∂Law ν p₀) := by
  have hp := contDiff_integral_product (Law ν p₀) n
    (fun (i : Fin n) ω => if i.1 < τ ω then q * Bit p₀ i.1 ω else 0)
    (fun i => stopped_padding_measurable p₀ τ ht q i.1) |q|
    (fun i ω => stopped_padding_bound p₀ τ q i.1 ω) f hf hfb
  convert hp using 1
  funext t
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  exact congrArg (fun z : ℝ => f ω * z)
    (padded_product τ n hτn (fun i ω => q * Bit p₀ i ω) t ω).symm

/-- The even derivative of a bounded stopped-output likelihood polynomial
is controlled by the same random stopping-time moment. -/
theorem bernoulli_stopped_output_derivative_budget
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m)
    (q : ℝ) (f : Seed × (ℕ → Bool) → ℝ)
    (hf : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1) :
    ENNReal.ofReal |iteratedDeriv (2 * m)
      (fun t : ℝ => ∫ ω, f ω *
        ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω)) ∂Law ν p₀) 0| ≤
      ENNReal.ofReal ((2 * m).factorial * |q| ^ (2 * m) * (2 * MomentC m + 1)) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
  have ht : Measurable τ := by
    simpa using (hτ.measurable.mono hτ.measurableSpace_le le_rfl).untopD 0
  let v := fun (i : Fin n) (ω : Seed × (ℕ → Bool)) =>
    if i.1 < τ ω then q * Bit p₀ i.1 ω else 0
  have hv : ∀ i, Measurable (v i) := fun i =>
    stopped_padding_measurable p₀ τ ht q i.1
  have hb : ∀ i ω, |v i ω| ≤ |q| := fun i ω =>
    stopped_padding_bound p₀ τ q i.1 ω
  have hp : ∀ ω, (fun t : ℝ => ∏ i : Fin n, (1 + t * v i ω)) =
      fun t : ℝ => ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω)) := by
    intro ω
    funext t
    exact padded_product τ n hτn (fun i ω => q * Bit p₀ i ω) t ω
  have hx := integral_iteratedDeriv_product (Law ν p₀) n (2 * m) v hv |q| hb f hf hfb
  have hF : (fun t : ℝ => ∫ ω, f ω * ∏ i : Fin n, (1 + t * v i ω) ∂Law ν p₀) =
      fun t : ℝ => ∫ ω, f ω * ∏ i : Fin (τ ω),
        (1 + t * (q * Bit p₀ i.1 ω)) ∂Law ν p₀ := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => congrArg (fun z : ℝ => f ω * z) (congrFun (hp ω) t))
  rw [hF] at hx
  simp_rw [hp] at hx
  rw [hx]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal |f ω * iteratedDeriv (2 * m)
        (fun t : ℝ => ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω))) 0|
        ∂Law ν p₀ := by
      simpa only [Real.enorm_eq_ofReal_abs] using
        (enorm_integral_le_lintegral_enorm
          (fun ω => f ω * iteratedDeriv (2 * m)
            (fun t : ℝ => ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω))) 0)
          (μ := Law ν p₀))
    _ ≤ _ := bernoulli_stopped_even_derivative_budget ν p₀ h₀ h₁ τ hτ n hτn hm q f hfb

private lemma stopped_output_parameter_identity
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (f : Seed × (ℕ → Bool) → ℝ) (hf : StronglyMeasurable[hτ.measurableSpace] f)
    (t γ : ℝ) (hp : (p : ℝ) = (p₀ : ℝ) + t * γ) :
    (∫ ω, f ω ∂Law ν p) = ∫ ω, f ω *
      ∏ i : Fin (τ ω), (1 + t * (γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) * Bit p₀ i.1 ω))
        ∂Law ν p₀ := by
  have ht : Measurable τ := by
    simpa using (hτ.measurable.mono hτ.measurableSpace_le le_rfl).untopD 0
  have hL := stopped_like_measurable p₀ p τ ht
  rw [bernoulli_stopped_output_identity ν p₀ p h₀ h₁ τ hτ f hf,
    integral_withDensity_eq_integral_toReal_smul hL.ennreal_ofReal
      (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  have hprod : (∏ i ∈ range (τ ω),
      if ω.2 i then (p : ℝ) / (p₀ : ℝ) else (1 - (p : ℝ)) / (1 - (p₀ : ℝ))) =
      ∏ i : Fin (τ ω), (1 + t *
        (γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) * Bit p₀ i.1 ω)) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => 1 + t *
      (γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) * Bit p₀ i ω))]
    apply prod_congr rfl
    intro i hi
    change (if ω.2 i then (p : ℝ) / (p₀ : ℝ) else
      (1 - (p : ℝ)) / (1 - (p₀ : ℝ))) = 1 + t *
      (γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) *
        ((if ω.2 i then (1 : ℝ) else 0) - (p₀ : ℝ)))
    cases ω.2 i <;> simp only [Bool.false_eq_true, ↓reduceIte, hp]
    all_goals field_simp [ne_of_gt h₀, ne_of_gt (sub_pos.mpr h₁)] <;> ring
  change (ENNReal.ofReal (∏ i ∈ range (τ ω),
      if ω.2 i then (p : ℝ) / (p₀ : ℝ) else (1 - (p : ℝ)) / (1 - (p₀ : ℝ)))).toReal • f ω =
      f ω * ∏ i : Fin (τ ω), (1 + t *
        (γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) * Bit p₀ i.1 ω))
  rw [smul_eq_mul, ENNReal.toReal_ofReal (by
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact div_nonneg p.2.1 p₀.2.1
    · exact div_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr p₀.2.2)), hprod, mul_comm]

/-- Every iterated derivative of a bounded stopped observation is differentiable
at each interior point of an affine Bernoulli family. -/
theorem bernoulli_stopped_affine_iterated_differentiable
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n)
    (γ x h : ℝ) (hp : x + h * γ = (p₀ : ℝ))
    (f : Seed × (ℕ → Bool) → ℝ)
    (hf : StronglyMeasurable[hτ.measurableSpace] f) (hfb : ∀ ω, |f ω| ≤ 1)
    (k : ℕ) :
    DifferentiableAt ℝ (iteratedDeriv k (fun t : ℝ => ∫ ω, f ω ∂Law ν
      (Set.projIcc 0 1 zero_le_one (x + t * γ)))) h := by
  have ht : Measurable τ := by
    simpa using (hτ.measurable.mono hτ.measurableSpace_le le_rfl).untopD 0
  let q := γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))
  let P := fun t : ℝ => ∫ ω, f ω *
    ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω)) ∂Law ν p₀
  have hP : ContDiff ℝ ⊤ P := contDiff_stopped_output ν p₀ τ ht n hτn q f
    (hf.mono hτ.measurableSpace_le).measurable hfb
  have hQ : ContDiff ℝ ⊤ (fun t => P (t - h)) := hP.comp (by fun_prop)
  have he : (fun t : ℝ => ∫ ω, f ω ∂Law ν
      (Set.projIcc 0 1 zero_le_one (x + t * γ))) =ᶠ[𝓝 h] (fun t => P (t - h)) := by
    have hc : Continuous (fun t : ℝ => x + t * γ) := by fun_prop
    have hw : ∀ᶠ t : ℝ in 𝓝 h, x + t * γ ∈ Set.Ioo 0 1 :=
      hc.continuousAt.preimage_mem_nhds (by simpa only [hp] using Ioo_mem_nhds h₀ h₁)
    filter_upwards [hw] with t ht
    apply stopped_output_parameter_identity ν p₀ _ h₀ h₁ τ hτ f hf (t - h) γ
    rw [Set.projIcc_of_mem (h := zero_le_one) ⟨ht.1.le, ht.2.le⟩]
    dsimp
    rw [← hp]
    ring
  exact (hQ.differentiable_iteratedDeriv k (by simp)).differentiableAt.congr_of_eventuallyEq
    (he.iteratedDeriv k)

/-- The actual parameter law of every bounded stopped observation has an
even derivative paid by its stopping-time moment at the same base point.
Projection to `[0,1]` only defines the probability law outside the local
parameter window. -/
theorem bernoulli_stopped_affine_derivative_budget
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m)
    (γ x h : ℝ) (hp : x + h * γ = (p₀ : ℝ)) (f : Seed × (ℕ → Bool) → ℝ)
    (hf : StronglyMeasurable[hτ.measurableSpace] f) (hfb : ∀ ω, |f ω| ≤ 1) :
    ENNReal.ofReal |iteratedDeriv (2 * m)
      (fun t : ℝ => ∫ ω, f ω ∂Law ν
        (Set.projIcc 0 1 zero_le_one (x + t * γ))) h| ≤
      ENNReal.ofReal ((2 * m).factorial *
        |γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| ^ (2 * m) * (2 * MomentC m + 1)) *
        ∫⁻ ω, ENNReal.ofReal ((τ ω : ℝ) ^ m) ∂Law ν p₀ := by
  let q := γ / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))
  have he : (fun t : ℝ => ∫ ω, f ω ∂Law ν
      (Set.projIcc 0 1 zero_le_one (x + (h + t) * γ))) =ᶠ[𝓝 0]
      (fun t : ℝ => ∫ ω, f ω *
        ∏ i : Fin (τ ω), (1 + t * (q * Bit p₀ i.1 ω)) ∂Law ν p₀) := by
    have hc : Continuous (fun t : ℝ => (p₀ : ℝ) + t * γ) := by fun_prop
    have hw : ∀ᶠ t : ℝ in 𝓝 0, (p₀ : ℝ) + t * γ ∈ Set.Ioo 0 1 :=
      hc.continuousAt.preimage_mem_nhds (by simpa using Ioo_mem_nhds h₀ h₁)
    filter_upwards [hw] with t ht
    have hrate : x + (h + t) * γ = (p₀ : ℝ) + t * γ := by rw [← hp]; ring
    rw [hrate]
    apply stopped_output_parameter_identity ν p₀ _ h₀ h₁ τ hτ f hf t γ
    exact congrArg Subtype.val (Set.projIcc_of_mem (h := zero_le_one) ⟨ht.1.le, ht.2.le⟩)
  have hd := he.iteratedDeriv_eq (2 * m)
  have htrans : iteratedDeriv (2 * m)
      (fun t : ℝ => ∫ ω, f ω ∂Law ν (Set.projIcc 0 1 zero_le_one (x + (h + t) * γ))) 0 =
      iteratedDeriv (2 * m)
        (fun t : ℝ => ∫ ω, f ω ∂Law ν (Set.projIcc 0 1 zero_le_one (x + t * γ))) h := by
    simpa only [add_zero] using congrFun (iteratedDeriv_comp_const_add (2 * m)
      (fun t : ℝ => ∫ ω, f ω ∂Law ν (Set.projIcc 0 1 zero_le_one (x + t * γ))) h) 0
  rw [htrans] at hd
  rw [hd]
  exact bernoulli_stopped_output_derivative_budget ν p₀ h₀ h₁ τ hτ n hτn hm q f
    (hf.mono hτ.measurableSpace_le).measurable hfb


end D5.S3.Estimation.SequentialDecisionRisk.BernoulliStoppedCoefficientBudget

