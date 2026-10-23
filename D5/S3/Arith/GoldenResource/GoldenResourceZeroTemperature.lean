/- GID: D5/S3/Arith/GoldenResource/GoldenResourceZeroTemperature
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenResourceZeroTemperature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Resource Boltzmann sums factor over primes and reach the optimum at zero temperature. -/

import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/- Library-search audit trail:
   1. D5 searches for boltzmann, ZeroTemperature, zero_temperature, tropical, log_sum_exp,
      eulerProduct and goldenResourceObjective found no Boltzmann sum of the resource
      objective, no Euler product for it and no zero-temperature limit.
   2. Pinned Mathlib searches for logSumExp, log_sum_exp and Laplace-principle limits of
      series found none. Reused: EulerProduct.eulerProduct_tprod,
      tendsto_tsum_of_dominated_convergence, harmonic_le_one_add_log,
      Real.log_le_rpow_div and Real.summable_nat_rpow_inv.
   3. Preregistered witnesses: the harmonic-logarithm estimate giving summability exactly
      when `1 < beta * lambda`, coprime additivity of the objective feeding the Euler
      product, and dominated convergence of the weights shifted by the frozen supremum to
      the indicator of the optimizers. Frozen inputs: the objective factorization, the
      attained optimizer and the supremum formula. -/

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature

open Filter Topology Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum

noncomputable section

/-- The Boltzmann sum `∑ₙ (σ(n)/n)^β n^(-βλ)` of the resource objective over `n ≥ 1`. -/
def boltzmannSum (lambda beta : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (beta * goldenResourceObjective lambda (n + 1))

/-- The optimal resource value: the sum of all positive prime-layer gains at price `λ`. -/
def groundValue {lambda : ℝ} (hlambda : 0 < lambda) : ℝ :=
  ∑ pk ∈ (positive_part_sum_finite_support hlambda).toFinset,
    Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - lambda)

private theorem one_le_divisor_inverse_sum {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have := Finset.single_le_sum (f := fun d : ℕ => (d : ℝ)⁻¹)
    (fun d _ => by positivity) h1
  simpa using this

private theorem divisor_inverse_sum_le (n : ℕ) :
    ∑ d ∈ n.divisors, (d : ℝ)⁻¹ ≤ 1 + Real.log n := by
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdn hnpos, Nat.le_of_dvd hnpos hdn⟩
  calc ∑ d ∈ n.divisors, (d : ℝ)⁻¹ ≤ ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (harmonic n : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

private theorem inv_rpow_eq_exp {n : ℕ} (hn : 1 ≤ n) (q : ℝ) :
    ((n : ℝ) ^ q)⁻¹ = Real.exp (-(q * Real.log n)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hpos, Real.exp_neg, mul_comm]

private theorem weight_lower {lambda beta : ℝ} (hbeta : 0 ≤ beta) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ (beta * lambda))⁻¹ ≤
      Real.exp (beta * goldenResourceObjective lambda n) := by
  rw [inv_rpow_eq_exp hn]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (∑ d ∈ n.divisors, (d : ℝ)⁻¹) :=
    Real.log_nonneg (one_le_divisor_inverse_sum hn)
  unfold goldenResourceObjective
  nlinarith [mul_nonneg hbeta hlog]

private theorem weight_upper {lambda beta : ℝ} (hbeta : 0 < beta)
    (hconv : 1 < beta * lambda) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (beta * goldenResourceObjective lambda n) ≤
      Real.exp (beta * Real.log (1 + (2 * beta / (beta * lambda - 1)))) *
        ((n : ℝ) ^ ((beta * lambda + 1) / 2))⁻¹ := by
  set ε : ℝ := (beta * lambda - 1) / (2 * beta) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have hεinv : ε⁻¹ = 2 * beta / (beta * lambda - 1) := by rw [hε, inv_div]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hpow : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hεpos.le
  have hlogle : Real.log n ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div hnpos.le hεpos
  set S : ℝ := ∑ d ∈ n.divisors, (d : ℝ)⁻¹ with hS
  have hS1 : 1 ≤ S := one_le_divisor_inverse_sum hn
  have hSle : S ≤ (1 + ε⁻¹) * (n : ℝ) ^ ε := by
    have h1 := divisor_inverse_sum_le n
    have h2 : (n : ℝ) ^ ε / ε = ε⁻¹ * (n : ℝ) ^ ε := by rw [div_eq_inv_mul]
    have h3 : 0 ≤ ε⁻¹ := (inv_pos.mpr hεpos).le
    nlinarith
  have hK : 0 < 1 + ε⁻¹ := by positivity
  have hlogS : Real.log S ≤ Real.log (1 + ε⁻¹) + ε * Real.log n := by
    have hrpos : 0 < (n : ℝ) ^ ε := by positivity
    calc Real.log S ≤ Real.log ((1 + ε⁻¹) * (n : ℝ) ^ ε) :=
          Real.log_le_log (by linarith) hSle
      _ = Real.log (1 + ε⁻¹) + ε * Real.log n := by
          rw [Real.log_mul hK.ne' hrpos.ne', Real.log_rpow hnpos]
  rw [inv_rpow_eq_exp hn, ← Real.exp_add, ← hεinv]
  apply Real.exp_le_exp.mpr
  unfold goldenResourceObjective
  rw [← hS]
  have hbε : beta * ε = (beta * lambda - 1) / 2 := by
    rw [hε]; field_simp
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  nlinarith [mul_le_mul_of_nonneg_left hlogS hbeta.le]

private theorem summable_weight {lambda beta : ℝ} (hbeta : 0 < beta)
    (hconv : 1 < beta * lambda) :
    Summable (fun n : ℕ => Real.exp (beta * goldenResourceObjective lambda (n + 1))) := by
  have hq : 1 < (beta * lambda + 1) / 2 := by linarith
  have hbase : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((beta * lambda + 1) / 2))⁻¹) :=
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ ((beta * lambda + 1) / 2))⁻¹) 1).mpr
      (Real.summable_nat_rpow_inv.mpr hq)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    (hbase.mul_left (Real.exp (beta * Real.log (1 + (2 * beta / (beta * lambda - 1))))))
  exact weight_upper hbeta hconv (by omega)

/-- For `β > 0` the Boltzmann weights are summable exactly when `β λ > 1`. -/
theorem boltzmann_summable_iff {lambda beta : ℝ} (hbeta : 0 < beta) :
    Summable (fun n : ℕ => Real.exp (beta * goldenResourceObjective lambda (n + 1))) ↔
      1 < beta * lambda := by
  constructor
  · intro hs
    have hlow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (beta * lambda))⁻¹) :=
      Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => weight_lower hbeta.le (by omega)) hs
    exact Real.summable_nat_rpow_inv.mp
      ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (beta * lambda))⁻¹) 1).mp hlow)
  · exact summable_weight hbeta

private theorem objective_one (lambda : ℝ) : goldenResourceObjective lambda 1 = 0 := by
  simp [goldenResourceObjective]

private theorem local_zero (lambda : ℝ) (p : ℕ) : goldenPrimeLocalObjective lambda p 0 = 0 := by
  unfold goldenPrimeLocalObjective
  rcases eq_or_ne (1 - (p : ℝ)⁻¹) 0 with h | h
  · simp [h]
  · simp [div_self h]

private theorem objective_mul_of_coprime (lambda : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : Nat.Coprime m n) :
    goldenResourceObjective lambda (m * n) =
      goldenResourceObjective lambda m + goldenResourceObjective lambda n := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
  rw [golden_resource_objective_factorization lambda (Nat.one_le_iff_ne_zero.mpr hmn0),
    golden_resource_objective_sum_on lambda hm (m * n).primeFactors
      (Nat.primeFactors_mono (dvd_mul_right m n) hmn0),
    golden_resource_objective_sum_on lambda hn (m * n).primeFactors
      (Nat.primeFactors_mono (dvd_mul_left n m) hmn0),
    ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Nat.factorization_mul hm0 hn0, Finsupp.add_apply]
  rcases Nat.eq_zero_or_pos (m.factorization p) with h | h
  · rw [h, zero_add, local_zero, zero_add]
  · have hpn : n.factorization p = 0 := by
      by_contra hne
      have hpm : p ∣ m := Nat.dvd_of_factorization_pos h.ne'
      have hpn' : p ∣ n := Nat.dvd_of_factorization_pos hne
      have hp1 : p ∣ 1 := by
        have := Nat.dvd_gcd hpm hpn'
        rwa [hmn.gcd_eq_one] at this
      exact hprime.ne_one (Nat.dvd_one.mp hp1)
    rw [hpn, add_zero, local_zero, add_zero]

private theorem objective_prime_pow (lambda : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    goldenResourceObjective lambda (p ^ e) = goldenPrimeLocalObjective lambda p e := by
  have hsub : (p ^ e).primeFactors ⊆ {p} := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ p := hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq)
    exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqdvd)
  rw [golden_resource_objective_sum_on lambda (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero e hp.ne_zero)) {p} hsub, Finset.sum_singleton, Nat.factorization_pow,
    Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]

/-- For `β > 0` and `β λ > 1` the Boltzmann sum is the Euler product of the local
prime-power partition functions. -/
theorem boltzmann_sum_euler_product {lambda beta : ℝ} (hbeta : 0 < beta)
    (hconv : 1 < beta * lambda) :
    boltzmannSum lambda beta =
      ∏' p : Nat.Primes, ∑' e : ℕ,
        Real.exp (beta * goldenPrimeLocalObjective lambda p e) := by
  classical
  let f : ℕ → ℝ := fun n =>
    if n = 0 then 0 else Real.exp (beta * goldenResourceObjective lambda n)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, objective_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [f]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f]
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
    simp only [f, if_neg hmn0, if_neg hm.ne', if_neg hn.ne']
    rw [objective_mul_of_coprime lambda hm hn hmn, mul_add, Real.exp_add]
  have hshift : Summable (fun n => f (n + 1)) := by
    simpa [f] using summable_weight hbeta hconv
  have hsum : Summable f := (summable_nat_add_iff 1).mp hshift
  have hnorm : Summable (fun n => ‖f n‖) := by
    simpa [Real.norm_eq_abs] using hsum.abs
  have heuler := EulerProduct.eulerProduct_tprod hf1 hmul hnorm hf0
  rw [hsum.tsum_eq_zero_add, hf0, zero_add] at heuler
  have hR : ∑' n : ℕ, f (n + 1) = boltzmannSum lambda beta := by
    unfold boltzmannSum
    congr 1
  have hL : ∀ p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e) =
      ∑' e : ℕ, Real.exp (beta * goldenPrimeLocalObjective lambda p e) := by
    intro p
    congr 1
    funext e
    simp only [f, if_neg (pow_ne_zero e p.prop.ne_zero), objective_prime_pow lambda p.prop]
  rw [← hR, ← heuler]
  exact tprod_congr hL

/-- At every positive price, `Z(β) e^(-βV)` tends to the number of optimizers and
`log Z(β) / β` tends to the optimal value `V` as `β → ∞`. -/
theorem zero_temperature_limit {lambda : ℝ} (hlambda : 0 < lambda) :
    1 ≤ {n : ℕ | 1 ≤ n ∧ goldenResourceObjective lambda n = groundValue hlambda}.ncard ∧
      Tendsto (fun beta => boltzmannSum lambda beta *
          Real.exp (-(beta * groundValue hlambda))) atTop
        (𝓝 ({n : ℕ | 1 ≤ n ∧
          goldenResourceObjective lambda n = groundValue hlambda}.ncard : ℝ)) ∧
      Tendsto (fun beta => Real.log (boltzmannSum lambda beta) / beta) atTop
        (𝓝 (groundValue hlambda)) := by
  classical
  set V := groundValue hlambda with hVdef
  set J := goldenResourceObjective lambda with hJ
  -- The frozen optimizer attains the frozen supremum value.
  obtain ⟨n₀, hn₀, _, hopt, _⟩ := optimal_layer_count_spec hlambda
  have hgreatest : IsGreatest {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ J m = x} (J n₀) :=
    ⟨⟨n₀, hn₀, rfl⟩, by rintro x ⟨m, hm, rfl⟩; exact hopt m hm⟩
  have hJn₀ : J n₀ = V := by
    rw [← hgreatest.csSup_eq]
    exact golden_resource_supremum_eq_positive_part_sum hlambda
  have hle : ∀ m : ℕ, 1 ≤ m → J m ≤ V := fun m hm => hJn₀ ▸ hopt m hm
  -- A reference inverse temperature with summable weights.
  set β₀ : ℝ := 2 / lambda with hβ₀
  have hβ₀pos : 0 < β₀ := by positivity
  have hβ₀conv : 1 < β₀ * lambda := by
    rw [hβ₀, div_mul_cancel₀ _ hlambda.ne']; norm_num
  have hs₀ := summable_weight hβ₀pos hβ₀conv
  -- Shifted weights and their pointwise limit.
  let g : ℝ → ℕ → ℝ := fun beta n => Real.exp (beta * (J (n + 1) - V))
  let B : Set ℕ := {n | J (n + 1) = V}
  have hgsplit : ∀ beta n, g beta n =
      Real.exp (beta * J (n + 1)) * Real.exp (-(beta * V)) := by
    intro beta n
    simp only [g]
    rw [← Real.exp_add]
    ring_nf
  have hbound : Summable (g β₀) := by
    have := hs₀.mul_right (Real.exp (-(β₀ * V)))
    refine this.congr (fun n => ?_)
    rw [hgsplit]
  have hgle : ∀ n, J (n + 1) - V ≤ 0 := fun n => by linarith [hle (n + 1) (by omega)]
  have hB : B.Finite := by
    have hcof := hbound.tendsto_cofinite_zero
    have hev : ∀ᶠ n in cofinite, g β₀ n < 1 / 2 :=
      hcof.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.mp hev).subset (fun n hn => ?_)
    have hn' : J (n + 1) = V := hn
    simp only [Set.mem_ofPred_eq, g, hn', sub_self, mul_zero, Real.exp_zero, not_lt]
    norm_num
  have hpoint : ∀ n, Tendsto (fun beta => g beta n) atTop
      (𝓝 (B.indicator (fun _ => (1 : ℝ)) n)) := by
    intro n
    by_cases hn : n ∈ B
    · have hn' : J (n + 1) = V := hn
      simp only [g, hn', sub_self, mul_zero, Real.exp_zero, Set.indicator_of_mem hn]
      exact tendsto_const_nhds
    · have hneg : J (n + 1) - V < 0 := lt_of_le_of_ne (hgle n) (fun h => hn (sub_eq_zero.mp h))
      rw [Set.indicator_of_notMem hn]
      exact Real.tendsto_exp_atBot.comp
        ((tendsto_id.atTop_mul_const_of_neg' hneg).congr (fun _ => rfl))
  have hdom : ∀ᶠ beta in atTop, ∀ n, ‖g beta n‖ ≤ g β₀ n := by
    filter_upwards [eventually_ge_atTop β₀] with beta hbeta n
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hbeta (hgle n))
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  -- The limit counts the optimizers.
  set A : Set ℕ := {n : ℕ | 1 ≤ n ∧ J n = V} with hAdef
  have hAimage : A = (fun n => n + 1) '' B := by
    ext m
    constructor
    · rintro ⟨hm, hJm⟩
      refine ⟨m - 1, ?_, Nat.sub_add_cancel hm⟩
      change J (m - 1 + 1) = V
      rwa [Nat.sub_add_cancel hm]
    · rintro ⟨n, hn, rfl⟩
      exact ⟨Nat.le_add_left 1 n, hn⟩
  have hcard : A.ncard = B.ncard := by
    rw [hAimage, Set.ncard_image_of_injective _ (add_left_injective 1)]
  have hindsum : ∑' n, B.indicator (fun _ => (1 : ℝ)) n = (A.ncard : ℝ) := by
    rw [tsum_eq_sum (s := hB.toFinset) (fun n hn => by
      rw [Set.Finite.mem_toFinset] at hn
      exact Set.indicator_of_notMem hn _)]
    rw [Finset.sum_congr rfl (fun n hn => Set.indicator_of_mem
      ((Set.Finite.mem_toFinset hB).mp hn) _), Finset.sum_const, nsmul_eq_mul, mul_one,
      hcard, Set.ncard_eq_toFinset_card B hB]
  have hlimZ : Tendsto (fun beta => boltzmannSum lambda beta * Real.exp (-(beta * V)))
      atTop (𝓝 (A.ncard : ℝ)) := by
    rw [← hindsum]
    refine hlim.congr (fun beta => ?_)
    unfold boltzmannSum
    rw [← tsum_mul_right]
    exact tsum_congr (fun n => hgsplit beta n)
  have hApos : 1 ≤ A.ncard := by
    have hfin : A.Finite := by rw [hAimage]; exact hB.image _
    exact Nat.one_le_iff_ne_zero.mpr
      ((Set.ncard_pos hfin).mpr ⟨n₀, hn₀, hJn₀⟩).ne'
  refine ⟨hApos, hlimZ, ?_⟩
  -- Logarithms: `log Z - β V → log #A`, so `log Z / β → V`.
  have hAR : (A.ncard : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ A.ncard := by exact_mod_cast hApos
    linarith
  have hloglim := hlimZ.log hAR
  have hevpos : ∀ᶠ beta in atTop, 0 < boltzmannSum lambda beta * Real.exp (-(beta * V)) :=
    hlimZ.eventually (lt_mem_nhds (by exact_mod_cast hApos))
  have hratio : Tendsto (fun beta =>
      Real.log (boltzmannSum lambda beta * Real.exp (-(beta * V))) / beta) atTop (𝓝 0) :=
    hloglim.div_atTop tendsto_id
  have hsum : Tendsto (fun beta => V +
      Real.log (boltzmannSum lambda beta * Real.exp (-(beta * V))) / beta) atTop (𝓝 V) := by
    simpa using hratio.const_add V
  refine hsum.congr' ?_
  filter_upwards [hevpos, eventually_gt_atTop 0] with beta hpos hbeta
  have hZpos : 0 < boltzmannSum lambda beta :=
    pos_of_mul_pos_left hpos (Real.exp_pos _).le
  rw [Real.log_mul hZpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

end

#print axioms boltzmann_summable_iff
#print axioms boltzmann_sum_euler_product
#print axioms zero_temperature_limit

end D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
