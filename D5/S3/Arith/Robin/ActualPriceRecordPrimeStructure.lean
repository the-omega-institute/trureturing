/- GID: D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualPriceRecordPrimeStructure
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Positive-price predecessor records have same-integer prime structure and localization. -/

import D5.S3.Arith.ExponentExchange.PrefixNormalForm
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! All positive predecessors, including one and two, occur in the record premise.
The strict inventory is used as a divisible envelope, with its own full counts.
Localization is in log-size; no crossing-height or RH assertion is made. -/

noncomputable section
namespace D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure

open Finset Filter
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.ExponentExchange.PrefixNormalForm
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.EulerLayerInventoryGrowth
open scoped Topology Chebyshev

private theorem price_record_antitone {m : ℕ} (hm : 0 < m) {lam : ℝ}
    (hlam : 0 < lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m) :
    ∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p := by
  obtain ⟨a, ha, ham, _, hanti, hratio⟩ := exists_antitone_exponent_form (by omega : 1 ≤ m)
  have heq : a = m := by
    by_contra hne
    have halt : a < m := lt_of_le_of_ne ham hne
    have hrec := hrecord a (by omega) halt
    rw [golden_resource_sigma_identity lam ha,
      golden_resource_sigma_identity lam (by omega : 1 ≤ m)] at hrec
    have hpos : 0 < (ArithmeticFunction.sigma 1 m : ℝ) / m :=
      div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm.ne')
        (by exact_mod_cast hm)
    have hlog := Real.log_le_log hpos hratio
    have hsize : Real.log (a : ℝ) < Real.log (m : ℝ) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast halt)
    nlinarith [mul_pos hlam (sub_pos.mpr hsize)]
  simpa only [heq] using hanti

private theorem support_of_antitone {m : ℕ} (hm : 2 ≤ m)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      m.factorization q ≤ m.factorization p) :
    m.primeFactors = Nat.primesLE (largestPrime m) := by
  classical
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup m.primeFactors hne id
  have hP : largestPrime m ∈ m.primeFactors := by
    have heq : largestPrime m = v := hvu
    exact heq.symm ▸ hv
  ext p
  constructor
  · intro hp
    exact Nat.mem_primesLE.mpr ⟨le_sup (f := id) hp, Nat.prime_of_mem_primeFactors hp⟩
  · intro hp
    obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
    by_cases heq : p = largestPrime m
    · simpa only [heq] using hP
    have hPl : 1 ≤ m.factorization (largestPrime m) :=
      (Nat.prime_of_mem_primeFactors hP).factorization_pos_of_dvd (by omega)
        (Nat.dvd_of_mem_primeFactors hP)
    have hval := hPl.trans (hanti p (largestPrime m) hprime
      (Nat.prime_of_mem_primeFactors hP) (lt_of_le_of_ne hpP heq))
    exact hprime.mem_primeFactors
      ((hprime.dvd_iff_one_le_factorization (by omega)).mpr hval) (by omega)

/-- Every positive-price predecessor record has antitone valuations, including
zero valuations, and initial prime support for this same integer. -/
theorem price_record_prime_structure {m : ℕ} (hm : 2 ≤ m) {lam : ℝ}
    (hlam : 0 < lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m) :
    (∀ p q : ℕ, p.Prime → q.Prime → p < q →
      m.factorization q ≤ m.factorization p) ∧
    m.primeFactors = Nat.primesLE (largestPrime m) := by
  have hanti := price_record_antitone (by omega : 0 < m) hlam hrecord
  exact ⟨hanti, support_of_antitone hm hanti⟩

/-- A strict record at a positive price divides the existing canonical strict
integer at that price. Zero and nonprime coordinates impose no extra premise. -/
theorem price_record_divides_strictInteger {m : ℕ} (hm : 0 < m) {lam : ℝ}
    (hlam : 0 < lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m) :
    m ∣ strictInteger lam := by
  have hlast (p : ℕ) (hp : p.Prime) (ha : 1 ≤ m.factorization p) :
      lam < goldenLayerMarginal p (m.factorization p) := by
    have hd : p ∣ m := (hp.dvd_iff_one_le_factorization hm.ne').mpr ha
    have hn : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hd) hp.pos
    have hproper : m / p < m := Nat.div_lt_self hm hp.one_lt
    have heq : m / p * p = m := Nat.div_mul_cancel hd
    have hfac : (m / p).factorization p + 1 = m.factorization p := by
      have h := congrArg (fun n : ℕ => n.factorization p) heq
      simpa [Nat.factorization_mul hn.ne' hp.ne_zero, hp.factorization] using h
    have hdelta := golden_resource_objective_single_layer_delta lam (by omega : 1 ≤ m / p) hp
    rw [heq, hfac] at hdelta
    have hrec := sub_pos.mpr (hrecord (m / p) hn hproper)
    rw [hdelta] at hrec
    exact sub_pos.mp ((mul_pos_iff_of_pos_right
      (Real.log_pos (by exact_mod_cast hp.one_lt))).mp hrec)
  apply (Nat.factorization_le_iff_dvd hm.ne'
    (by have := strictInteger_pos hlam; omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : m.factorization p = 0
    · rw [hz]; exact Nat.zero_le _
    · have ha : 1 ≤ m.factorization p := by omega
      exact (strict_layer_iff hlam hp ha).mpr (hlast p hp ha)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private theorem price_record_clock_confinement {m : ℕ} (hm : 0 < m) {lam t : ℝ}
    (hlam : 0 < lam) (ht : 2 ≤ t) (hprice : 1 / (t * Real.log t) ≤ lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m) :
    m ∣ strictInteger (1 / (t * Real.log t)) ∧
    (∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) ≤
      2 * θ (Real.sqrt (2 * t)) + 2 * (ψ t - θ t) ∧
    (∀ p k : ℕ, p.Prime → 1 ≤ k → k ≤ m.factorization p →
      (p : ℝ) ^ k < (k : ℝ) * t) := by
  have hqt : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos (by linarith)))
  have hd := (price_record_divides_strictInteger hm hlam hrecord).trans
    (strictInteger_dvd hlam hqt hprice)
  have hU : 0 < strictInteger (1 / (t * Real.log t)) := by
    have := strictInteger_pos hqt; omega
  have hcounts := fun p (_ : p.Prime) => strictInteger_counts hqt p
  refine ⟨hd, (higher_layer_mass_mono hm hU hd).trans
    (strict_inventory_higher_layer_bound ht hU hcounts), ?_⟩
  intro p k hp hk hkm
  have hval := (Nat.factorization_le_iff_dvd hm.ne' hU.ne').mpr hd
  exact active_power_linear_cutoff ht hcounts hp hk (hkm.trans (hval p))

/-- One absolute constant controls the same record integer's entire higher mass.
Its prime support is initial, and all occupied powers have a linear clock cutoff. -/
theorem price_record_prime_confinement :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 3 ≤ m →
      let X := Real.log (m : ℝ)
      let lam0 := 1 / (40 * X * Real.log X)
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lam0 n < goldenResourceObjective lam0 m) →
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        m.factorization q ≤ m.factorization p) ∧
      m.primeFactors = Nat.primesLE (largestPrime m) ∧
      X = θ (largestPrime m) +
        (∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) ∧
      (0 ≤ ∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) ∧
      (∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) ≤
        2 * θ (Real.sqrt (80 * X)) + 2 * (ψ (40 * X) - θ (40 * X)) ∧
      2 * θ (Real.sqrt (80 * X)) + 2 * (ψ (40 * X) - θ (40 * X)) ≤ K * Real.sqrt X ∧
      X - K * Real.sqrt X ≤ θ (largestPrime m) ∧ θ (largestPrime m) ≤ X ∧
      m ∣ strictInteger (1 / (40 * X * Real.log (40 * X))) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k → k ≤ m.factorization p →
        (p : ℝ) ^ k < 40 * (k : ℝ) * X) := by
  obtain ⟨c, hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := Real.sqrt 40 * (4 * Real.log 4 + 2 * |c|)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro m hm
  dsimp only
  let X := Real.log (m : ℝ)
  have hm0 : 0 < m := by omega
  have hX : 1 < X := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by exact_mod_cast hm : (3 : ℝ) ≤ m)
    dsimp [X]
    linarith [Real.log_three_gt_d9]
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlam : 0 < 1 / (40 * X * Real.log X) := by positivity
  intro hrecord
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure (by omega : 2 ≤ m) hlam hrecord
  have hsplit : X = θ (largestPrime m) +
      ∑ p ∈ m.primeFactors, ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, ← hsupport]
    exact log_factorization_split hm0
  have hnonneg : 0 ≤ ∑ p ∈ m.primeFactors,
      ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p :=
    sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
  have hclock : 2 ≤ 40 * X := by linarith
  have hqt : 1 / (40 * X * Real.log (40 * X)) < 1 / (40 * X * Real.log X) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact mul_lt_mul_of_pos_left (Real.log_lt_log hX0 (by linarith)) (by positivity)
  obtain ⟨hdvd, hmass, hcut⟩ := price_record_clock_confinement hm0 hlam hclock hqt.le hrecord
  have hmass' : (∑ p ∈ m.primeFactors,
      ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p) ≤
      2 * θ (Real.sqrt (80 * X)) + 2 * (ψ (40 * X) - θ (40 * X)) := by
    simpa only [show (2 : ℝ) * (40 * X) = 80 * X by ring] using hmass
  have htail : ψ (40 * X) - θ (40 * X) ≤ |c| * Real.sqrt (40 * X) :=
    (hc _).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (Real.sqrt_nonneg _))
  have hroot : Real.sqrt (80 * X) ≤ 2 * Real.sqrt (40 * X) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt (show 0 ≤ 40 * X by positivity)]
  have htheta : θ (Real.sqrt (80 * X)) ≤
      2 * Real.log 4 * Real.sqrt (40 * X) := calc
    _ ≤ Real.log 4 * Real.sqrt (80 * X) :=
      Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg _)
    _ ≤ Real.log 4 * (2 * Real.sqrt (40 * X)) :=
      mul_le_mul_of_nonneg_left hroot hlog4.le
    _ = _ := by ring
  have hbound : 2 * θ (Real.sqrt (80 * X)) +
      2 * (ψ (40 * X) - θ (40 * X)) ≤ K * Real.sqrt X := by
    have heq : K * Real.sqrt X =
        (4 * Real.log 4 + 2 * |c|) * Real.sqrt (40 * X) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 40)]
      dsimp [K]
      ring
    rw [heq]
    nlinarith
  refine ⟨hanti, hsupport, hsplit, hnonneg, hmass', hbound, ?_, ?_, hdvd, ?_⟩
  · linarith
  · linarith
  · intro p k hp hk hkm
    simpa only [show (k : ℝ) * (40 * X) = 40 * (k : ℝ) * X by ring] using
      hcut p k hp hk hkm

/-- For each tolerance one log-size threshold works for every integer with the
same full positive-price predecessor record. Only the higher mass has a specified
square-root error; the prime-number contribution is qualitative. -/
theorem price_record_largest_prime_localization :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ, 0 < A ∧
      ∀ m : ℕ, 3 ≤ m → A ≤ Real.log (m : ℝ) →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective (1 / (40 * Real.log m * Real.log (Real.log m))) n <
          goldenResourceObjective (1 / (40 * Real.log m * Real.log (Real.log m))) m) →
      |(largestPrime m : ℝ) / Real.log m - 1| < epsilon := by
  obtain ⟨K, hK, hfinite⟩ := price_record_prime_confinement
  intro epsilon hepsilon
  let d := min (epsilon / 8) (1 / 8)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hde : d ≤ epsilon / 8 := min_le_left _ _
  have hd8 : d ≤ 1 / 8 := min_le_right _ _
  have htheta := EulerLayerRootCorrection.prime_number_limits.2
  obtain ⟨Y, hY⟩ := (eventually_atTop.1
    (htheta.eventually (Metric.ball_mem_nhds (1 : ℝ) hd)))
  have herr : Tendsto (fun x : ℝ => K / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  obtain ⟨Z, hZ⟩ := (eventually_atTop.1 (herr.eventually (eventually_lt_nhds hd)))
  let A := max 1 (max (4 * K ^ 2) (max (2 * Real.log 4 * max Y 1) Z))
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨A, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm hAm hrecord
  let X := Real.log (m : ℝ)
  let P := (largestPrime m : ℝ)
  have hX : 0 < X := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hAm
  have hAK : 4 * K ^ 2 ≤ X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hAm
  have hAY : 2 * Real.log 4 * max Y 1 ≤ X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hAm
  have hAZ : Z ≤ X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hAm
  obtain ⟨_, hsupport, hsplit, hnonneg, hmass, hbound, hlower, hupper, _, _⟩ :=
    hfinite m hm hrecord
  have hroot : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX.le
  have hhalf : K * Real.sqrt X ≤ X / 2 := by
    have hks : 2 * K ≤ Real.sqrt X := by nlinarith
    nlinarith [mul_nonneg hroot (sub_nonneg.mpr hks)]
  have hcheb : θ P ≤ Real.log 4 * P :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  have hPlower : X / 2 ≤ Real.log 4 * P := by
    change X - K * Real.sqrt X ≤ θ P at hlower
    linarith
  have hPY : max Y 1 ≤ P := by nlinarith
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) ((le_max_right Y 1).trans hPY)
  have hrel := hY P ((le_max_left Y 1).trans hPY)
  rw [Real.dist_eq] at hrel
  have hrelLo := (abs_lt.mp hrel).1
  have hrelHi := (abs_lt.mp hrel).2
  have hthetaLo : (1 - d) * P < θ P := by
    have hh := (lt_div_iff₀ hP).mp (show 1 - d < θ P / P by linarith)
    nlinarith
  have hthetaHi : θ P < (1 + d) * P := by
    have hh := (div_lt_iff₀ hP).mp (show θ P / P < 1 + d by linarith)
    nlinarith
  have hPupper : P ≤ 2 * X := by
    change θ P ≤ X at hupper
    nlinarith [mul_nonneg hP.le (show 0 ≤ 1 / 2 - d by linarith)]
  have hsmall : K * Real.sqrt X < d * X := by
    have hh := (div_lt_iff₀ (Real.sqrt_pos.mpr hX)).mp (hZ X hAZ)
    nlinarith [mul_pos (Real.sqrt_pos.mpr hX)
      (sub_pos.mpr hh)]
  have hQsmall := hmass.trans hbound
  change X = θ P + _ at hsplit
  have hdP : d * P ≤ 2 * d * X := by
    nlinarith only [mul_le_mul_of_nonneg_left hPupper hd.le]
  have hQlt := hQsmall.trans_lt hsmall
  have hminus : X - P < 3 * d * X := by
    nlinarith only [hsplit, hQlt, hthetaHi, hdP]
  have hplus : P - X < 2 * d * X := by
    nlinarith only [hsplit, hnonneg, hthetaLo, hdP]
  have heX := mul_le_mul_of_nonneg_right hde hX.le
  have hdX := mul_pos hd hX
  have hlarge : 3 * d * X < epsilon * X := by nlinarith only [heX, hdX]
  apply abs_lt.mpr
  constructor
  · have hh : (1 - epsilon) * X < P := by nlinarith only [hminus, hlarge]
    have hr := (lt_div_iff₀ hX).mpr hh
    change -epsilon < P / X - 1
    linarith only [hr]
  · have hh : P < (1 + epsilon) * X := by nlinarith only [hplus, hlarge, hdX]
    have hr := (div_lt_iff₀ hX).mpr hh
    change P / X - 1 < epsilon
    linarith only [hr]

private theorem finite_theta_abel_upper {y z rho : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (hrho : 0 ≤ rho)
    (htheta : ∀ t ∈ Set.Icc y z,
      (1 - rho) * t ≤ θ t ∧ θ t ≤ (1 + rho) * t) :
    (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
      (1 + 3 * rho) / (y * Real.log y) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  let f : ℝ → ℝ := fun t => 1 / t ^ 2
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := hy0.trans_le hyz
  have hc (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) = θ t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hd (t : ℝ) (ht : t ∈ Set.Icc y z) :
      HasDerivAt f (-2 / t ^ 3) t := by
    have ht0 : t ≠ 0 := (hy0.trans_le ht.1).ne'
    convert (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht0) using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hcont : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc y z) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne')
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y z) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c hy0.le hyz
    (fun t ht => (hd t ht).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le hyz] at habel
  have hprod : MeasureTheory.IntegrableOn (fun t => deriv f t * θ t) (Set.Icc y z) := by
    simpa only [hc] using integrableOn_mul_sum_Icc c hy0.le hi (m := 0)
  have hlowcont : ContinuousOn (fun t : ℝ => -2 * (1 + rho) / t ^ 2)
      (Set.Icc y z) := continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero _ (hy0.trans_le ht.1).ne')
  have hlowint := hlowcont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hyz
  have hint := intervalIntegral.integral_mono_on hyz hlowint
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr hprod) (fun t ht => by
      rw [(hd t ht).deriv]
      have ht0 : 0 < t := hy0.trans_le ht.1
      have hh := mul_le_mul_of_nonpos_left (htheta t ht).2
        (show -2 / t ^ 3 ≤ 0 by positivity)
      convert hh using 1 <;> field_simp <;> ring)
  have hFTC : (∫ t in y..z, -2 * (1 + rho) / t ^ 2) =
      2 * (1 + rho) / z - 2 * (1 + rho) / y := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hlowint
    intro t ht
    rw [Set.uIcc_of_le hyz] at ht
    have ht0 : t ≠ 0 := (hy0.trans_le ht.1).ne'
    convert (hasDerivAt_const t (2 * (1 + rho))).div (hasDerivAt_id t) ht0
      using 1 <;> simp <;> ring
  rw [hFTC] at hint
  have htop : f z * θ z ≤ (1 + rho) / z := by
    have hh := mul_le_mul_of_nonneg_left (htheta z ⟨hyz, le_rfl⟩).2
      (show 0 ≤ f z by dsimp [f]; positivity)
    convert hh using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hbot : (1 - rho) / y ≤ f y * θ y := by
    have hh := mul_le_mul_of_nonneg_left (htheta y ⟨le_rfl, hyz⟩).1
      (show 0 ≤ f y by dsimp [f]; positivity)
    convert hh using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hweighted : (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime,
      Real.log p / (p : ℝ) ^ 2) ≤ (1 + 3 * rho) / y := by
    have hs : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) =
        ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2 := by
      simp only [sum_filter, c, f, mul_ite, mul_zero, one_div_mul_eq_div]
    rw [hs] at habel
    have hzterm : 0 ≤ (1 + rho) / z := by positivity
    have heq : (1 + rho) / z - (1 - rho) / y -
        (2 * (1 + rho) / z - 2 * (1 + rho) / y) =
        (1 + 3 * rho) / y - (1 + rho) / z := by ring
    linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcompare : Real.log y *
      (∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpy : y < (p : ℝ) := (Nat.floor_lt hy0.le).mp (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hlog := Real.log_le_log hy0 hpy.le
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr (sq_nonneg (p : ℝ)))
  have hh := (le_div_iff₀ hlogy).mpr (by simpa only [mul_comm] using hcompare.trans hweighted)
  simpa only [div_div] using hh

private theorem record_lower_price {m : ℕ} (hm : 0 < m) {a b : ℝ} (hab : a ≤ b)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective b n < goldenResourceObjective b m) :
    ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective a n < goldenResourceObjective a m := by
  intro n hn hnm
  have hlog := Real.log_lt_log (by exact_mod_cast hn : (0 : ℝ) < n)
    (by exact_mod_cast hnm : (n : ℝ) < m)
  have hr := hrecord n hn hnm
  rw [golden_resource_sigma_identity b (by omega : 1 ≤ n),
    golden_resource_sigma_identity b (by omega : 1 ≤ m)] at hr
  rw [golden_resource_sigma_identity a (by omega : 1 ≤ n),
    golden_resource_sigma_identity a (by omega : 1 ≤ m)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hlog.le)]

private theorem short_layer_gain_lower {m q : ℕ} (hq : q.Prime)
    (hv : m.factorization q ≤ 1) :
    (1 - 1 / (q : ℝ)) / (q : ℝ) ^ 2 ≤
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q := by
  let x := (q : ℝ)⁻¹
  let r := x ^ (m.factorization q + 1)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hx : 0 < x := inv_pos.mpr hq0
  have hx1 : x < 1 := (inv_lt_one₀ hq0).mpr (by exact_mod_cast hq.one_lt)
  have hr0 : 0 ≤ r := (pow_pos hx _).le
  have hr1 : r < 1 := pow_lt_one₀ hx.le hx1 (by omega)
  have hrx : r * x < 1 := by nlinarith
  have hden : 0 < 1 - r := by linarith
  have hnum : 0 < 1 - r * x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hnum hden)
  have hbase : r * (1 - x) ≤ 1 - ((1 - r * x) / (1 - r))⁻¹ := by
    rw [inv_div]
    have hh : (1 - r) / (1 - r * x) ≤ 1 - r * (1 - x) := by
      apply (div_le_iff₀ hnum).mpr
      nlinarith [mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hx1.le))
        (mul_nonneg hr0 hx.le)]
    linarith
  have hpow : x ^ 2 ≤ r := pow_le_pow_of_le_one hx.le hx1.le (by omega)
  have hsmall := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hx1.le)
  have heq : goldenLayerMarginal q (m.factorization q + 1) * Real.log q =
      Real.log ((1 - r * x) / (1 - r)) := by
    unfold goldenLayerMarginal
    rw [div_mul_cancel₀ _ hq.log_pos.ne', pow_succ]
  rw [heq]
  have hh := hsmall.trans (hbase.trans hlog)
  convert hh using 1 <;> dsimp [x] <;> field_simp <;> ring

private theorem actual_layer_tail_le {m q : ℕ} (hq : q.Prime) {k : ℕ}
    (hk : 1 ≤ k) (hkv : k ≤ m.factorization q + 1) :
    OriginalEndpointPrimeTail.layerTail m q ≤
      (q : ℝ)⁻¹ ^ k / (1 - (q : ℝ)⁻¹ ^ k) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hx : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hq0
  have hx1 : (q : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hq0).mpr (by exact_mod_cast hq.one_lt)
  have hrk : (q : ℝ)⁻¹ ^ (m.factorization q + 1) ≤ (q : ℝ)⁻¹ ^ k :=
    pow_le_pow_of_le_one hx.le hx1.le hkv
  have hkl : (q : ℝ)⁻¹ ^ k < 1 := pow_lt_one₀ hx.le hx1 (by omega)
  have hr : 0 < 1 - (q : ℝ)⁻¹ ^ (m.factorization q + 1) := by linarith
  have hlog : -Real.log (1 - (q : ℝ)⁻¹ ^ k) ≤
      (q : ℝ)⁻¹ ^ k / (1 - (q : ℝ)⁻¹ ^ k) := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hkl))
    rw [Real.log_inv] at hh
    convert hh using 1 <;> field_simp <;> ring
  exact (neg_le_neg (Real.log_le_log (sub_pos.mpr hkl) (by linarith))).trans hlog

private theorem medium_valuation {m P q : ℕ} {lam alpha kappa u y : ℝ}
    (hm : 0 < m) (hlam : 0 < lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m)
    (hP : P.Prime) (hPm : P ∣ m) (hq : q.Prime) (hqP : q < P)
    (hu : 0 < u) (hk : 0 < kappa) (ha0 : 0 ≤ 1 - alpha / 2 + kappa)
    (ha1 : 1 - alpha / 2 + kappa ≤ 1)
    (huy : u < (q : ℝ)) (hqy : (q : ℝ) ≤ y) (hy : 0 ≤ y)
    (hyP : y ^ 2 * (1 - alpha / 2 + kappa) = (P : ℝ))
    (huk : 1 / u ≤ kappa / 4)
    (hprice : alpha / 2 - kappa / 4 ≤
      (P : ℝ) * lam * (Real.log P - Real.log q)) :
    2 ≤ m.factorization q := by
  by_contra hval
  have hlow := short_layer_gain_lower hq (by omega : m.factorization q ≤ 1)
  obtain ⟨_, _, _, _, _, hex, hlast, _⟩ :=
    ExponentExchange.PriceRecordMissingLayer.price_record_missing_layer
      hm hlam hrecord hP hPm hq hqP
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqp : (1 - alpha / 2 + kappa) * (q : ℝ) ^ 2 ≤ (P : ℝ) := by
    have hs : (q : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs ha0]
  have hInv : 1 / (q : ℝ) ≤ kappa / 4 :=
    (one_div_le_one_div_of_le hu huy.le).trans huk
  have hscale : 1 - alpha / 2 + 3 * kappa / 4 ≤
      (P : ℝ) * ((1 - 1 / (q : ℝ)) / (q : ℝ) ^ 2) := by
    have hdiff : 0 ≤ 1 - 1 / (q : ℝ) := by
      have hh := one_div_lt_one_of_one_lt₀ hq1
      linarith
    have hh := mul_le_mul_of_nonneg_right hqp hdiff
    have hsmall : (1 - alpha / 2 + kappa) * (1 / (q : ℝ)) ≤ kappa / 4 := by
      nlinarith [mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 1 / (q : ℝ))]
    have hh' : (1 - alpha / 2 + 3 * kappa / 4) * (q : ℝ) ^ 2 ≤
        (P : ℝ) * (1 - 1 / (q : ℝ)) := by
      have hz := mul_nonneg (sq_nonneg (q : ℝ))
        (show 0 ≤ (1 - alpha / 2 + kappa) * (1 - 1 / (q : ℝ)) -
          (1 - alpha / 2 + 3 * kappa / 4) by nlinarith)
      nlinarith
    simpa only [mul_div_assoc] using (le_div_iff₀ (sq_pos_of_pos hq0)).mpr hh'
  have hg := mul_le_mul_of_nonneg_left hlow hP0.le
  have he := mul_lt_mul_of_pos_left (hex.trans_le hlast) hP0
  have hcancel : (P : ℝ) * (1 / (P : ℝ)) = 1 := by field_simp
  rw [hcancel] at he
  nlinarith only [hg, he, hscale, hprice, hk]

private theorem finite_cubic_tail {u : ℝ} (hu : 0 < u) (S : Finset ℕ)
    (hS : ∀ p ∈ S, u < (p : ℝ)) :
    (∑ p ∈ S, 1 / (p : ℝ) ^ 3) ≤ 2 / u ^ 2 := by
  classical
  let K := ⌊u⌋₊ + 1
  have hK1 : 1 ≤ K := by dsimp [K]; omega
  have huK : u ≤ (K : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one u).le
  have hKp (p : ℕ) (hp : p ∈ S) : K ≤ p := by
    have := (Nat.floor_lt hu.le).mpr (hS p hp)
    dsimp [K]; omega
  have hshift : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) =
      ∑ k ∈ S.image (fun p => p - K), 1 / ((k + K : ℕ) : ℝ) ^ 2 := by
    rw [sum_image (by
      intro p hp q hq heq
      have := hKp p hp
      have := hKp q hq
      change p - K = q - K at heq
      omega)]
    apply sum_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (hKp p hp)]
  have hsum : Summable (fun k : ℕ => 1 / ((k + K : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add] using
      (summable_nat_add_iff K).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hsquare : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤ 2 / u := by
    rw [hshift]
    calc
      _ ≤ ∑' k : ℕ, 1 / ((k + K : ℕ) : ℝ) ^ 2 :=
        hsum.sum_le_tsum _ (by intro k hk; positivity)
      _ ≤ 2 / (K : ℝ) := by
        simpa only [Nat.cast_add] using
          (Mertens.sum_one_div_sq_le (N := (K : ℝ)) (by exact_mod_cast hK1))
      _ ≤ 2 / u := div_le_div_of_nonneg_left (by norm_num) hu huK
  calc
    _ ≤ (1 / u) * ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hp0 : 0 < (p : ℝ) := hu.trans (hS p hp)
      have hh := mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le hu (hS p hp).le)
        (show 0 ≤ 1 / (p : ℝ) ^ 2 by positivity)
      convert hh using 1 <;> field_simp <;> ring
    _ ≤ (1 / u) * (2 / u) := mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 2 / u ^ 2 := by ring

private theorem actual_tail_finite {m : ℕ} {lam alpha kappa rho u y : ℝ}
    (hm : 3 ≤ m) (hlam : 0 < lam)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lam n < goldenResourceObjective lam m)
    (hk : 0 < kappa) (ha0 : 0 < 1 - alpha / 2 + kappa)
    (ha1 : 1 - alpha / 2 + kappa ≤ 1)
    (hu : 2 ≤ u) (huP : u ^ 3 = (largestPrime m : ℝ))
    (huy : u ≤ y) (hyP : y ^ 2 * (1 - alpha / 2 + kappa) = (largestPrime m : ℝ))
    (hylt : y < (largestPrime m : ℝ))
    (hyroot : Real.sqrt (largestPrime m : ℝ) ≤ y)
    (huk : 1 / u ≤ kappa / 4) (hrho : 0 ≤ rho)
    (htheta : ∀ t ∈ Set.Icc y (largestPrime m : ℝ),
      (1 - rho) * t ≤ θ t ∧ θ t ≤ (1 + rho) * t)
    (hprice : ∀ q : ℕ, q.Prime → u < (q : ℝ) → (q : ℝ) ≤ y →
      alpha / 2 - kappa / 4 ≤
        (largestPrime m : ℝ) * lam * (Real.log (largestPrime m) - Real.log q)) :
    OriginalEndpointPrimeTail.tail m ≤ 6 / u ^ 2 +
      (1 + 3 * rho) / ((1 - 1 / (largestPrime m : ℝ)) * y * Real.log y) := by
  classical
  let P := largestPrime m
  let S := m.primeFactors
  let small := S.filter (fun p : ℕ => (p : ℝ) ≤ u)
  let medium := S.filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ y)
  let large := S.filter (fun p : ℕ => y < (p : ℝ))
  have hne : S.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup S hne id
  have hPS : P ∈ S := by
    have heq : P = v := hvu
    exact heq.symm ▸ hv
  have hP : P.Prime := Nat.prime_of_mem_primeFactors hPS
  have hPm : P ∣ m := Nat.dvd_of_mem_primeFactors hPS
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP.one_lt
  have hmax (p : ℕ) (hp : p ∈ S) : p ≤ P := le_sup (f := id) hp
  have hu0 : 0 < u := by linarith
  have hy : 1 < y := by linarith
  have huplt : u < (P : ℝ) := huy.trans_lt hylt
  have hcard : (small.card : ℝ) ≤ u := by
    have hsub : small ⊆ Ioc 0 ⌊u⌋₊ := by
      intro p hp
      obtain ⟨hpS, hpu⟩ := mem_filter.mp hp
      exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hpS).pos, Nat.le_floor hpu⟩
    calc
      _ ≤ ((Ioc 0 ⌊u⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (⌊u⌋₊ : ℝ) := by simp
      _ ≤ u := Nat.floor_le hu0.le
  have hsmall : (∑ p ∈ small, OriginalEndpointPrimeTail.layerTail m p) ≤ 2 / u ^ 2 := by
    have hs := sum_le_card_nsmul small (OriginalEndpointPrimeTail.layerTail m)
      (2 / (P : ℝ)) (by
        intro p hp
        obtain ⟨hpS, hpu⟩ := mem_filter.mp hp
        have hpP : p < P := by exact_mod_cast hpu.trans_lt huplt
        have hh := ExponentExchange.PriceRecordMissingLayer.price_record_missing_layer
          (by omega : 0 < m) hlam hrecord hP hPm (Nat.prime_of_mem_primeFactors hpS) hpP
        exact hh.2.2.2.2.2.2.2.2.2.2.2.le)
    rw [nsmul_eq_mul] at hs
    calc
      _ ≤ (small.card : ℝ) * (2 / (P : ℝ)) := hs
      _ ≤ u * (2 / (P : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 / u ^ 2 := by rw [← huP]; field_simp; ring
  have hmedium : (∑ p ∈ medium, OriginalEndpointPrimeTail.layerTail m p) ≤ 4 / u ^ 2 := by
    have hpoint (p : ℕ) (hp : p ∈ medium) :
        OriginalEndpointPrimeTail.layerTail m p ≤ 2 / (p : ℝ) ^ 3 := by
      obtain ⟨hpS, hup, hpy⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpS
      have hpP : p < P := by exact_mod_cast hpy.trans_lt hylt
      have hval := medium_valuation (by omega : 0 < m) hlam hrecord hP hPm hprime hpP
        hu0 hk ha0.le ha1 hup hpy (by linarith) hyP huk (hprice p hprime hup hpy)
      have hh := actual_layer_tail_le hprime (by norm_num : 1 ≤ (3 : ℕ)) (by omega)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hprime.two_le : (2 : ℝ) ≤ p)
      have hpow : (p : ℝ)⁻¹ ^ 3 ≤ 1 / 2 := by
        have hh' := pow_le_pow_of_le_one (inv_nonneg.mpr hp0.le)
          (show (p : ℝ)⁻¹ ≤ 1 by linarith) (by norm_num : 1 ≤ (3 : ℕ))
        simp only [pow_one] at hh'
        linarith
      have hb : (p : ℝ)⁻¹ ^ 3 / (1 - (p : ℝ)⁻¹ ^ 3) ≤ 2 * (p : ℝ)⁻¹ ^ 3 := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - (p : ℝ)⁻¹ ^ 3)).mpr
        nlinarith [pow_nonneg (inv_nonneg.mpr hp0.le) 3]
      simpa only [inv_pow, div_eq_mul_inv, mul_one] using hh.trans hb
    calc
      _ ≤ ∑ p ∈ medium, 2 / (p : ℝ) ^ 3 := sum_le_sum hpoint
      _ = 2 * ∑ p ∈ medium, 1 / (p : ℝ) ^ 3 := by simp only [mul_sum, mul_one_div]
      _ ≤ 2 * (2 / u ^ 2) := mul_le_mul_of_nonneg_left
        (finite_cubic_tail hu0 medium (fun p hp => (mem_filter.mp hp).2.1)) (by norm_num)
      _ = 4 / u ^ 2 := by ring
  have hden : 0 < 1 - 1 / (P : ℝ) := by
    have := one_div_lt_one_of_one_lt₀ hP1
    linarith
  have hlarge : (∑ p ∈ large, OriginalEndpointPrimeTail.layerTail m p) ≤
      (1 + 3 * rho) / ((1 - 1 / (P : ℝ)) * y * Real.log y) := by
    have hsub : large ⊆ (Ioc ⌊y⌋₊ ⌊(P : ℝ)⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpS, hyp⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith : 0 ≤ y)).mpr hyp,
        ?_⟩, Nat.prime_of_mem_primeFactors hpS⟩
      simpa only [Nat.floor_natCast] using hmax p hpS
    have hpoint (p : ℕ) (hp : p ∈ large) :
        OriginalEndpointPrimeTail.layerTail m p ≤
          (1 / (1 - 1 / (P : ℝ))) * (1 / (p : ℝ) ^ 2) := by
      obtain ⟨hpS, hyp⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpS
      have hval : 1 ≤ m.factorization p :=
        hprime.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hpS)
      have hh := actual_layer_tail_le hprime (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hsq : (P : ℝ) ≤ (p : ℝ) ^ 2 := by
        nlinarith [Real.sq_sqrt hP0.le, Real.sqrt_nonneg (P : ℝ)]
      have hinv : (p : ℝ)⁻¹ ^ 2 ≤ 1 / (P : ℝ) := by
        simpa only [one_div, inv_pow] using one_div_le_one_div_of_le hP0 hsq
      have hd := div_le_div_of_nonneg_left (pow_nonneg (inv_nonneg.mpr hp0.le) 2)
        hden (show 1 - 1 / (P : ℝ) ≤ 1 - (p : ℝ)⁻¹ ^ 2 by linarith)
      calc
        _ ≤ (p : ℝ)⁻¹ ^ 2 / (1 - (p : ℝ)⁻¹ ^ 2) := hh
        _ ≤ (p : ℝ)⁻¹ ^ 2 / (1 - 1 / (P : ℝ)) := hd
        _ = _ := by simp only [inv_pow, one_div, div_eq_mul_inv]; ring
    calc
      _ ≤ ∑ p ∈ large, (1 / (1 - 1 / (P : ℝ))) * (1 / (p : ℝ) ^ 2) := sum_le_sum hpoint
      _ = (1 / (1 - 1 / (P : ℝ))) * ∑ p ∈ large, 1 / (p : ℝ) ^ 2 := (mul_sum ..).symm
      _ ≤ (1 / (1 - 1 / (P : ℝ))) *
          ∑ p ∈ (Ioc ⌊y⌋₊ ⌊(P : ℝ)⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
          (by intro p hp hnot; positivity)) (by positivity)
      _ ≤ (1 / (1 - 1 / (P : ℝ))) * ((1 + 3 * rho) / (y * Real.log y)) :=
        mul_le_mul_of_nonneg_left (finite_theta_abel_upper hy hylt.le hrho htheta) (by positivity)
      _ = _ := by ring
  have hsplit : OriginalEndpointPrimeTail.tail m =
      (∑ p ∈ small, OriginalEndpointPrimeTail.layerTail m p) +
      (∑ p ∈ medium, OriginalEndpointPrimeTail.layerTail m p) +
      ∑ p ∈ large, OriginalEndpointPrimeTail.layerTail m p := by
    simp only [OriginalEndpointPrimeTail.tail, small, medium, large, sum_filter,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases hpu : (p : ℝ) ≤ u
    · have hpy : (p : ℝ) ≤ y := hpu.trans huy
      simp [hpu, hpy, not_lt.mpr hpu, not_lt.mpr hpy]
    · by_cases hpy : (p : ℝ) ≤ y <;> simp [hpu, hpy]
  change _ ≤ 6 / u ^ 2 + (1 + 3 * rho) / ((1 - 1 / (P : ℝ)) * y * Real.log y)
  linarith

#print axioms price_record_prime_structure
#print axioms price_record_divides_strictInteger
#print axioms price_record_prime_confinement
#print axioms price_record_largest_prime_localization

end D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
