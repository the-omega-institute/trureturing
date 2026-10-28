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
import Mathlib.Analysis.Complex.ExponentialBounds

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
    have hsize := Real.log_lt_log (by exact_mod_cast (by omega : 0 < a))
      (by exact_mod_cast halt)
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
  have hanti := price_record_antitone hm0 hlam hrecord
  have hsupport := support_of_antitone (by omega : 2 ≤ m) hanti
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
    convert hmass using 1 <;> congr 2 <;> ring
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
    convert hcut p k hp hk hkm using 1 <;> ring

#print axioms price_record_divides_strictInteger
#print axioms price_record_prime_confinement

end D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
