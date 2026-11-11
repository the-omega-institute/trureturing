/- GID: D5/S3/Arith/Robin/PriceRecord/FirstPrimePrefixLocalization
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FirstPrimePrefixLocalization
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Every fixed logarithmic scale localizes the first actual prime prefix. -/

import D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail

/- The first-layer charge consumes the common finite local-gap bound.
All prime factors and exponents are those of the original positive integer.
No record price or record hypothesis is needed in this module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization

open Finset Real Filter Asymptotics
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.PriceRecord.ActualIntegerOccupationCoercivity
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)

-- Missing first layers pay their actual marginal, even at n=1.
private lemma missing_first_loss {lam : ℝ} (hlam : 0 < lam) {p : ℕ} (hp : p.Prime) :
    log p * (goldenLayerMarginal p 1 - lam) ≤
      goldenPrimeLocalObjective lam p (optimalLayerCount lam p) -
        goldenPrimeLocalObjective lam p 0 := by
  have hm := count_maximal hlam hp 1
  have hs := golden_prime_local_objective_diff hp lam 0
  norm_num only [zero_add] at hs
  nlinarith

-- Later occupied layers cannot cancel the loss of a negative first layer.
private lemma occupied_first_loss {lam : ℝ} (hlam : 0 < lam) {p a : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hg : goldenLayerMarginal p 1 ≤ lam) :
    log p * (lam - goldenLayerMarginal p 1) ≤
      goldenPrimeLocalObjective lam p (optimalLayerCount lam p) -
        goldenPrimeLocalObjective lam p a := by
  have hdown : AntitoneOn (goldenPrimeLocalObjective lam p) (Set.Ici 1) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hk _
    change 1 ≤ k at hk
    have hmk : goldenLayerMarginal p (k + 1) ≤ lam := by
      have hlt : 1 < k + 1 := by omega
      exact (golden_layer_strict_decrease hp (by norm_num) hlt).le.trans hg
    have hs := golden_prime_local_objective_diff hp lam k
    have hlog : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmk) hlog]
  have hmax := count_maximal hlam hp 0
  have hstep := golden_prime_local_objective_diff hp lam 0
  have hcomp := hdown (by norm_num) ha ha
  norm_num only [zero_add] at hstep
  nlinarith

/-- Exact finite first-layer charge against the SAME actual pressure defect.
H contains absent primes; X contains primes occupied at least once. There is
no support cap and no bound on any later factorization exponent. -/
theorem actual_first_layer_charge {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : 1 ≤ n)
    (H X : Finset ℕ) (hdisj : Disjoint H X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : ∀ p ∈ H, p.Prime ∧ n.factorization p = 0 ∧
      ρ ≤ goldenLayerMarginal p 1 - referencePrice z)
    (hX : ∀ p ∈ X, p.Prime ∧ 1 ≤ n.factorization p ∧
      ρ ≤ referencePrice z - goldenLayerMarginal p 1) :
    ρ * ((∑ p ∈ H, log p) + ∑ p ∈ X, log p) ≤ actualDefect z n := by
  classical
  have hlam : 0 < referencePrice z :=
    one_div_pos.mpr (mul_pos (by linarith) (log_pos hz))
  let gap : ℕ → ℝ := fun p =>
    goldenPrimeLocalObjective (referencePrice z) p
        (optimalLayerCount (referencePrice z) p) -
      goldenPrimeLocalObjective (referencePrice z) p (n.factorization p)
  have hh : ∀ p ∈ H, ρ * log p ≤ gap p := by
    intro p hp
    have h := hH p hp
    have hc := missing_first_loss hlam h.1
    dsimp [gap]
    rw [h.2.1]
    nlinarith [mul_le_mul_of_nonneg_right h.2.2 (log_natCast_nonneg p)]
  have hx : ∀ p ∈ X, ρ * log p ≤ gap p := by
    intro p hp
    have h := hX p hp
    have hg : goldenLayerMarginal p 1 ≤ referencePrice z := by linarith [h.2.2]
    have hc := occupied_first_loss hlam h.1 h.2.1 hg
    dsimp [gap]
    nlinarith [mul_le_mul_of_nonneg_right h.2.2 (log_natCast_nonneg p)]
  calc
    _ = (∑ p ∈ H, ρ * log p) + ∑ p ∈ X, ρ * log p := by
      rw [← mul_sum, ← mul_sum]; ring
    _ ≤ (∑ p ∈ H, gap p) + ∑ p ∈ X, gap p :=
      add_le_add (sum_le_sum hh) (sum_le_sum hx)
    _ = ∑ p ∈ H ∪ X, gap p := (sum_union hdisj).symm
    _ ≤ actualDefect z n := by
      apply actual_local_gap_sum_le_defect hz hn
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · exact (hH p hp).1
      · exact (hX p hp).1

private lemma first_marginal_bounds {p : ℕ} (hp : p.Prime) :
    1 / (((p : ℝ) + 1) * log p) ≤ goldenLayerMarginal p 1 ∧
    goldenLayerMarginal p 1 ≤ 1 / ((p : ℝ) * log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 < log (p : ℝ) := hp.log_pos
  have heq := golden_layer_marginal_one_eq_log_one_add_inv hp
  constructor
  · have ha : 0 < 1 + 1 / (p : ℝ) := by positivity
    have hh := one_sub_inv_le_log_of_pos ha
    have hid : 1 - (1 + 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) + 1) := by
      field_simp [hp0.ne', ha.ne', (show (p : ℝ) + 1 ≠ 0 by positivity)]
      <;> ring
    rw [hid] at hh
    rw [heq, ← div_div]
    exact div_le_div_of_nonneg_right hh hlp.le
  · have hh := golden_layer_marginal_le_inv_pow hp (by norm_num : 1 ≤ 1)
    norm_num only [pow_one] at hh
    calc
      _ ≤ (p : ℝ)⁻¹ / log p := hh
      _ = _ := by field_simp [hp0.ne', hlp.ne']

-- The geometric width and the margin use different fractions of eta.
private lemma first_band_margins {z η : ℝ} (hz : 1 < z)
    (hη : 0 < η) (hηb : η ≤ 1 / 4) (hsize : 4 ≤ η * z) :
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ z * (1 - η / 2) →
      η / (4 * z * log z) ≤ goldenLayerMarginal p 1 - referencePrice z) ∧
    (∀ p : ℕ, p.Prime → z * (1 + η / 2) ≤ (p : ℝ) →
      η / (4 * z * log z) ≤ referencePrice z - goldenLayerMarginal p 1) := by
  have hz0 : 0 < z := by linarith
  have hL : 0 < log z := log_pos hz
  constructor
  · intro p hp hpb
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < log (p : ℝ) := hp.log_pos
    have hpc : (p : ℝ) + 1 ≤ z * (1 - η / 4) := by nlinarith
    have hpz : (p : ℝ) ≤ z := by nlinarith
    have hlog : log (p : ℝ) ≤ log z := log_le_log hp0 hpz
    have hcoef : 0 ≤ 1 - η / 4 := by linarith
    have hden : ((p : ℝ) + 1) * log p ≤ (1 - η / 4) * (z * log z) := by
      calc
        _ ≤ (z * (1 - η / 4)) * log z :=
          mul_le_mul hpc hlog hlp.le (mul_nonneg hz0.le hcoef)
        _ = _ := by ring
    have hcomp : (1 + η / 4) * (((p : ℝ) + 1) * log p) ≤ z * log z := by
      calc
        _ ≤ (1 + η / 4) * ((1 - η / 4) * (z * log z)) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg η) (mul_pos hz0 hL).le]
    have hb : (1 + η / 4) / (z * log z) ≤ goldenLayerMarginal p 1 := by
      apply le_trans _ (first_marginal_bounds hp).1
      exact (div_le_div_iff₀ (mul_pos hz0 hL) (by positivity)).mpr (by
        simpa only [one_mul] using hcomp)
    have heq : (1 + η / 4) / (z * log z) =
        referencePrice z + η / (4 * z * log z) := by
      unfold referencePrice
      field_simp [hz0.ne', hL.ne'] <;> ring
    rw [heq] at hb
    linarith
  · intro p hp hpa
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < log (p : ℝ) := hp.log_pos
    have hzp : z ≤ (p : ℝ) := by nlinarith
    have hlog : log z ≤ log (p : ℝ) := log_le_log hz0 hzp
    have hden : (1 + η / 2) * (z * log z) ≤ (p : ℝ) * log p := by
      calc
        _ = (z * (1 + η / 2)) * log z := by ring
        _ ≤ _ := mul_le_mul hpa hlog hL.le hp0.le
    have hc : 1 ≤ (1 - η / 4) * (1 + η / 2) := by
      nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hηb)]
    have hcomp : z * log z ≤ (1 - η / 4) * ((p : ℝ) * log p) := by
      calc
        _ ≤ ((1 - η / 4) * (1 + η / 2)) * (z * log z) :=
          le_mul_of_one_le_left (mul_pos hz0 hL).le hc
        _ = (1 - η / 4) * ((1 + η / 2) * (z * log z)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hden (by linarith)
    have hb : goldenLayerMarginal p 1 ≤ (1 - η / 4) / (z * log z) := by
      apply (first_marginal_bounds hp).2.trans
      exact (div_le_div_iff₀ (mul_pos hp0 hlp) (mul_pos hz0 hL)).mpr (by
        simpa only [one_mul] using hcomp)
    have heq : (1 - η / 4) / (z * log z) =
        referencePrice z - η / (4 * z * log z) := by
      unfold referencePrice
      field_simp [hz0.ne', hL.ne'] <;> ring
    rw [heq] at hb
    linarith

-- One finite set and its EXACT theta mass, with the literal endpoint convention.
private lemma finite_theta_band {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b) ∧
      (∑ p ∈ S, log p) = Chebyshev.theta b - Chebyshev.theta a := by
  classical
  let S := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ := by
    intro p hp
    obtain ⟨hpA, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpA.trans (Nat.floor_mono hab), hprime⟩
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpB, hpA⟩ := mem_sdiff.mp hp
    obtain ⟨hpb, hprime⟩ := Nat.mem_primesLE.mp hpB
    refine ⟨hprime, ?_, (Nat.le_floor_iff (ha.trans hab)).mp hpb⟩
    by_contra! hpa
    exact hpA (Nat.mem_primesLE.mpr ⟨Nat.le_floor hpa, hprime⟩)
  · rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
      ← sum_sdiff hsub]
    dsimp [S]
    ring

/-- A finite displacement of the first prefix pays eta^2 sqrt(z)/32.
The two PNT window masses are explicit finite inequalities here; the uniform
all-logarithmic-scale supplier below discharges them from the GLOBAL PNT. -/
theorem first_prefix_displacement_charge {z η : ℝ} (hz : 1 < z)
    (hη : 0 < η) (hηb : η ≤ 1 / 4) (hsize : 4 ≤ η * z)
    (hbelow : η * z / 8 ≤ Chebyshev.theta (z * (1 - η / 2)) -
      Chebyshev.theta (z * (1 - 3 * η / 4)))
    (habove : η * z / 8 ≤ Chebyshev.theta (z * (1 + 3 * η / 4)) -
      Chebyshev.theta (z * (1 + η / 2)))
    {n : ℕ} (hn : 1 ≤ n)
    (hsupport : n.primeFactors = Nat.primesLE (largestPrime n))
    (hfar : (largestPrime n : ℝ) ≤ z * (1 - η) ∨
      z * (1 + η) ≤ (largestPrime n : ℝ)) :
    η ^ 2 * sqrt z / 32 ≤ sqrt z * log z * actualDefect z n := by
  classical
  have hz0 : 0 < z := by linarith
  have hL : 0 < log z := log_pos hz
  have hmargin := first_band_margins hz hη hηb hsize
  have hρ : 0 ≤ η / (4 * z * log z) := by positivity
  have hscale : 0 ≤ sqrt z * log z := by positivity
  have hηz0 : 0 < η * z := mul_pos hη hz0
  have hpay : η / (4 * z * log z) * (η * z / 8) ≤ actualDefect z n := by
    rcases hfar with hfar | hfar
    · have hηz := mul_le_mul_of_nonneg_right hηb hz0.le
      obtain ⟨S, hS, hmass⟩ := finite_theta_band
        (a := z * (1 - 3 * η / 4)) (b := z * (1 - η / 2))
        (by nlinarith) (by nlinarith)
      have hH : ∀ p ∈ S, p.Prime ∧ n.factorization p = 0 ∧
          η / (4 * z * log z) ≤ goldenLayerMarginal p 1 - referencePrice z := by
        intro p hp
        obtain ⟨hprime, hpa, hpb⟩ := hS p hp
        have hPp : (largestPrime n : ℝ) < p := by nlinarith
        have hnot : ¬ p ∣ n := by
          intro hd
          have hpm := hprime.mem_primeFactors hd (by omega : n ≠ 0)
          rw [hsupport] at hpm
          have hpP : p ≤ largestPrime n := (Nat.mem_primesLE.mp hpm).1
          have : (p : ℝ) ≤ largestPrime n := by exact_mod_cast hpP
          linarith
        exact ⟨hprime, Nat.factorization_eq_zero_of_not_dvd hnot,
          hmargin.1 p hprime hpb⟩
      have hc := actual_first_layer_charge hz hn S ∅ (by simp) hρ hH (by simp)
      simp only [sum_empty, add_zero] at hc
      exact (mul_le_mul_of_nonneg_left (hbelow.trans_eq hmass.symm) hρ).trans hc
    · obtain ⟨S, hS, hmass⟩ := finite_theta_band
        (a := z * (1 + η / 2)) (b := z * (1 + 3 * η / 4))
        (by positivity) (by nlinarith)
      have hX : ∀ p ∈ S, p.Prime ∧ 1 ≤ n.factorization p ∧
          η / (4 * z * log z) ≤ referencePrice z - goldenLayerMarginal p 1 := by
        intro p hp
        obtain ⟨hprime, hpa, hpb⟩ := hS p hp
        have hpP : p ≤ largestPrime n := by
          have : (p : ℝ) ≤ largestPrime n := by nlinarith
          exact_mod_cast this
        have hpm : p ∈ n.primeFactors := by
          rw [hsupport]
          exact Nat.mem_primesLE.mpr ⟨hpP, hprime⟩
        exact ⟨hprime, hprime.factorization_pos_of_dvd (by omega : n ≠ 0)
          (Nat.dvd_of_mem_primeFactors hpm), hmargin.2 p hprime hpa.le⟩
      have hc := actual_first_layer_charge hz hn ∅ S (by simp) hρ (by simp) hX
      simp only [sum_empty, zero_add] at hc
      exact (mul_le_mul_of_nonneg_left (habove.trans_eq hmass.symm) hρ).trans hc
  have hc := mul_le_mul_of_nonneg_left hpay hscale
  have heq : (sqrt z * log z) * (η / (4 * z * log z) * (η * z / 8)) =
      η ^ 2 * sqrt z / 32 := by
    field_simp [hz0.ne', hL.ne'] <;> ring
  rwa [heq] at hc

-- Uniformity in y is essential: the endpoint may move with z.
private lemma uniform_theta_error {T z : ℝ} (hz : 1 < z)
    (hL : 2 * log 2 ≤ log z) (hT : T ≤ z / 2) (N : ℕ)
    (hθ : ∀ y : ℝ, T ≤ y → |Chebyshev.theta y - y| ≤ y / log y ^ N)
    {y : ℝ} (hylo : z / 2 ≤ y) (hyhi : y ≤ 2 * z) :
    |Chebyshev.theta y - y| ≤ 2 ^ (N + 1) * z / log z ^ N := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < log z := log_pos hz
  have hy0 : 0 < y := by linarith
  have hlog : log z / 2 ≤ log y := by
    have hh := log_le_log (by positivity : 0 < z / 2) hylo
    rw [log_div hz0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have hly : 0 < log y := by linarith
  have hp : log z ^ N ≤ 2 ^ N * log y ^ N := by
    have hh := pow_le_pow_left₀ hl.le (show log z ≤ 2 * log y by linarith) N
    simpa only [mul_pow] using hh
  have he : y / log y ^ N ≤ 2 ^ (N + 1) * z / log z ^ N := by
    apply (div_le_div_iff₀ (pow_pos hly N) (pow_pos hl N)).mpr
    calc
      y * log z ^ N ≤ y * (2 ^ N * log y ^ N) :=
        mul_le_mul_of_nonneg_left hp hy0.le
      _ ≤ (2 * z) * (2 ^ N * log y ^ N) :=
        mul_le_mul_of_nonneg_right hyhi (by positivity)
      _ = _ := by rw [pow_succ]; ring
  exact (hθ y (hT.trans hylo)).trans he

/-- GLOBAL theta errors at fixed log power A+1 supply both moving finite
bands. The threshold is chosen before z and eta=e/log(z)^A. -/
theorem eventually_first_prefix_windows (A : ℕ) {e : ℝ} (he : 0 < e)
    (heb : e ≤ 1 / 4) :
    ∀ᶠ z : ℝ in atTop,
      1 < z ∧ 1 ≤ log z ∧ 0 < e / log z ^ A ∧ e / log z ^ A ≤ 1 / 4 ∧
      4 ≤ (e / log z ^ A) * z ∧
      (e / log z ^ A) * z / 8 ≤
        Chebyshev.theta (z * (1 - (e / log z ^ A) / 2)) -
          Chebyshev.theta (z * (1 - 3 * (e / log z ^ A) / 4)) ∧
      (e / log z ^ A) * z / 8 ≤
        Chebyshev.theta (z * (1 + 3 * (e / log z ^ A) / 4)) -
          Chebyshev.theta (z * (1 + (e / log z ^ A) / 2)) := by
  have hθev : ∀ᶠ y : ℝ in atTop,
      |Chebyshev.theta y - y| ≤ y / log y ^ (A + 1) := by
    filter_upwards [(theta_error_log_power (A + 1)).bound (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (1 : ℝ)] with y hy hy1
    have hpos : 0 ≤ y / log y ^ (A + 1) :=
      div_nonneg (by linarith) (pow_nonneg (log_pos hy1).le _)
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hpos] using hy
  obtain ⟨T, hT⟩ := eventually_atTop.mp hθev
  have hsmall : Tendsto (fun z : ℝ => log z ^ A / z) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (A : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * log 2)),
    eventually_ge_atTop (2 * T),
    tendsto_log_atTop.eventually_ge_atTop (16 * 2 ^ (A + 2) / e),
    hsmall.eventually_lt_const (by positivity : (0 : ℝ) < e / 4)]
    with z hz hL hTz hbig hsmallz
  have hz0 : 0 < z := by linarith
  have hL1 : 1 ≤ log z := (le_max_left _ _).trans hL
  have hl : 0 < log z := by linarith
  have hL2 : 2 * log 2 ≤ log z := (le_max_right _ _).trans hL
  let η := e / log z ^ A
  have hη : 0 < η := by dsimp [η]; positivity
  have hηb : η ≤ 1 / 4 := by
    have hp : 1 ≤ log z ^ A := one_le_pow₀ hL1
    exact (div_le_self he.le hp).trans heb
  have hsize : 4 ≤ η * z := by
    have hh := (div_lt_iff₀ hz0).mp hsmallz
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hl A)).mpr
    nlinarith
  have hcoeff : 2 ^ (A + 2) / log z ≤ e / 16 := by
    apply (div_le_iff₀ hl).mpr
    have hh := (div_le_iff₀ he).mp hbig
    nlinarith
  have herror (y : ℝ) (hylo : z / 2 ≤ y) (hyhi : y ≤ 2 * z) :
      |Chebyshev.theta y - y| ≤ η * z / 16 := by
    have hh := uniform_theta_error hz hL2 (by linarith : T ≤ z / 2)
      (A + 1) hT hylo hyhi
    apply hh.trans
    calc
      2 ^ (A + 1 + 1) * z / log z ^ (A + 1) =
          (2 ^ (A + 2) / log z) * (z / log z ^ A) := by
        simp only [pow_succ]
        field_simp [hl.ne'] <;> ring
      _ ≤ (e / 16) * (z / log z ^ A) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = η * z / 16 := by dsimp [η]; ring
  have hηz := mul_le_mul_of_nonneg_right hηb hz0.le
  have hηz0 := mul_pos hη hz0
  have ha := herror (z * (1 - 3 * η / 4)) (by nlinarith) (by nlinarith)
  have hb := herror (z * (1 - η / 2)) (by nlinarith) (by nlinarith)
  have hc := herror (z * (1 + η / 2)) (by nlinarith) (by nlinarith)
  have hd := herror (z * (1 + 3 * η / 4)) (by nlinarith) (by nlinarith)
  refine ⟨hz, hL1, hη, hηb, hsize, ?_, ?_⟩
  · linarith [(abs_le.mp ha).2, (abs_le.mp hb).1]
  · linarith [(abs_le.mp hc).2, (abs_le.mp hd).1]

/-- Every fixed logarithmic scale, uniformly over ALL positive prime-prefix
integers with bounded SAME actual normalized defect. The unit is in scope;
its missing first band rules it out naturally, with no n>=2 threshold. -/
theorem bounded_defect_first_prefix_localization (A : ℕ) {K : ℝ} (hK : 0 ≤ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, 2 ≤ Z ∧ ∀ z : ℝ, Z ≤ z → ∀ n : ℕ, 1 ≤ n →
      n.primeFactors = Nat.primesLE (largestPrime n) →
      sqrt z * log z * actualDefect z n ≤ K →
      |log z ^ A * ((largestPrime n : ℝ) / z - 1)| < ε := by
  let e : ℝ := min ε (1 / 4)
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have heb : e ≤ 1 / 4 := min_le_right _ _
  have hr : Tendsto (fun z : ℝ => log z ^ (2 * A) / sqrt z) atTop (𝓝 0) := by
    simpa only [rpow_natCast, ← sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 * A : ℕ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hc : 0 < e ^ 2 / (32 * (K + 1)) := by positivity
  have hev := (eventually_first_prefix_windows A he heb).and
    (hr.eventually_lt_const hc)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp hev
  refine ⟨max 2 Z₀, le_max_left _ _, ?_⟩
  intro z hz n hn hsupport hd
  obtain ⟨⟨hz1, hL1, hη, hηb, hsize, hbelow, habove⟩, hcost⟩ :=
    hZ₀ z ((le_max_right _ _).trans hz)
  have hz0 : 0 < z := by linarith
  have hl : 0 < log z := by linarith
  have hr0 : 0 < sqrt z := sqrt_pos.mpr hz0
  have hp : 0 < log z ^ A := pow_pos hl A
  by_contra! hbad
  have hbad' : e ≤ |log z ^ A * ((largestPrime n : ℝ) / z - 1)| := heε.trans hbad
  have hfar : (largestPrime n : ℝ) ≤ z * (1 - e / log z ^ A) ∨
      z * (1 + e / log z ^ A) ≤ (largestPrime n : ℝ) := by
    by_cases hP : (largestPrime n : ℝ) ≤ z
    · left
      have hsign : log z ^ A * ((largestPrime n : ℝ) / z - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le
          (by have := (div_le_one hz0).mpr hP; linarith)
      rw [abs_of_nonpos hsign] at hbad'
      have heq : -(log z ^ A * ((largestPrime n : ℝ) / z - 1)) =
          log z ^ A * (z - (largestPrime n : ℝ)) / z := by
        field_simp [hz0.ne'] <;> ring
      rw [heq] at hbad'
      have hh := (le_div_iff₀ hz0).mp hbad'
      have hηeq : z * (1 - e / log z ^ A) = z - e * z / log z ^ A := by ring
      rw [hηeq]
      have hdiv : e * z / log z ^ A ≤ z - (largestPrime n : ℝ) :=
        (div_le_iff₀ hp).mpr (by nlinarith)
      linarith
    · right
      have hP' : z ≤ (largestPrime n : ℝ) := (lt_of_not_ge hP).le
      have hsign : 0 ≤ log z ^ A * ((largestPrime n : ℝ) / z - 1) :=
        mul_nonneg hp.le (by have := (one_le_div hz0).mpr hP'; linarith)
      rw [abs_of_nonneg hsign] at hbad'
      have hh : e * z ≤ log z ^ A * ((largestPrime n : ℝ) - z) := by
        have heq : log z ^ A * ((largestPrime n : ℝ) / z - 1) =
            (log z ^ A * ((largestPrime n : ℝ) - z)) / z := by
          field_simp [hz0.ne'] <;> ring
        rw [heq] at hbad'
        exact (le_div_iff₀ hz0).mp hbad'
      have hdiv : e * z / log z ^ A ≤ (largestPrime n : ℝ) - z :=
        (div_le_iff₀ hp).mpr (by nlinarith)
      have heq : z * (1 + e / log z ^ A) = z + e * z / log z ^ A := by ring
      rw [heq]
      linarith
  have hcharge := first_prefix_displacement_charge hz1 hη hηb hsize hbelow habove
    hn hsupport hfar
  have hcost' : K < (e / log z ^ A) ^ 2 * sqrt z / 32 := by
    have hden : 0 < 32 * (K + 1) := by positivity
    have hh := (div_lt_div_iff₀ hr0 hden).mp hcost
    have hpow : log z ^ (2 * A) = (log z ^ A) ^ 2 := by rw [mul_comm 2 A, pow_mul]
    rw [hpow] at hh
    have hpos : 0 < (log z ^ A) ^ 2 := sq_pos_of_pos hp
    have hraw : K + 1 < e ^ 2 * sqrt z / (32 * (log z ^ A) ^ 2) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith
    have heq : e ^ 2 * sqrt z / (32 * (log z ^ A) ^ 2) =
        (e / log z ^ A) ^ 2 * sqrt z / 32 := by ring
    rw [heq] at hraw
    linarith
  linarith

end D5.S3.Arith.Robin.PriceRecord.FirstPrimePrefixLocalization
