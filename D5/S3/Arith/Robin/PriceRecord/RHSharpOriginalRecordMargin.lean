/- GID: D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp lower Robin-margin endpoint for original positive-price strict records under RH. -/

import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-! Sharp lower Robin-margin control and attainment on original strict records. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime tail tail_robin_data)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D B actual_B_lower_endpoint)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)

namespace D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin

private abbrev C := FullArithmeticCorrectionSecondOrder.correction
def K : ℝ := 2 * Real.sqrt 2 - 2 - firstLiMass

theorem fullC_leading (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      1 < Chebyshev.theta (largestPrime m : ℝ) ∧ 1 < Real.log (m : ℝ) ∧
      |D (largestPrime m : ℝ) * C m - 2 * Real.sqrt 2| < epsilon := by
  obtain ⟨T0, hT0, hT⟩ :=
    FullArithmeticCorrectionSecondOrder.price_record_full_arithmetic_correction_second_order
      1 zero_lt_one
  let d := Real.sqrt 2 * (2 + Real.log 2)
  let Z := 1 + (1 + |d|) / epsilon
  refine ⟨max (max T0 2) (Real.exp Z), (le_max_right T0 2).trans (le_max_left _ _), ?_⟩
  intro m hm lambda hlambda hrecord hlarge
  have hP : T0 ≤ (largestPrime m : ℝ) :=
    (le_max_left T0 2).trans ((le_max_left _ _).trans hlarge)
  have h := hT m hm lambda hlambda hrecord hP
  refine ⟨h.1, h.2.1, ?_⟩
  let P : ℝ := largestPrime m
  have hP2 : 2 ≤ P := (le_max_right T0 2).trans ((le_max_left _ _).trans hlarge)
  have hLP : Z ≤ Real.log P := by
    have hh := Real.log_le_log (Real.exp_pos Z) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp] using hh
  have hL : 0 < Real.log P := Real.log_pos (by linarith)
  have hab : |Real.log P * (D P * C m - 2*Real.sqrt 2) + d| < 1 := by
    simpa only [P, D, C, FullArithmeticCorrectionSecondOrder.correction, d] using h.2.2.1
  have htriangle : |Real.log P * (D P * C m - 2*Real.sqrt 2)| < 1 + |d| := by
    have hh := abs_sub (Real.log P * (D P * C m - 2*Real.sqrt 2)+d) d
    rw [add_sub_cancel_right] at hh
    linarith
  rw [abs_mul, abs_of_pos hL] at htriangle
  have hsmall : (1 + |d|) / epsilon < Real.log P := by
    dsimp [Z] at hLP
    linarith
  have hZ : 1 + |d| < epsilon * Real.log P := by
    have hh := (div_lt_iff₀ he).mp hsmall
    nlinarith
  nlinarith [htriangle.trans hZ]

def Pn (x : ℝ) : ℕ := (Nat.primesLE ⌊x⌋₊).sup id

private lemma prime_prefix (x : ℝ) : Nat.primesLE (Pn x) = Nat.primesLE ⌊x⌋₊ := by
  have hPN : Pn x ≤ ⌊x⌋₊ := by
    apply Finset.sup_le
    intro p hp
    exact (Nat.mem_primesLE.mp hp).1
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpP.trans hPN, hprime⟩
  · intro hp
    exact Nat.mem_primesLE.mpr ⟨Finset.le_sup (f := id) hp, (Nat.mem_primesLE.mp hp).2⟩

private lemma Pn_two {x : ℝ} (hx : 2 ≤ x) : 2 ≤ Pn x := by
  exact Finset.le_sup (f := id) (Nat.mem_primesLE.mpr ⟨Nat.le_floor hx, Nat.prime_two⟩)

private lemma theta_prefix (x : ℝ) : Chebyshev.theta (Pn x : ℝ) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE, prime_prefix]

lemma B_prefix (x : ℝ) : B (Pn x : ℝ) = B x := by
  have he : Mertens.E₃ (Pn x : ℝ) - Real.log (Real.log (Pn x : ℝ)) =
      Mertens.E₃ x - Real.log (Real.log x) := by
    unfold Mertens.E₃
    rw [Nat.floor_natCast, ← Nat.primesLE_eq_filter_Ioc_zero,
      ← Nat.primesLE_eq_filter_Ioc_zero, prime_prefix]
    ring
  dsimp [B]
  rw [theta_prefix]
  linarith

lemma cutoff_record (x : ℝ) (hx : 2 ≤ x) :
    ∃ m : ℕ, ∃ lambda : ℝ, 2 ≤ m ∧ 0 < lambda ∧
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) ∧
      m.primeFactors = Nat.primesLE ⌊x⌋₊ ∧ largestPrime m = Pn x := by
  let N := ⌊x⌋₊
  let lambda := ActualBalancedCutoff.firstLayerPrice ((N : ℝ) + 1)
  have hN : 2 ≤ N := Nat.le_floor hx
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlambda : 0 < lambda := by
    dsimp [lambda, ActualBalancedCutoff.firstLayerPrice]
    have hi : 0 < 1 / ((N : ℝ) + 1) := one_div_pos.mpr (by linarith)
    exact div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
  have hactive (p : ℕ) (hp : p.Prime) :
      lambda < goldenLayerMarginal p 1 ↔ p ≤ N := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    change ActualBalancedCutoff.firstLayerPrice ((N : ℝ) + 1) <
      ActualBalancedCutoff.firstLayerPrice (p : ℝ) ↔ p ≤ N
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    constructor
    · intro h
      by_contra hnot
      have hle : (N : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : N + 1 ≤ p)
      have hh := ActualBalancedCutoff.firstLayerPrice_strictAnti.antitoneOn
        (by linarith : 1 < (N : ℝ) + 1) hp1 hle
      exact (not_lt_of_ge hh) h
    · intro h
      apply ActualBalancedCutoff.firstLayerPrice_strictAnti hp1
        (by linarith : 1 < (N : ℝ) + 1)
      have : (p : ℝ) ≤ N := by exact_mod_cast h
      linarith
  obtain ⟨m, hm, hcounts, hopt, hleast⟩ := optimal_layer_count_spec hlambda
  have hcount (p : ℕ) (hp : p.Prime) :
      1 ≤ m.factorization p ↔ p ≤ N := by
    rw [hcounts]
    have hmem := Set.ext_iff.mp (positive_layers_eq_count_interval hlambda hp) (1 : ℕ)
    change (1 ≤ (1 : ℕ) ∧ p.Prime ∧ lambda < goldenLayerMarginal p 1) ↔
      (1 ≤ (1 : ℕ) ∧ 1 ≤ optimalLayerCount lambda p) at hmem
    simpa only [le_refl, hp, true_and, hactive p hp] using hmem.symm
  have hsupport : m.primeFactors = Nat.primesLE N := by
    ext p
    constructor
    · intro hp
      obtain ⟨hprime, hdvd, hm0⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesLE.mpr ⟨(hcount p hprime).mp
        ((hprime.dvd_iff_one_le_factorization hm0).mp hdvd), hprime⟩
    · intro hp
      obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hprime,
        (hprime.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr
          ((hcount p hprime).mpr hpN), by omega⟩
  have h2dvd : 2 ∣ m := (Nat.prime_two.dvd_iff_one_le_factorization
    (by omega : m ≠ 0)).mpr ((hcount 2 Nat.prime_two).mpr hN)
  have hm2 : 2 ≤ m := Nat.le_of_dvd (by omega : 0 < m) h2dvd
  have hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m := by
    intro n hn hnm
    have hle := hopt n (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hnopt : IsGoldenResourceOptimal lambda n := by
      intro k hk
      rw [heq]
      exact hopt k hk
    exact (Nat.le_of_dvd hn (hleast n (by omega) hnopt)).not_gt hnm
  refine ⟨m, lambda, hm2, hlambda, hrecord, hsupport, ?_⟩
  simp only [largestPrime, hsupport, Pn, N]

lemma Pn_atTop : Tendsto (fun x : ℝ => (Pn x : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro Y
  obtain ⟨p, hpY, hp⟩ := Nat.exists_infinite_primes ⌈Y⌉₊
  filter_upwards [eventually_ge_atTop (p : ℝ)] with x hx
  have hpN : p ∈ Nat.primesLE ⌊x⌋₊ := Nat.mem_primesLE.mpr ⟨Nat.le_floor hx, hp⟩
  have hP : p ≤ Pn x := Finset.le_sup (f := id) hpN
  exact (Nat.le_ceil Y).trans ((by exact_mod_cast hpY : (⌈Y⌉₊ : ℝ) ≤ p).trans
    (by exact_mod_cast hP))

lemma normalization :
    Tendsto (fun x : ℝ => D (Pn x : ℝ) / D x) atTop (𝓝 1) := by
  have htheta := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have hratio : Tendsto (fun x : ℝ => (Pn x : ℝ) / x) atTop (𝓝 1) := by
    have hh := htheta.div (htheta.comp Pn_atTop) (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at hh
    change Tendsto (fun x : ℝ => (Chebyshev.theta x / x) /
      (Chebyshev.theta (Pn x : ℝ) / (Pn x : ℝ))) atTop (𝓝 1) at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      htheta.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx ht
    have hx0 : 0 < x := by linarith
    have hP2 : (2 : ℝ) ≤ Pn x := by exact_mod_cast Pn_two hx
    have hP0 : (0 : ℝ) < Pn x := by linarith
    have ht0 : Chebyshev.theta x ≠ 0 := by
      have hpos : 0 < Chebyshev.theta x := by
        simpa only [zero_mul] using (lt_div_iff₀ hx0).mp ht
      exact hpos.ne'
    change (Chebyshev.theta x / x) /
      (Chebyshev.theta (Pn x : ℝ) / (Pn x : ℝ)) = (Pn x : ℝ) / x
    rw [theta_prefix]
    field_simp [hx0.ne', hP0.ne', ht0]
  have hlogdiff : Tendsto (fun x : ℝ => Real.log ((Pn x : ℝ) / x)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlogratio : Tendsto (fun x : ℝ => Real.log (Pn x : ℝ) / Real.log x) atTop (𝓝 1) := by
    have hh := (hlogdiff.div_atTop Real.tendsto_log_atTop).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), Pn_atTop.eventually_gt_atTop 1] with x hx hP
    change Real.log ((Pn x : ℝ) / x) / Real.log x + 1 =
      Real.log (Pn x : ℝ) / Real.log x
    rw [Real.log_div (by linarith : (Pn x : ℝ) ≠ 0) (by linarith : x ≠ 0)]
    field_simp [(Real.log_pos hx).ne']
    ring
  have hh := hratio.sqrt.mul hlogratio
  simp only [Real.sqrt_one, one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.sqrt_div (Nat.cast_nonneg _), div_mul_div_comm]
  rfl

private lemma B_transfer (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D (Pn x : ℝ) * B (Pn x : ℝ) - D x * B x) atTop (𝓝 0) := by
  let C := |firstLiMass| + 3
  have hbound : ∀ᶠ x : ℝ in atTop, |D x * B x| ≤ C := by
    filter_upwards [(actual_B_lower_endpoint hRH).1 1 zero_lt_one] with x hx
    have hh := abs_sub (D x * B x + 2) 2
    rw [add_sub_cancel_right] at hh
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    dsimp [C]
    linarith [le_abs_self firstLiMass, hx.2]
  have he : Tendsto (fun x : ℝ => (D (Pn x : ℝ) / D x - 1) * (D x * B x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x => |D (Pn x : ℝ) / D x - 1| * C) ?_
      (by simpa using (normalization.sub_const 1).abs.mul_const C)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  apply he.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [B_prefix]
  have hD : D x ≠ 0 := mul_ne_zero
    (Real.sqrt_pos.mpr (by linarith : 0 < x)).ne' (Real.log_pos hx).ne'
  field_simp [hD]

lemma margin_identity {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    robinLogMargin m = B (largestPrime m : ℝ) + C m := by
  have hs := (price_record_prime_structure hm hlambda hrecord).2
  rw [(tail_robin_data (by omega : 0 < m) hs).2]
  dsimp [B, C, FullArithmeticCorrectionSecondOrder.correction]
  ring

/-- Uniform lower control for every original strict record, and sharp attainment by genuine records. -/
theorem original_record_sharp_lower_endpoint (hRH : RiemannHypothesis) :
    (∀ epsilon : ℝ, 0 < epsilon → ∃ T : ℝ, 2 ≤ T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      K - epsilon < D (largestPrime m : ℝ) * robinLogMargin m) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ m : ℕ, ∃ lambda : ℝ, 2 ≤ m ∧ 0 < lambda ∧
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) ∧
      Y < (largestPrime m : ℝ) ∧ 1 < Chebyshev.theta (largestPrime m : ℝ) ∧
      1 < Real.log (m : ℝ) ∧
      |D (largestPrime m : ℝ) * robinLogMargin m - K| < epsilon) := by
  constructor
  · intro epsilon he
    obtain ⟨TB, hTB⟩ := eventually_atTop.mp
      ((actual_B_lower_endpoint hRH).1 (epsilon / 2) (by positivity))
    obtain ⟨TC, hTC, hC⟩ := fullC_leading (epsilon / 2) (by positivity)
    refine ⟨max TB TC, hTC.trans (le_max_right _ _), ?_⟩
    intro m hm lambda hlambda hrecord hlarge
    have hb := hTB (largestPrime m : ℝ) ((le_max_left _ _).trans hlarge)
    have hc := hC m hm lambda hlambda hrecord ((le_max_right _ _).trans hlarge)
    rw [margin_identity hm hlambda hrecord]
    dsimp [K]
    nlinarith [(abs_lt.mp hb.2).1, (abs_lt.mp hc.2.2).1]
  · intro epsilon he Y
    obtain ⟨TC, hTC, hC⟩ := fullC_leading (epsilon / 3) (by positivity)
    obtain ⟨TT, hTT⟩ := eventually_atTop.mp
      ((Metric.tendsto_nhds.mp (B_transfer hRH)) (epsilon / 3) (by positivity))
    have hPlarge : ∀ᶠ x : ℝ in atTop, max TC (Y + 1) ≤ (Pn x : ℝ) :=
      Pn_atTop.eventually_ge_atTop _
    obtain ⟨TP, hTP⟩ := eventually_atTop.mp hPlarge
    obtain ⟨x, hx, htheta, hb⟩ := (actual_B_lower_endpoint hRH).2.1
      (epsilon / 3) (by positivity) (max TT TP)
    have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
    have hxTT : TT ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
    have hxTP : TP ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
    obtain ⟨m, lambda, hm, hlambda, hrecord, hsupport, hP⟩ := cutoff_record x hx2
    have hlarge : TC ≤ (largestPrime m : ℝ) := by
      rw [hP]
      exact (le_max_left _ _).trans (hTP x hxTP)
    have hc := hC m hm lambda hlambda hrecord hlarge
    refine ⟨m, lambda, hm, hlambda, hrecord, ?_, hc.1, hc.2.1, ?_⟩
    · rw [hP]
      have hh := (le_max_right _ _).trans (hTP x hxTP)
      linarith
    · have ht := hTT x hxTT
      simp only [Real.dist_eq, sub_zero] at ht
      rw [margin_identity hm hlambda hrecord]
      have hid : D (largestPrime m : ℝ) * (B (largestPrime m : ℝ) + C m) - K =
          (D x * B x + 2 + firstLiMass) +
          (D (Pn x : ℝ) * B (Pn x : ℝ) - D x * B x) +
          (D (largestPrime m : ℝ) * C m - 2 * Real.sqrt 2) := by
        rw [hP]
        dsimp [K]
        ring
      rw [hid]
      exact (abs_add_le _ _).trans_lt (by
        have hh := abs_add_le (D x * B x + 2 + firstLiMass)
          (D (Pn x : ℝ) * B (Pn x : ℝ) - D x * B x)
        linarith [hc.2.2])

end D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
