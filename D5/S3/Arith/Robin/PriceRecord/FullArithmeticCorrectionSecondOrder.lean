/- GID: D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Same-integer mass and complete arithmetic correction at all positive-price records. -/

/- Full arithmetic correction at all positive-price strict predecessor records.
   The exact same-integer mass identity and a finite higher-layer bound give
   the logarithmic clock correction. The public CompleteTailSecondOrder
   endpoint supplies the Euler tail. Their sum has uniform second-order
   laws in both the largest-prime and original-integer logarithmic clocks.
   Arbitrarily large literal records realize both coefficients. The full
   integer, price and strict-predecessor telescope is retained throughout.
   The signed Mertens/theta expression remains uncontrolled: no Robin sign,
   RH statement or literature novelty is asserted. -/

import D5.S3.Arith.Robin.PriceRecord.CompleteTailSecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder

open Finset Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime tail)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.EulerLayerRootCorrection

/-- The complete ORIGINAL correction, with the integer's own logarithmic clock. -/
def correction (m : ℕ) : ℝ :=
  tail m + Real.log (Real.log (Real.log (m : ℝ))) -
    Real.log (Real.log (Chebyshev.theta (largestPrime m : ℝ)))

/-- Exact support of an occupied exponent layer; Q=1 is included. -/
private theorem layer_support {m j : ℕ} (hm : 0 < m) (hj : 1 ≤ j)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      m.factorization q ≤ m.factorization p) :
    m.primeFactors.filter (fun p => j ≤ m.factorization p) =
      Nat.primesLE (layerPrime m j) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpm, hjp⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨(le_sup (f := id) (mem_filter.mpr ⟨hpm, hjp⟩)).trans (le_max_right _ _),
        Nat.prime_of_mem_primeFactors hpm⟩
  · intro hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hp
    have hv := valuation_below_layer_prime hprime hanti hpQ
    have hpm := hprime.mem_primeFactors
      ((hprime.dvd_iff_one_le_factorization hm.ne').mpr (hj.trans hv)) hm.ne'
    exact mem_filter.mpr ⟨hpm, hv⟩

/-- A genuine same-integer factorization identity, not a clock hypothesis. -/
theorem record_log_mass {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    Real.log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ) =
      Chebyshev.theta (layerPrime m 2 : ℝ) + strict_inventory_third_layer_mass m := by
  obtain ⟨hanti, hsupport⟩ := price_record_prime_structure hm hlambda hrecord
  have hsplit := log_inventory_split (by omega : 0 < m)
  have hfirst : (∑ p ∈ m.primeFactors, Real.log (p : ℝ)) =
      Chebyshev.theta (largestPrime m : ℝ) := by
    rw [hsupport, Chebyshev.theta_eq_sum_primesLE_log]
  have hsecond : strict_inventory_second_layer_mass m =
      Chebyshev.theta (layerPrime m 2 : ℝ) := by
    rw [strict_inventory_second_layer_mass,
      layer_support (by omega : 0 < m) (by norm_num : 1 ≤ (2 : ℕ)) hanti,
      Chebyshev.theta_eq_sum_primesLE_log]
  rw [hfirst, hsecond] at hsplit
  linarith

/-- The third and higher layers cost at most Q3 times one prime-power log.
No maximum-exponent theorem and no infinite layer sum is used. -/
theorem record_third_mass_bound {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    0 ≤ strict_inventory_third_layer_mass m ∧
    strict_inventory_third_layer_mass m ≤
      (layerPrime m 3 : ℝ) * Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
  classical
  let S := m.primeFactors.filter (fun p => 3 ≤ m.factorization p)
  let B : ℝ := Real.log (4 * (largestPrime m : ℝ) ^ 2)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hP2 : 2 ≤ largestPrime m := hr.two_le.trans
    (le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hr, hrd, by omega⟩))
  have hB : 0 ≤ B := Real.log_nonneg (by
    have : (2 : ℝ) ≤ largestPrime m := by exact_mod_cast hP2
    nlinarith)
  have hcard : (S.card : ℝ) ≤ (layerPrime m 3 : ℝ) := by
    have hsub : S ⊆ Ioc 0 (layerPrime m 3) := by
      intro p hp
      exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos,
        (le_sup (f := id) hp).trans (le_max_right _ _)⟩
    have hh := card_le_card hsub
    exact_mod_cast (by simpa only [Nat.card_Ioc, Nat.sub_zero] using hh :
      S.card ≤ layerPrime m 3)
  have hterm (p : ℕ) (hp : p ∈ S) :
      0 ≤ ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p ∧
      ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p ≤ B := by
    have hprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hpow := PrimePowerEnvelope.price_record_prime_power_envelope hm hlambda.le
      hrecord p hprime (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
    have hpowR : (p : ℝ) ^ m.factorization p < 4 * (largestPrime m : ℝ) ^ 2 := by
      exact_mod_cast hpow
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog := Real.log_lt_log (pow_pos hp0 _) hpowR
    rw [Real.log_pow] at hlog
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hprime.log_pos.le, ?_⟩
    calc
      _ ≤ (m.factorization p : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (m.factorization p) 2)
          hprime.log_pos.le
      _ ≤ B := hlog.le
  refine ⟨sum_nonneg fun p hp => (hterm p hp).1, ?_⟩
  change (∑ p ∈ S, ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p) ≤ _
  calc
    _ ≤ (S.card : ℝ) * B := by
      simpa only [nsmul_eq_mul] using sum_le_card_nsmul S
        (fun p => ((m.factorization p - 2 : ℕ) : ℝ) * Real.log p) B
        (fun p hp => (hterm p hp).2)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

/- Elementary rate calculus. UnitRate w u records u=1+o(1/w), not an
   assumed clock expansion. Every concrete instance is proved below. -/
private def UnitRate {α : Type*} (l : Filter α) (w u : α → ℝ) : Prop :=
  Tendsto u l (𝓝 1) ∧ Tendsto (fun x => w x * (u x - 1)) l (𝓝 0)

private theorem unit_of_scaled {α : Type*} {l : Filter α} {w u : α → ℝ}
    (hw : Tendsto w l atTop)
    (hu : Tendsto (fun x => w x * (u x - 1)) l (𝓝 0)) : UnitRate l w u := by
  refine ⟨?_, hu⟩
  have hd : Tendsto (fun x => u x - 1) l (𝓝 0) := by
    apply (hu.div_atTop hw).congr'
    filter_upwards [hw.eventually_gt_atTop 0] with x hx
    exact mul_div_cancel_left₀ _ hx.ne'
  simpa only [sub_add_cancel, zero_add] using hd.add_const 1

private theorem unit_mul {α : Type*} {l : Filter α} {w u v : α → ℝ}
    (hu : UnitRate l w u) (hv : UnitRate l w v) :
    UnitRate l w (fun x => u x * v x) := by
  refine ⟨by simpa using hu.1.mul hv.1, ?_⟩
  have hh := (hu.2.mul hv.1).add hv.2
  simp only [zero_mul, zero_add] at hh
  exact hh.congr (fun x => by ring)

private theorem unit_inv {α : Type*} {l : Filter α} {w u : α → ℝ}
    (hu : UnitRate l w u) : UnitRate l w (fun x => (u x)⁻¹) := by
  refine ⟨by simpa using hu.1.inv₀ (by norm_num : (1 : ℝ) ≠ 0), ?_⟩
  have hh := hu.2.neg.div hu.1 (by norm_num : (1 : ℝ) ≠ 0)
  simp only [neg_zero, zero_div] at hh
  apply hh.congr'
  filter_upwards [hu.1.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx
  dsimp
  field_simp [hx.ne']
  ring

private theorem unit_sqrt {α : Type*} {l : Filter α} {w u : α → ℝ}
    (hu : UnitRate l w u) : UnitRate l w (fun x => Real.sqrt (u x)) := by
  have hs : Tendsto (fun x => Real.sqrt (u x)) l (𝓝 1) := by
    simpa using hu.1.sqrt
  refine ⟨hs, ?_⟩
  have hh := hu.2.div (hs.add_const 1) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [hu.1.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
    with x hx
  have hd : Real.sqrt (u x) + 1 ≠ 0 := (by positivity : 0 < Real.sqrt (u x) + 1).ne'
  symm
  apply (eq_div_iff hd).mpr
  calc
    (w x * (Real.sqrt (u x) - 1)) * (Real.sqrt (u x) + 1) =
        w x * (Real.sqrt (u x) ^ 2 - 1) := by ring
    _ = w x * (u x - 1) := by rw [Real.sq_sqrt hx.le]

/-- Multiplication transports a second coefficient when the factor is 1+o(1/w). -/
private theorem second_mul_unit {α : Type*} {l : Filter α} {w u v : α → ℝ}
    {a b : ℝ} (hw : Tendsto w l atTop)
    (hu : Tendsto (fun x => w x * (u x - a)) l (𝓝 b))
    (hv : UnitRate l w v) :
    Tendsto (fun x => w x * (u x * v x - a)) l (𝓝 b) := by
  have hh := (hu.mul hv.1).add (hv.2.const_mul a)
  simp only [mul_one, mul_zero, add_zero] at hh
  exact hh.congr (fun x => by ring)

-- Congruence is kept separate so rates never hide pointwise assumptions.
private theorem unit_congr {α : Type*} {l : Filter α} {w u v : α → ℝ}
    (hu : UnitRate l w u) (h : u =ᶠ[l] v) : UnitRate l w v :=
  ⟨hu.1.congr' h, hu.2.congr' (h.mono fun x hx => by rw [hx])⟩


/-- Relative clocks and their logarithms, including eventual positivity.
The rate of log(y)/log(t) follows from the EXACT log quotient identity. -/
private theorem relative_clocks {α : Type*} {l : Filter α} {t y : α → ℝ}
    (ht : Tendsto t l atTop)
    (hy : UnitRate l (fun x => Real.log (t x)) (fun x => y x / t x)) :
    Tendsto y l atTop ∧
    UnitRate l (fun x => Real.log (t x))
      (fun x => Real.log (y x) / Real.log (t x)) ∧
    UnitRate l (fun x => Real.log (t x))
      (fun x => t x * Real.log (t x) / (y x * Real.log (y x))) := by
  have hL := Real.tendsto_log_atTop.comp ht
  have hyTop : Tendsto y l atTop := by
    apply (hy.1.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) ht).congr'
    filter_upwards [ht.eventually_gt_atTop 0] with x hx
    exact div_mul_cancel₀ _ hx.ne'
  have hlog : Tendsto (fun x => Real.log (y x / t x)) l (𝓝 0) := by
    simpa using hy.1.log (by norm_num : (1 : ℝ) ≠ 0)
  have hlogRate : Tendsto
      (fun x => Real.log (t x) * (Real.log (y x) / Real.log (t x) - 1))
      l (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [ht.eventually_gt_atTop 1, hyTop.eventually_gt_atTop 1] with x hx hyx
    rw [Real.log_div (by linarith : y x ≠ 0) (by linarith : t x ≠ 0)]
    field_simp [(Real.log_pos hx).ne']
    <;> ring
  have hlogUnit := unit_of_scaled hL hlogRate
  refine ⟨hyTop, hlogUnit, ?_⟩
  apply unit_congr (unit_inv (unit_mul hy hlogUnit))
  filter_upwards [ht.eventually_gt_atTop 1, hyTop.eventually_gt_atTop 1] with x hx hyx
  field_simp [(by linarith : t x ≠ 0), (by linarith : y x ≠ 0),
    (Real.log_pos hx).ne', (Real.log_pos hyx).ne']
  <;> ring

/-- Public PNT error supplies theta(t)/t=1+o(1/log(t)). -/
private theorem theta_unit {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l atTop) :
    UnitRate l (fun x => Real.log (t x)) (fun x => Chebyshev.theta (t x) / t x) := by
  have hL := Real.tendsto_log_atTop.comp ht
  have he := LogarithmicLayerRigidity.theta_error_eight.tendsto_div_nhds_zero.comp ht
  have hi : Tendsto (fun x => 1 / Real.log (t x) ^ 7) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp hL)
  apply unit_of_scaled hL
  have hh := he.mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [ht.eventually_gt_atTop 1] with x hx
  simp only [Function.comp_def]
  field_simp [(by linarith : t x ≠ 0), (Real.log_pos hx).ne']
  <;> ring

/-- The two tangent inequalities supply a finite nonlinear remainder bracket.
They include E=0 and require only the real positive-log domain. -/
private theorem clock_bracket {a e : ℝ} (ha : 1 < a) (he : 0 ≤ e) :
    e / ((a + e) * Real.log (a + e)) ≤
      Real.log (Real.log (a + e)) - Real.log (Real.log a) ∧
    Real.log (Real.log (a + e)) - Real.log (Real.log a) ≤ e / (a * Real.log a) := by
  by_cases hz : e = 0
  · simp [hz]
  have he0 : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
  have hae : 1 < a + e := by linarith
  have hupper := RestrictedDivisorStrictInventory.loglog_tangent ha hae (by linarith)
  have hlower := RestrictedDivisorStrictInventory.loglog_tangent hae ha (by linarith)
  have hu : Real.log (Real.log (a + e)) - Real.log (Real.log a) ≤
      e / (a * Real.log a) := by
    simpa [ActualRobinClockCovariance.g, div_eq_mul_inv] using hupper.le
  have hl : e / ((a + e) * Real.log (a + e)) ≤
      Real.log (Real.log (a + e)) - Real.log (Real.log a) := by
    simpa [ActualRobinClockCovariance.g, div_eq_mul_inv] using
      (neg_le_neg hlower.le)
  exact ⟨hl, hu⟩

private theorem log_power_small {α : Type*} {l : Filter α} {P : α → ℝ}
    (hP : Tendsto P l atTop) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => Real.log (P x) ^ n / P x ^ r) l (𝓝 0) := by
  simpa only [Real.rpow_natCast, Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop (n : ℝ) hr).tendsto_div_nhds_zero.comp hP)

theorem record_layer_ratio {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop)
    (j : ℕ) (hj : 2 ≤ j) :
    Tendsto (fun x => (layerPrime (m x) j : ℝ) ^ j /
      (largestPrime (m x) : ℝ)) l (𝓝 (j : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨T, _, hT⟩ := price_record_fixed_layer_rigidity j hj epsilon hepsilon
  filter_upwards [hP.eventually_ge_atTop T] with x hx
  simpa only [Real.dist_eq] using hT (m x) (hm x) (lambda x) (hlambda x) (hrecord x) hx

/-- Only the j=2 rigidity is used to recover the second coefficient of Q2.
The first-order/logarithmic ratios are derived, not supplied as assumptions. -/
private theorem second_layer_limits {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => (layerPrime (m x) 2 : ℝ)) l atTop ∧
    Tendsto (fun x => Real.log (layerPrime (m x) 2 : ℝ) /
      Real.log (largestPrime (m x) : ℝ)) l (𝓝 (1 / 2 : ℝ)) ∧
    Tendsto (fun x => (layerPrime (m x) 2 : ℝ) /
      Real.sqrt (largestPrime (m x) : ℝ)) l (𝓝 (Real.sqrt 2)) ∧
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      ((layerPrime (m x) 2 : ℝ) / Real.sqrt (largestPrime (m x) : ℝ) - Real.sqrt 2))
      l (𝓝 (-Real.sqrt 2 * Real.log 2 / 2)) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => layerPrime (m x) 2
  let L : α → ℝ := fun x => Real.log (P x)
  let z : α → ℝ := fun x => Q x / Real.sqrt (P x)
  let k : ℝ := Real.sqrt 2
  have hk : 0 < k := Real.sqrt_pos.mpr (by norm_num)
  have hk2 : k ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hL : Tendsto L l atTop := Real.tendsto_log_atTop.comp hP
  have hraw := record_layer_ratio m lambda hm hlambda hrecord hP 2 (by norm_num)
  have hzsq : Tendsto (fun x => z x ^ 2) l (𝓝 2) := by
    apply hraw.congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hp
    dsimp [z]
    rw [div_pow, Real.sq_sqrt hp.le]
  have hz : Tendsto z l (𝓝 k) := by
    apply hzsq.sqrt.congr
    intro x
    exact Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hQ : Tendsto Q l atTop := by
    apply (hz.pos_mul_atTop hk (Real.tendsto_sqrt_atTop.comp hP)).congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hp
    exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hp).ne'
  have hlogz : Tendsto (fun x => Real.log (z x)) l (𝓝 (Real.log k)) := hz.log hk.ne'
  have hH : Tendsto (fun x => Real.log (Q x) / L x) l (𝓝 (1 / 2 : ℝ)) := by
    have hh := (hlogz.div_atTop hL).add_const (1 / 2 : ℝ)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 1, hQ.eventually_gt_atTop 0] with x hp hq
    dsimp [z, L]
    rw [Real.log_div hq.ne' (Real.sqrt_pos.mpr (by linarith)).ne',
      Real.log_sqrt (by linarith : 0 ≤ P x)]
    have hlogP : Real.log (P x) ≠ 0 := (Real.log_pos hp).ne'
    field_simp [hlogP] <;> ring
  have hrigidity : Tendsto (fun x => L x * (Q x ^ 2 / (2 * P x) - 1))
      l (𝓝 (-Real.log 2)) := by
    have hh : Tendsto (fun x => L x * (Q x ^ 2 / (2 * P x) - 1) + Real.log 2)
        l (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro epsilon hepsilon
      obtain ⟨T, _, hT⟩ := LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity
        2 (by norm_num) epsilon hepsilon
      filter_upwards [hP.eventually_ge_atTop T] with x hx
      simpa only [Real.dist_eq, sub_zero, Nat.cast_ofNat, P, Q, L] using
        hT (m x) (hm x) (lambda x) (hlambda x) (hrecord x) hx
    simpa only [add_sub_cancel_right, zero_sub] using hh.sub_const (Real.log 2)
  have hd := (hrigidity.const_mul 2).div (hz.add_const k) (by positivity : k + k ≠ 0)
  have hval : 2 * (-Real.log 2) / (k + k) = -k * Real.log 2 / 2 := by
    field_simp [hk.ne', (by positivity : k + k ≠ 0)]
    nlinarith [congrArg (fun t : ℝ => Real.log 2 * t) hk2]
  rw [hval] at hd
  refine ⟨hQ, hH, hz, ?_⟩
  apply hd.congr'
  filter_upwards [hP.eventually_gt_atTop 0] with x hp
  have hd0 : z x + k ≠ 0 := (by
    have hz0 : 0 ≤ z x := div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    positivity : 0 < z x + k).ne'
  have hsq : z x ^ 2 = Q x ^ 2 / P x := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt hp.le]
  symm
  apply (eq_div_iff hd0).mpr
  have heq : (z x - k) * (z x + k) = 2 * (Q x ^ 2 / (2 * P x) - 1) := by
    rw [show Q x ^ 2 / (2 * P x) = (Q x ^ 2 / P x) / 2 by ring]
    nlinarith
  calc
    (L x * (z x - k)) * (z x + k) = L x * ((z x - k) * (z x + k)) := by ring
    _ = 2 * (L x * (Q x ^ 2 / (2 * P x) - 1)) := by rw [heq]; ring

/-- Q3=O(P^(1/3)) and the finite envelope make all layers >=3 negligible
at the stronger mass scale sqrt(P)/log(P). -/
private theorem third_mass_negligible {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      strict_inventory_third_layer_mass (m x) / Real.sqrt (largestPrime (m x) : ℝ))
      l (𝓝 0) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let L : α → ℝ := fun x => Real.log (P x)
  let A : ℝ := (4 : ℝ) ^ (1 / 3 : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hratio := record_layer_ratio m lambda hm hlambda hrecord hP 3 (by norm_num)
  have hQbound : ∀ᶠ x in l, (layerPrime (m x) 3 : ℝ) ≤ A * P x ^ (1 / 3 : ℝ) := by
    filter_upwards [hP.eventually_gt_atTop 0,
      hratio.eventually (eventually_lt_nhds (by norm_num : (3 : ℝ) < 4))] with x hp hq
    have hc : (layerPrime (m x) 3 : ℝ) ^ 3 ≤ 4 * P x :=
      (div_le_iff₀ hp).mp hq.le
    have hr := Real.rpow_le_rpow (by positivity) hc (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hleft : ((layerPrime (m x) 3 : ℝ) ^ 3) ^ (1 / 3 : ℝ) =
        (layerPrime (m x) 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    rw [hleft, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hp.le] at hr
    exact hr
  have hmajor : Tendsto
      (fun x => A * (Real.log 4 * (L x / P x ^ (1 / 6 : ℝ)) +
        2 * (L x ^ 2 / P x ^ (1 / 6 : ℝ)))) l (𝓝 0) := by
    simpa only [mul_zero, add_zero, pow_one] using
      (((log_power_small hP 1 (by norm_num : (0 : ℝ) < 1 / 6)).const_mul
        (Real.log 4)).add
        ((log_power_small hP 2 (by norm_num : (0 : ℝ) < 1 / 6)).const_mul 2)).const_mul A
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hP.eventually_gt_atTop 1] with x hp
    exact div_nonneg (mul_nonneg (Real.log_pos hp).le
      (record_third_mass_bound (hm x) (hlambda x) (hrecord x)).1) (Real.sqrt_nonneg _)
  · filter_upwards [hP.eventually_gt_atTop 1, hQbound] with x hp hq
    have hp0 : 0 < P x := by linarith
    have hb := (record_third_mass_bound (hm x) (hlambda x) (hrecord x)).2
    have hlogB : Real.log (4 * P x ^ 2) = Real.log 4 + 2 * L x := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 2 hp0.ne'), Real.log_pow]
      simp [L]
    have hlogB0 : 0 ≤ Real.log (4 * P x ^ 2) := Real.log_nonneg (by nlinarith)
    have hbound := hb.trans (mul_le_mul_of_nonneg_right hq hlogB0)
    have hs : Real.sqrt (P x) = P x ^ (1 / 3 : ℝ) * P x ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0]
      norm_num
    calc
      _ ≤ L x * (A * P x ^ (1 / 3 : ℝ) * Real.log (4 * P x ^ 2)) /
          Real.sqrt (P x) := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbound (Real.log_pos hp).le) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [hs, hlogB]
        field_simp [(Real.rpow_pos_of_pos hp0 (1 / 3 : ℝ)).ne',
          (Real.rpow_pos_of_pos hp0 (1 / 6 : ℝ)).ne']
        <;> ring

/-- Same-integer E=Q2+o(sqrt(P)/log(P)), with the actual Q2 coefficient.
In particular, the X/P conclusion is relative: it does not bound X-P by sqrt(P). -/
theorem record_mass_limits {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => (Real.log (m x : ℝ) - Chebyshev.theta (largestPrime (m x) : ℝ)) /
      Real.sqrt (largestPrime (m x) : ℝ)) l (𝓝 (Real.sqrt 2)) ∧
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      ((Real.log (m x : ℝ) - Chebyshev.theta (largestPrime (m x) : ℝ)) /
        Real.sqrt (largestPrime (m x) : ℝ) - Real.sqrt 2))
      l (𝓝 (-Real.sqrt 2 * Real.log 2 / 2)) ∧
    UnitRate l (fun x => Real.log (largestPrime (m x) : ℝ))
      (fun x => Real.log (m x : ℝ) / (largestPrime (m x) : ℝ)) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let Q : α → ℝ := fun x => layerPrime (m x) 2
  let L : α → ℝ := fun x => Real.log (P x)
  let X : α → ℝ := fun x => Real.log (m x : ℝ)
  let E : α → ℝ := fun x => X x - Chebyshev.theta (P x)
  obtain ⟨hQ, hH, hz, hzD⟩ := second_layer_limits m lambda hm hlambda hrecord hP
  have hL : Tendsto L l atTop := Real.tendsto_log_atTop.comp hP
  have hLQ : Tendsto (fun x => L x / Real.log (Q x)) l (𝓝 2) := by
    simpa using hH.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have htQ := theta_unit hQ
  have hthetaError : Tendsto
      (fun x => L x * (Chebyshev.theta (Q x) - Q x) / Real.sqrt (P x)) l (𝓝 0) := by
    have hh := (htQ.2.mul hLQ).mul hz
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [hQ.eventually_gt_atTop 1, hP.eventually_gt_atTop 0] with x hq hp
    dsimp [Q, P, L]
    field_simp [(by linarith : Q x ≠ 0), (Real.log_pos hq).ne',
      (Real.sqrt_pos.mpr hp).ne']
  have hthird := third_mass_negligible m lambda hm hlambda hrecord hP
  have hEsecond : Tendsto (fun x => L x * (E x / Real.sqrt (P x) - Real.sqrt 2))
      l (𝓝 (-Real.sqrt 2 * Real.log 2 / 2)) := by
    have hh := (hzD.add hthetaError).add hthird
    simp only [add_zero] at hh
    apply hh.congr
    intro x
    have hmass := record_log_mass (hm x) (hlambda x) (hrecord x)
    change E x = Chebyshev.theta (Q x) + strict_inventory_third_layer_mass (m x) at hmass
    rw [hmass]
    ring
  have hE : Tendsto (fun x => E x / Real.sqrt (P x)) l (𝓝 (Real.sqrt 2)) := by
    have hh : Tendsto (fun x => E x / Real.sqrt (P x) - Real.sqrt 2) l (𝓝 0) := by
      apply (hEsecond.div_atTop hL).congr'
      filter_upwards [hL.eventually_gt_atTop 0] with x hx
      exact mul_div_cancel_left₀ _ hx.ne'
    simpa only [sub_add_cancel, zero_add] using hh.add_const (Real.sqrt 2)
  have hsmall : Tendsto (fun x => L x / Real.sqrt (P x)) l (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, pow_one] using
      log_power_small hP 1 (by norm_num : (0 : ℝ) < 1 / 2)
  have hErelative : Tendsto (fun x => L x * E x / P x) l (𝓝 0) := by
    have hh := hE.mul hsmall
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hp
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hp.le]
    ring
  have htP := theta_unit hP
  have hXrelative : Tendsto (fun x => L x * (X x / P x - 1)) l (𝓝 0) := by
    have hh := htP.2.add hErelative
    simp only [add_zero] at hh
    apply hh.congr
    intro x
    dsimp [E, X]
    ring
  exact ⟨hE, hEsecond, unit_of_scaled hL hXrelative⟩

/-- Both nonlinear tangent endpoints have the same second coefficient.
This pays the clock remainder at sqrt(P)*log(P)^2 without assuming a Taylor
estimate or suppressing the theta(P)-P oscillation. -/
private theorem record_clock_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      (Real.sqrt (largestPrime (m x) : ℝ) * Real.log (largestPrime (m x) : ℝ) *
        (Real.log (Real.log (Real.log (m x : ℝ))) -
          Real.log (Real.log (Chebyshev.theta (largestPrime (m x) : ℝ)))) -
        Real.sqrt 2) + Real.sqrt 2 * Real.log 2 / 2) l (𝓝 0) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let L : α → ℝ := fun x => Real.log (P x)
  let X : α → ℝ := fun x => Real.log (m x : ℝ)
  let th : α → ℝ := fun x => Chebyshev.theta (P x)
  let E : α → ℝ := fun x => X x - th x
  let B (y : α → ℝ) : α → ℝ := fun x => P x * L x / (y x * Real.log (y x))
  let clk : α → ℝ := fun x => Real.log (Real.log (X x)) - Real.log (Real.log (th x))
  let k : ℝ := Real.sqrt 2
  let d : ℝ := k * Real.log 2 / 2
  have hL : Tendsto L l atTop := Real.tendsto_log_atTop.comp hP
  obtain ⟨hE, hED, hXunit⟩ := record_mass_limits m lambda hm hlambda hrecord hP
  obtain ⟨hX, _, hBX⟩ := relative_clocks hP hXunit
  obtain ⟨hth, _, hBth⟩ := relative_clocks hP (theta_unit hP)
  have hlo : Tendsto (fun x => L x * ((E x / Real.sqrt (P x)) * B X x - k) + d)
      l (𝓝 0) := by
    have hh := (second_mul_unit hL hED hBX).add_const d
    convert hh using 1 <;> dsimp [d, k] <;> ring
  have hhi : Tendsto (fun x => L x * ((E x / Real.sqrt (P x)) * B th x - k) + d)
      l (𝓝 0) := by
    have hh := (second_mul_unit hL hED hBth).add_const d
    convert hh using 1 <;> dsimp [d, k] <;> ring
  have hE0 (x : α) : 0 ≤ E x := by
    have hmass := record_log_mass (hm x) (hlambda x) (hrecord x)
    have htheta0 : 0 ≤ Chebyshev.theta (layerPrime (m x) 2 : ℝ) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact sum_nonneg fun p _ => Real.log_natCast_nonneg p
    dsimp [E, X, th, P]
    rw [hmass]
    exact add_nonneg htheta0 (record_third_mass_bound (hm x) (hlambda x) (hrecord x)).1
  have hnorm (y : α → ℝ) : ∀ᶠ x in l,
      (E x / Real.sqrt (P x)) * B y x =
        Real.sqrt (P x) * L x * (E x / (y x * Real.log (y x))) := by
    filter_upwards [hP.eventually_gt_atTop 0] with x hp
    dsimp [B]
    have hs : Real.sqrt (P x) ^ 2 = P x := Real.sq_sqrt hp.le
    have he : (E x * P x) / Real.sqrt (P x) = E x * Real.sqrt (P x) := by
      apply (div_eq_iff (Real.sqrt_pos.mpr hp).ne').mpr
      calc
        E x * P x = E x * Real.sqrt (P x) ^ 2 := by rw [hs]
        _ = (E x * Real.sqrt (P x)) * Real.sqrt (P x) := by ring
    calc
      (E x / Real.sqrt (P x)) * (P x * L x / (y x * Real.log (y x))) =
          ((E x * P x) / Real.sqrt (P x)) * (L x / (y x * Real.log (y x))) := by ring
      _ = _ := by rw [he]; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hth.eventually_gt_atTop 1, hP.eventually_gt_atTop 1,
      hnorm X] with x ht hp hid
    have hb := (clock_bracket ht (hE0 x)).1
    have hsum : th x + E x = X x := by dsimp [E]; ring
    rw [hsum] at hb
    change E x / (X x * Real.log (X x)) ≤ clk x at hb
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.sqrt_nonneg (P x)) (Real.log_pos hp).le)
    have hsub := sub_le_sub_right hmul k
    have hscale := mul_le_mul_of_nonneg_left hsub (Real.log_pos hp).le
    have hadd := add_le_add_right hscale d
    simpa [clk, L, P, th, d, k, add_comm, add_left_comm, add_assoc] using hadd
  · filter_upwards [hth.eventually_gt_atTop 1, hP.eventually_gt_atTop 1,
      hnorm th] with x ht hp hid
    have hb := (clock_bracket ht (hE0 x)).2
    have hsum : th x + E x = X x := by dsimp [E]; ring
    rw [hsum] at hb
    change clk x ≤ E x / (th x * Real.log (th x)) at hb
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.sqrt_nonneg (P x)) (Real.log_pos hp).le)
    have hsub := sub_le_sub_right hmul k
    have hscale := mul_le_mul_of_nonneg_left hsub (Real.log_pos hp).le
    have hadd := add_le_add_right hscale d
    simpa [clk, L, P, th, d, k, add_comm, add_left_comm, add_assoc] using hadd

private theorem complete_tail_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      (Real.sqrt (largestPrime (m x) : ℝ) * Real.log (largestPrime (m x) : ℝ) *
        tail (m x) - Real.sqrt 2) + Real.sqrt 2 * (2 + Real.log 2 / 2)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨T, _, hT⟩ := CompleteTailSecondOrder.price_record_complete_tail_second_order
    epsilon hepsilon
  filter_upwards [hP.eventually_ge_atTop T] with x hx
  simpa only [Real.dist_eq, sub_zero] using
    hT (m x) (hm x) (lambda x) (hlambda x) (hrecord x) hx

private theorem full_correction_P_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      (Real.sqrt (largestPrime (m x) : ℝ) * Real.log (largestPrime (m x) : ℝ) *
        correction (m x) - 2 * Real.sqrt 2) + Real.sqrt 2 * (2 + Real.log 2))
      l (𝓝 0) := by
  have hh := (complete_tail_limit m lambda hm hlambda hrecord hP).add
    (record_clock_limit m lambda hm hlambda hrecord hP)
  simp only [add_zero] at hh
  apply hh.congr
  intro x
  dsimp [correction]
  ring

/-- The second-order transport uses X/P=1+o(1/log(P)), not X-P=O(sqrt(P)). -/
private theorem full_correction_X_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (Real.log (m x : ℝ)) *
      (Real.sqrt (Real.log (m x : ℝ)) * Real.log (Real.log (m x : ℝ)) *
        correction (m x) - 2 * Real.sqrt 2) + Real.sqrt 2 * (2 + Real.log 2))
      l (𝓝 0) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let L : α → ℝ := fun x => Real.log (P x)
  let X : α → ℝ := fun x => Real.log (m x : ℝ)
  let W : α → ℝ := fun x => Real.sqrt (P x) * L x * correction (m x)
  let a : ℝ := 2 * Real.sqrt 2
  let d : ℝ := Real.sqrt 2 * (2 + Real.log 2)
  have hL : Tendsto L l atTop := Real.tendsto_log_atTop.comp hP
  have hPsecond : Tendsto (fun x => L x * (W x - a)) l (𝓝 (-d)) := by
    simpa [W, L, a, d, add_sub_cancel_right, zero_sub] using
      (full_correction_P_limit m lambda hm hlambda hrecord hP).sub_const d
  have hXu := (record_mass_limits m lambda hm hlambda hrecord hP).2.2
  obtain ⟨hX, hlog, _⟩ := relative_clocks hP hXu
  have hfactor := unit_mul (unit_sqrt hXu) hlog
  have hnorm : ∀ᶠ x in l,
      W x * (Real.sqrt (X x / P x) * (Real.log (X x) / L x)) =
        Real.sqrt (X x) * Real.log (X x) * correction (m x) := by
    filter_upwards [hP.eventually_gt_atTop 1, hX.eventually_gt_atTop 0] with x hp hx
    rw [Real.sqrt_div hx.le]
    dsimp [W, L, P, X]
    field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < P x)).ne',
      (Real.log_pos hp).ne']
  have htransport := second_mul_unit hL hPsecond hfactor
  have houter := htransport.mul hlog.1
  simp only [mul_one] at houter
  have hh := houter.add_const d
  simp only [neg_add_cancel] at hh
  apply hh.congr'
  filter_upwards [hnorm, hL.eventually_gt_atTop 0] with x hx hl
  rw [hx]
  dsimp [L, X, P, a, d]
  have hlogP : Real.log (largestPrime (m x) : ℝ) ≠ 0 := by
    simpa [L, P] using hl.ne'
  field_simp [hlogP] <;> ring

/-- A single threshold, chosen before m and lambda, controls BOTH complete
second-order normalizations and the actual positive-log domains. -/
theorem price_record_full_arithmetic_correction_second_order
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      1 < Chebyshev.theta (largestPrime m : ℝ) ∧ 1 < Real.log (m : ℝ) ∧
      (let P : ℝ := largestPrime m
       let X := Real.log (m : ℝ)
       let C := tail m + Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta P))
       |Real.log P * (Real.sqrt P * Real.log P * C - 2 * Real.sqrt 2) +
         Real.sqrt 2 * (2 + Real.log 2)| < epsilon ∧
       |Real.log X * (Real.sqrt X * Real.log X * C - 2 * Real.sqrt 2) +
         Real.sqrt 2 * (2 + Real.log 2)| < epsilon) := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ n : ℕ, 0 < n → n < v.1 →
      goldenResourceObjective v.2 n < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let lambda : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  have htheta := (relative_clocks hP (theta_unit hP)).1
  have hX := (relative_clocks hP
    (record_mass_limits m lambda (fun x => x.2.1) (fun x => x.2.2.1)
      (fun x => x.2.2.2) hP).2.2).1
  have hfirst := (Metric.tendsto_nhds.mp
    (full_correction_P_limit m lambda (fun x => x.2.1) (fun x => x.2.2.1)
      (fun x => x.2.2.2) hP)) epsilon hepsilon
  have hsecond := (Metric.tendsto_nhds.mp
    (full_correction_X_limit m lambda (fun x => x.2.1) (fun x => x.2.2.1)
      (fun x => x.2.2.2) hP)) epsilon hepsilon
  have hall := (htheta.eventually_gt_atTop 1).and
    ((hX.eventually_gt_atTop 1).and (hfirst.and hsecond))
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn lam hlam hrecord hlarge
  let x : S := ⟨(n, lam), hn, hlam, hrecord⟩
  have hx := hT (largestPrime n : ℝ) ((le_max_left T 2).trans hlarge) x rfl
  simpa only [Real.dist_eq, sub_zero, correction, P, m] using hx

/-- Finite envelope for the actual log integer. Used only to convert a uniform
P-threshold into a uniform X-threshold; this does not assume P and X are close. -/
theorem record_log_envelope {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    Real.log (m : ℝ) ≤ (largestPrime m : ℝ) *
      Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
  classical
  have hP2 : 2 ≤ largestPrime m := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    exact hp.two_le.trans (le_sup (f := id)
      (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩))
  have hB : 0 ≤ Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
    apply Real.log_nonneg
    have hp : (2 : ℝ) ≤ largestPrime m := by exact_mod_cast hP2
    nlinarith
  have hcard : (m.primeFactors.card : ℝ) ≤ (largestPrime m : ℝ) := by
    have hh : m.primeFactors ⊆ Ioc 0 (largestPrime m) := by
      intro p hp
      exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos, le_sup (f := id) hp⟩
    exact_mod_cast (by simpa using card_le_card hh : m.primeFactors.card ≤ largestPrime m)
  have hterm (p : ℕ) (hp : p ∈ m.primeFactors) :
      (m.factorization p : ℝ) * Real.log p ≤ Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hh := PrimePowerEnvelope.price_record_prime_power_envelope hm hlambda.le
      hrecord p hprime (Nat.dvd_of_mem_primeFactors hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpow : (p : ℝ) ^ m.factorization p < 4 * (largestPrime m : ℝ) ^ 2 := by
      exact_mod_cast hh
    simpa only [Real.log_pow] using (Real.log_lt_log (pow_pos hp0 _) hpow).le
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  calc
    _ ≤ (m.primeFactors.card : ℝ) * Real.log (4 * (largestPrime m : ℝ) ^ 2) := by
      simpa only [nsmul_eq_mul] using sum_le_card_nsmul m.primeFactors
        (fun p => (m.factorization p : ℝ) * Real.log p)
        (Real.log (4 * (largestPrime m : ℝ) ^ 2)) hterm
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

/-- The identical law with an X=log(m) threshold, matching the actual clock
in uniform_min_tail_robin_second_order_lower. That LOWER theorem is not used
as a two-sided supplier anywhere in this file. -/
theorem price_record_full_arithmetic_correction_second_order_X
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ X0 : ℝ, 1 < X0 ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      X0 ≤ Real.log (m : ℝ) →
      1 < Chebyshev.theta (largestPrime m : ℝ) ∧
      (let X := Real.log (m : ℝ)
       let L := Real.log X
       |L * (Real.sqrt X * L *
         (tail m + Real.log (Real.log X) -
           Real.log (Real.log (Chebyshev.theta (largestPrime m : ℝ)))) - 2 * Real.sqrt 2) +
           Real.sqrt 2 * (2 + Real.log 2)| < epsilon) := by
  obtain ⟨T, hT1, hT⟩ := price_record_full_arithmetic_correction_second_order epsilon hepsilon
  let B : ℝ := max T 2
  have hB2 : 2 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < Real.log (4 * B ^ 2) := Real.log_pos (by nlinarith)
  refine ⟨B * Real.log (4 * B ^ 2) + 2, by nlinarith [mul_pos hB0 hlogB], ?_⟩
  intro m hm lambda hlambda hrecord hX
  have hP0 : (0 : ℝ) ≤ largestPrime m := Nat.cast_nonneg _
  have hlarge : T ≤ (largestPrime m : ℝ) := by
    by_contra! hsmall
    have hpB : (largestPrime m : ℝ) ≤ B := hsmall.le.trans (le_max_left _ _)
    have hp2 : 2 ≤ largestPrime m := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      exact hp.two_le.trans (le_sup (f := id)
        (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩))
    have hpR : (2 : ℝ) ≤ largestPrime m := by exact_mod_cast hp2
    have hlogle : Real.log (4 * (largestPrime m : ℝ) ^ 2) ≤ Real.log (4 * B ^ 2) :=
      Real.log_le_log (by positivity)
        (by nlinarith [pow_le_pow_left₀ hP0 hpB 2])
    have hmass := record_log_envelope hm hlambda hrecord
    have hbounded : Real.log (m : ℝ) ≤ B * Real.log (4 * B ^ 2) := hmass.trans
      ((mul_le_mul_of_nonneg_left hlogle hP0).trans
        (mul_le_mul_of_nonneg_right hpB hlogB.le))
    linarith
  obtain ⟨htheta, _, _, hsecond⟩ := hT m hm lambda hlambda hrecord hlarge
  exact ⟨htheta, hsecond⟩


/-- Nonvacuity/sharpness: genuine positive-price LITERAL records occur with
arbitrarily large largest prime. The optimizer is used here only to construct
witnesses, never to replace an arbitrary m in the universal asymptotic. -/
theorem arbitrarily_large_price_records (T : ℝ) :
    ∃ m : ℕ, ∃ lambda : ℝ, 2 ≤ m ∧ 0 < lambda ∧
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) ∧
      T < (largestPrime m : ℝ) := by
  let N := max ⌈T⌉₊ 2
  obtain ⟨p, hp, hNp, _⟩ := Nat.exists_prime_lt_and_le_two_mul N (by dsimp [N]; omega)
  have hTP : T < (p : ℝ) := by
    have hTN : T ≤ (N : ℝ) := (Nat.le_ceil T).trans (by
      exact_mod_cast le_max_left ⌈T⌉₊ 2)
    exact hTN.trans_lt (by exact_mod_cast hNp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have hratio : (1 - (p : ℝ)⁻¹ ^ (1 + 1)) / (1 - (p : ℝ)⁻¹ ^ 1) =
      1 + (p : ℝ)⁻¹ := by
    norm_num only [pow_one]
    apply (div_eq_iff hden.ne').mpr
    ring
  have hgain : 0 < goldenLayerMarginal p 1 := by
    rw [goldenLayerMarginal, hratio]
    exact div_pos (Real.log_pos (by linarith)) hp.log_pos
  let lambda := goldenLayerMarginal p 1 / 2
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hactive : lambda < goldenLayerMarginal p 1 := by dsimp [lambda]; linarith
  obtain ⟨m, hm, hcounts, hopt, hleast⟩ :=
    D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount.optimal_layer_count_spec hlambda
  have hv : 1 ≤ m.factorization p := by
    rw [hcounts]
    have hmem : (1 : ℕ) ∈ {k : ℕ | 1 ≤ k ∧ p.Prime ∧
        lambda < goldenLayerMarginal p k} := ⟨le_rfl, hp, hactive⟩
    rw [D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount.positive_layers_eq_count_interval
      hlambda hp] at hmem
    exact hmem.2
  have hpd : p ∣ m := (hp.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr hv
  have hm2 : 2 ≤ m := hp.two_le.trans (Nat.le_of_dvd (by omega : 0 < m) hpd)
  have hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m := by
    intro n hn hnm
    have hle := hopt n (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hnopt : D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion.IsGoldenResourceOptimal
        lambda n := by
      intro k hk
      rw [heq]
      exact hopt k hk
    have hd := hleast n (by omega) hnopt
    exact (Nat.le_of_dvd hn hd).not_gt hnm
  refine ⟨m, lambda, hm2, hlambda, hrecord, ?_⟩
  have hm0 : m ≠ 0 := by omega
  have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hm0⟩
  exact hTP.trans_le (by exact_mod_cast (le_sup (f := id) hmem))

/-- Only the Q2 coefficient needed by the complete residual proof. This helper is
consumed by ActualRecordHigherLayerResidual.actual_record_critical_residual.
The inverse/square-root rate and second-coefficient calculus are the original
private suppliers above; no standalone own-log module is introduced. -/
theorem record_second_own_clock_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (Real.log (m x : ℝ)) *
      ((layerPrime (m x) 2 : ℝ) / Real.sqrt (Real.log (m x : ℝ)) - Real.sqrt 2))
      l (𝓝 (-Real.log 2 / Real.sqrt 2)) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let X : α → ℝ := fun x => Real.log (m x : ℝ)
  let Q : α → ℝ := fun x => layerPrime (m x) 2
  let a : ℝ := Real.sqrt 2
  have ha : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hLP : Tendsto (fun x => Real.log (P x)) l atTop := Real.tendsto_log_atTop.comp hP
  have hXu := (record_mass_limits m lambda hm hlambda hrecord hP).2.2
  obtain ⟨hX, hlogs, _⟩ := relative_clocks hP hXu
  have hsqrtUnit : UnitRate l (fun x => Real.log (P x))
      (fun x => Real.sqrt (P x) / Real.sqrt (X x)) := by
    apply unit_congr (unit_sqrt (unit_inv hXu))
    filter_upwards [hP.eventually_gt_atTop 0] with x hp
    simp only [inv_div]
    exact Real.sqrt_div hp.le (X x)
  have hsecond := (second_layer_limits m lambda hm hlambda hrecord hP).2.2.2
  have htransport := second_mul_unit hLP hsecond hsqrtUnit
  have hout := hlogs.1.mul htransport
  simp only [one_mul] at hout
  have hb : -a * Real.log 2 / 2 = -Real.log 2 / a := by
    field_simp [ha.ne']
    nlinarith [congrArg (fun z : ℝ => Real.log 2 * z) ha2]
  change Tendsto _ l (𝓝 (-a * Real.log 2 / 2)) at hout
  rw [hb] at hout
  apply hout.congr'
  filter_upwards [hP.eventually_gt_atTop 1, hX.eventually_gt_atTop 0] with x hp hx
  have hp0 : 0 < P x := by linarith
  change (Real.log (X x) / Real.log (P x)) * (Real.log (P x) *
    (Q x / Real.sqrt (P x) * (Real.sqrt (P x) / Real.sqrt (X x)) - a)) =
    Real.log (X x) * (Q x / Real.sqrt (X x) - a)
  have hlogP : Real.log (P x) ≠ 0 := (Real.log_pos hp).ne'
  field_simp [hlogP, (Real.sqrt_pos.mpr hp0).ne'] <;> ring

end D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
