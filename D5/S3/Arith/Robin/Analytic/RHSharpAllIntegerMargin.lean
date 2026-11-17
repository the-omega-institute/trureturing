/- GID: D5/S3/Arith/Robin/Analytic/RHSharpAllIntegerMargin
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RHSharpAllIntegerMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: RH-only sharp integer margins, original-record attainment and real liminf. -/

import D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-! Sharp all-integer Robin margins under RH.

The proof uses the public original-record endpoint and the identical arithmetic
correction in both public second-order estimates. The classical all-integer
lower constant is attributed to Musin, citing Ramanujan and Robin; exact equality
also uses the genuine original-record endpoint. No rate, LI, novelty, RH proof
or explicit finite 5040 cutoff is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Finset
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D)
open D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
  (K original_record_sharp_lower_endpoint)
open D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
  (price_record_full_arithmetic_correction_second_order)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_split)

namespace D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin

def F (n : ℕ) : ℝ := D (Real.log (n : ℝ)) * robinLogMargin n

def T (n : ℕ) : ℝ :=
  (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) -
    (ArithmeticFunction.sigma 1 n : ℝ) / n) * Real.sqrt (Real.log (n : ℝ))

private abbrev price (a : ℝ) : ℝ := 1 / (a * Real.log a)
private abbrev E : ℝ := Real.exp Real.eulerMascheroniConstant
private abbrev C := PriceRecord.FullArithmeticCorrectionSecondOrder.correction

private lemma D_pos {a : ℝ} (ha : 1 < a) : 0 < D a :=
  mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos ha)

private lemma D_atTop : Tendsto D atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max B 0)] with x hx hl
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hl0 : 0 ≤ Real.log x := (le_max_right _ _).trans hl
  have hh := mul_le_mul_of_nonneg_right hs hl0
  dsimp [D]
  linarith [(le_max_left B 0).trans hl]

private lemma D_ratio {α : Type*} {l : Filter α} {x y : α → ℝ}
    (hx : Tendsto x l atTop) (hy : Tendsto y l atTop)
    (hr : Tendsto (fun v => y v / x v) l (𝓝 1)) :
    Tendsto (fun v => D (y v) / D (x v)) l (𝓝 1) := by
  have hlog : Tendsto (fun v => Real.log (y v / x v)) l (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have hlratio : Tendsto (fun v => Real.log (y v) / Real.log (x v)) l (𝓝 1) := by
    have hh := (hlog.div_atTop (Real.tendsto_log_atTop.comp hx)).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [hx.eventually_gt_atTop 1, hy.eventually_gt_atTop 1] with v hvx hvy
    dsimp only [Function.comp_def]
    rw [Real.log_div (by linarith : y v ≠ 0) (by linarith : x v ≠ 0)]
    field_simp [(Real.log_pos hvx).ne']
    <;> ring
  have hh := hr.sqrt.mul hlratio
  simp only [Real.sqrt_one, one_mul] at hh
  apply hh.congr'
  filter_upwards [hx.eventually_gt_atTop 1, hy.eventually_gt_atTop 1] with v hvx hvy
  rw [Real.sqrt_div (by linarith : 0 ≤ y v)]
  dsimp [D]
  field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < x v)).ne',
    (Real.log_pos hvx).ne']
  <;> ring

private lemma largestPrime_le {m : ℕ} (hm : 0 < m) : largestPrime m ≤ m := by
  change m.primeFactors.sup id ≤ m
  apply Finset.sup_le
  intro p hp
  exact Nat.le_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)

/-- A fixed public second-order error bound suffices when its log clock
diverges. Both applications below retain the identical correction C(m). -/
private lemma leading_of_second_order_bound {α : Type*} {l : Filter α}
    {x z : α → ℝ} (hx : Tendsto x l atTop)
    (hbound : ∀ᶠ v in l,
      |Real.log (x v) * (z v - 2 * Real.sqrt 2) +
        Real.sqrt 2 * (2 + Real.log 2)| < 1) :
    Tendsto z l (𝓝 (2 * Real.sqrt 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let d : ℝ := Real.sqrt 2 * (2 + Real.log 2)
  filter_upwards [hbound, (Real.tendsto_log_atTop.comp hx).eventually_gt_atTop
    (max 0 ((1 + |d|) / ε))] with v hb hl
  have hL : 0 < Real.log (x v) := (le_max_left _ _).trans_lt hl
  have htriangle : |Real.log (x v) * (z v - 2 * Real.sqrt 2)| < 1 + |d| := by
    have hh := abs_sub (Real.log (x v) * (z v - 2 * Real.sqrt 2) + d) d
    rw [add_sub_cancel_right] at hh
    change |Real.log (x v) * (z v - 2 * Real.sqrt 2) + d| < 1 at hb
    linarith
  rw [abs_mul, abs_of_pos hL] at htriangle
  have hsmall : (1 + |d|) / ε < Real.log (x v) :=
    (le_max_right _ _).trans_lt hl
  have hZ : 1 + |d| < ε * Real.log (x v) := by
    have hh := (div_lt_iff₀ hε).mp hsmall
    nlinarith
  rw [Real.dist_eq]
  nlinarith [htriangle.trans hZ]

private lemma record_clocks {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x k, 0 < k → k < m x →
      goldenResourceObjective (lambda x) k < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x => Real.log (m x : ℝ)) l atTop ∧
    Tendsto (fun x => D (Real.log (m x : ℝ)) / D (largestPrime (m x) : ℝ))
      l (𝓝 1) := by
  -- m >= P pays log(m) -> infinity without a raw log(m)/P limit.
  have hb : Tendsto (fun x => Real.log (m x : ℝ)) l atTop := by
    rw [tendsto_atTop]
    intro B
    filter_upwards [(Real.tendsto_log_atTop.comp hP).eventually_ge_atTop B,
      hP.eventually_gt_atTop 0] with x hx hp
    have hPm : (largestPrime (m x) : ℝ) ≤ m x := by
      exact_mod_cast largestPrime_le (by have := hm x; omega)
    exact hx.trans (Real.log_le_log hp hPm)
  obtain ⟨P0, _, hfull⟩ :=
    price_record_full_arithmetic_correction_second_order 1 zero_lt_one
  have hbound : ∀ᶠ x in l,
      |Real.log (largestPrime (m x) : ℝ) *
        (D (largestPrime (m x) : ℝ) * C (m x) - 2 * Real.sqrt 2) +
        Real.sqrt 2 * (2 + Real.log 2)| < 1 ∧
      |Real.log (Real.log (m x : ℝ)) *
        (D (Real.log (m x : ℝ)) * C (m x) - 2 * Real.sqrt 2) +
        Real.sqrt 2 * (2 + Real.log 2)| < 1 := by
    filter_upwards [hP.eventually_ge_atTop P0] with x hx
    have hh := hfull (m x) (hm x) (lambda x) (hlambda x) (hrecord x) hx
    simpa only [D, C, PriceRecord.FullArithmeticCorrectionSecondOrder.correction]
      using hh.2.2
  have hPC : Tendsto (fun x => D (largestPrime (m x) : ℝ) * C (m x))
      l (𝓝 (2 * Real.sqrt 2)) :=
    leading_of_second_order_bound hP (hbound.mono (fun _ hx => hx.1))
  have hbC : Tendsto (fun x => D (Real.log (m x : ℝ)) * C (m x))
      l (𝓝 (2 * Real.sqrt 2)) :=
    leading_of_second_order_bound hb (hbound.mono (fun _ hx => hx.2))
  have hc : 0 < 2 * Real.sqrt 2 := by positivity
  -- Pay nonvanishing of the actual shared factor before cancelling it.
  have hCne : ∀ᶠ x in l, C (m x) ≠ 0 := by
    filter_upwards [hPC.eventually_const_lt hc] with x hx
    intro hzero
    rw [hzero, mul_zero] at hx
    exact (lt_irrefl 0) hx
  have hquot := hbC.div hPC hc.ne'
  simp only [div_self hc.ne'] at hquot
  refine ⟨hb, hquot.congr' ?_⟩
  filter_upwards [hCne] with x hx
  exact mul_div_mul_right (D (Real.log (m x : ℝ)))
    (D (largestPrime (m x) : ℝ)) hx

private structure Contact where
  a : ℝ
  m : ℕ
  ha : 1 < a
  hm : 2 ≤ m
  hb : 1 < Real.log (m : ℝ)
  counts : ∀ p : ℕ, p.Prime → m.factorization p = optimalLayerCount (price a) p
  optimal : IsGoldenResourceOptimal (price a) m
  record : ∀ k : ℕ, 0 < k → k < m →
    goldenResourceObjective (price a) k < goldenResourceObjective (price a) m

private lemma contact_exists : ∃ A : ℝ, ∀ a : ℝ, A ≤ a → ∃ x : Contact, x.a = a := by
  obtain ⟨A, hA, hgrowth⟩ :=
    EulerLayerInventoryGrowth.strict_inventory_uniform_growth (1 / 2) (by norm_num)
  refine ⟨max A 4, ?_⟩
  intro a ha
  have haA : A ≤ a := (le_max_left _ _).trans ha
  have ha4 : 4 ≤ a := (le_max_right _ _).trans ha
  have ha1 : 1 < a := by linarith
  have hp : 0 < price a := one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ha1))
  obtain ⟨m, hm, hc, ho, hleast⟩ := optimal_layer_count_spec hp
  have hg := hgrowth a haA m (by omega) (fun p _ => hc p)
  have hb : 1 < Real.log (m : ℝ) := by
    have hh := (lt_div_iff₀ (by linarith : 0 < a)).mp (by
      linarith [(abs_lt.mp hg).1] : (1 / 2 : ℝ) < Real.log (m : ℝ) / a)
    linarith
  have hm2 : 2 ≤ m := by
    by_contra! h
    have he : m = 1 := by omega
    simp [he] at hb
    norm_num at hb
  have hr : ∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective (price a) k < goldenResourceObjective (price a) m := by
    intro k hk hkm
    have hle := ho k (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hkopt : IsGoldenResourceOptimal (price a) k := by
      intro j hj
      rw [heq]
      exact ho j hj
    exact (Nat.le_of_dvd hk (hleast k (by omega) hkopt)).not_gt hkm
  exact ⟨⟨a, m, ha1, hm2, hb, (fun p _ => hc p), ho, hr⟩, rfl⟩

private lemma contact_limits :
    let l : Filter Contact := comap Contact.a atTop
    Tendsto (fun x => (largestPrime x.m : ℝ)) l atTop ∧
    Tendsto (fun x => D x.a / D (largestPrime x.m : ℝ)) l (𝓝 1) := by
  let l : Filter Contact := comap Contact.a atTop
  have ha : Tendsto Contact.a l atTop := tendsto_comap
  have hba : Tendsto (fun x : Contact => Real.log (x.m : ℝ) / x.a) l (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨A, _, hg⟩ := EulerLayerInventoryGrowth.strict_inventory_uniform_growth ε hε
    filter_upwards [ha.eventually_ge_atTop A] with x hx
    simpa only [Real.dist_eq] using hg x.a hx x.m (by have := x.hm; omega) x.counts
  have hprice : Tendsto (fun x : Contact => price x.a) l (𝓝 0) := by
    have hprod : Tendsto (fun x : Contact => x.a * Real.log x.a) l atTop := by
      rw [tendsto_atTop]
      intro B
      filter_upwards [ha.eventually_ge_atTop (max B 0),
        (Real.tendsto_log_atTop.comp ha).eventually_ge_atTop 1] with x hx hl
      dsimp only [Function.comp_def] at hl
      have h0 : 0 ≤ x.a := (le_max_right _ _).trans hx
      have hh := mul_le_mul_of_nonneg_left hl h0
      linarith [(le_max_left B 0).trans hx]
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hprod
  have hP : Tendsto (fun x : Contact => (largestPrime x.m : ℝ)) l atTop := by
    rw [tendsto_atTop]
    intro Y
    obtain ⟨p, hpY, hp⟩ := Nat.exists_infinite_primes ⌈Y⌉₊
    have hgain : 0 < goldenLayerMarginal p 1 := by
      rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
      have hi : 0 < 1 / (p : ℝ) := one_div_pos.mpr (by exact_mod_cast hp.pos)
      exact div_pos (Real.log_pos (by linarith)) hp.log_pos
    filter_upwards [hprice.eventually_lt_const hgain] with x hx
    have hv : 1 ≤ x.m.factorization p := by
      rw [x.counts p hp]
      have hmem : (1 : ℕ) ∈ {k : ℕ | 1 ≤ k ∧ p.Prime ∧
          price x.a < goldenLayerMarginal p k} := ⟨le_rfl, hp, hx⟩
      rw [positive_layers_eq_count_interval
        (one_div_pos.mpr (mul_pos (by linarith [x.ha]) (Real.log_pos x.ha))) hp] at hmem
      exact hmem.2
    have hm0 : x.m ≠ 0 := by have := x.hm; omega
    have hpd : p ∣ x.m := (hp.dvd_iff_one_le_factorization hm0).mpr hv
    have hpmem := Nat.mem_primeFactors.mpr ⟨hp, hpd, hm0⟩
    have hpP : p ≤ largestPrime x.m := Finset.le_sup (f := id) hpmem
    exact (Nat.le_ceil Y).trans ((by exact_mod_cast hpY : (⌈Y⌉₊ : ℝ) ≤ p).trans
      (by exact_mod_cast hpP))
  have hcl := record_clocks
    (fun x : Contact => x.m) (fun x => price x.a) (fun x => x.hm)
    (fun x => one_div_pos.mpr (mul_pos (by linarith [x.ha]) (Real.log_pos x.ha)))
    (fun x => x.record) hP
  have hDbDa := D_ratio ha hcl.1 hba
  have haP : Tendsto (fun x : Contact => D x.a / D (largestPrime x.m : ℝ))
      l (𝓝 1) := by
    -- (D(b)/D(P))/(D(b)/D(a)) = D(a)/D(P), with all domains paid.
    have hh := hcl.2.div hDbDa (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 1] with x hx
    change (D (Real.log (x.m : ℝ)) / D (largestPrime x.m : ℝ)) /
      (D (Real.log (x.m : ℝ)) / D x.a) = D x.a / D (largestPrime x.m : ℝ)
    field_simp [(D_pos x.ha).ne', (D_pos x.hb).ne', (D_pos hx).ne']
    <;> ring
  exact ⟨hP, haP⟩

private lemma defect_comparison (x : Contact) {n : ℕ} (hn : 0 < n)
    (ha : Real.log (n : ℝ) = x.a) : robinLogMargin x.m ≤ robinLogMargin n := by
  let a := x.a
  let b := Real.log (x.m : ℝ)
  have hconc : 0 ≤ Real.log (Real.log a) - Real.log (Real.log b) - price a * (a - b) := by
    by_cases he : a = b
    · simp [he]
    · have hh := RestrictedDivisorStrictInventory.loglog_tangent x.ha x.hb he
      change Real.log (Real.log b) - Real.log (Real.log a) <
        (b - a) * (1 / (a * Real.log a)) at hh
      nlinarith
  have hopt := x.optimal n (by omega)
  have hid : robinLogMargin n - robinLogMargin x.m =
      (Real.log (Real.log a) - Real.log (Real.log b) - price a * (a - b)) +
      (goldenResourceObjective (price a) x.m - goldenResourceObjective (price a) n) := by
    rw [golden_resource_sigma_identity (price a) (n := x.m) (by have := x.hm; omega),
      golden_resource_sigma_identity (price a) (n := n) (by omega)]
    dsimp [robinLogMargin, a, b]
    rw [ha]
    ring
  linarith

private lemma log_lower (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, K - ε < F n := by
  let c : ℝ := K - ε / 2
  obtain ⟨P0, _, hrecord⟩ := (original_record_sharp_lower_endpoint hRH).1
    (ε / 2) (by positivity)
  obtain ⟨A0, hexists⟩ := contact_exists
  have hlim := contact_limits
  -- Only the FIXED signed c is multiplied by the near-one ratio. This is
  -- continuity of r*c, equivalently control of |r-1|*|c|, never of r*z.
  have hc : Tendsto (fun x : Contact => (D x.a / D (largestPrime x.m : ℝ)) * c)
      (comap Contact.a atTop) (𝓝 c) := by simpa using hlim.2.mul_const c
  have hall := (hlim.1.eventually_ge_atTop (max P0 2)).and
    (hc.eventually_const_lt (show K - ε < c by dsimp [c]; linarith))
  obtain ⟨A1, hA1⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (max A0 A1), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  obtain ⟨x, hx⟩ := hexists _ ((le_max_left _ _).trans hn)
  have h := hA1 _ ((le_max_right _ _).trans hn) x hx
  have hP2 : (1 : ℝ) < largestPrime x.m := by linarith [(le_max_right P0 2).trans h.1]
  have hDP := D_pos hP2
  have hDa := D_pos x.ha
  have hz := hrecord x.m x.hm (price x.a)
    (one_div_pos.mpr (mul_pos (by linarith [x.ha]) (Real.log_pos x.ha))) x.record
    ((le_max_left _ _).trans h.1)
  have hcomp := defect_comparison x hn0 hx.symm
  have hprod : (D x.a / D (largestPrime x.m : ℝ)) * c <
      D x.a * robinLogMargin x.m := by
    calc
      (D x.a / D (largestPrime x.m : ℝ)) * c <
          (D x.a / D (largestPrime x.m : ℝ)) *
            (D (largestPrime x.m : ℝ) * robinLogMargin x.m) :=
        mul_lt_mul_of_pos_left hz (div_pos hDa hDP)
      _ = D x.a * robinLogMargin x.m := by
        rw [← mul_assoc, div_mul_cancel₀ _ hDP.ne']
  have hbound := mul_le_mul_of_nonneg_left hcomp hDa.le
  have hFn : F n = D x.a * robinLogMargin n := by simp only [F, hx]
  rw [hFn]
  exact h.2.trans (hprod.trans_le hbound)

private lemma log_attainment (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, ∃ lambda : ℝ, N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧ |F m - K| < ε := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ k : ℕ, 0 < k → k < v.1 → goldenResourceObjective v.2 k < goldenResourceObjective v.2 v.1}
  let P : S → ℝ := fun x => largestPrime x.1.1
  let l : Filter S := comap P atTop
  have hcl := record_clocks (fun x : S => x.1.1) (fun x => x.1.2)
    (fun x => x.2.1) (fun x => x.2.2.1) (fun x => x.2.2.2)
    (show Tendsto P l atTop from tendsto_comap)
  let δ := ε / (2 * (|K| + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnear := (Metric.tendsto_nhds.mp hcl.2) δ hδ
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_comap.mp hnear)
  let η := min 1 (ε / 2)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  obtain ⟨m, lambda, hm, hl, hr, hP, _, _, hz⟩ :=
    (original_record_sharp_lower_endpoint hRH).2 η hη (max (max A (N : ℝ)) 2)
  have hP0 : max A (N : ℝ) < (largestPrime m : ℝ) :=
    (le_max_left _ _).trans_lt hP
  let x : S := ⟨(m, lambda), hm, hl, hr⟩
  have hratio : |D (Real.log (m : ℝ)) / D (largestPrime m : ℝ) - 1| < δ := by
    simpa only [Real.dist_eq] using hA (P x) ((le_max_left _ _).trans hP0.le) x rfl
  have hm0 : 0 < m := by omega
  have hNm : N ≤ m := by
    have hNP : (N : ℝ) < largestPrime m := (le_max_right _ _).trans_lt hP0
    have hle : (largestPrime m : ℝ) ≤ m := by exact_mod_cast largestPrime_le hm0
    exact_mod_cast (hNP.trans_le hle).le
  let z := D (largestPrime m : ℝ) * robinLogMargin m
  let r := D (Real.log (m : ℝ)) / D (largestPrime m : ℝ)
  have hz1 : |z| < |K| + 1 := by
    have hh := abs_add_le (z - K) K
    rw [sub_add_cancel] at hh
    have hzη : |z - K| < η := hz
    linarith [min_le_left (1 : ℝ) (ε / 2)]
  have herr : |(r - 1) * z| < ε / 2 := by
    rw [abs_mul]
    have hh := mul_lt_mul_of_pos_right hratio (by positivity : 0 < |K| + 1)
    have hh' : |r - 1| * |z| ≤ |r - 1| * (|K| + 1) :=
      mul_le_mul_of_nonneg_left hz1.le (abs_nonneg _)
    have hδeq : δ * (|K| + 1) = ε / 2 := by
      dsimp [δ]
      field_simp [(by positivity : 0 < |K| + 1).ne']
      <;> ring
    exact hh'.trans_lt (by simpa only [hδeq] using hh)
  have hDP : D (largestPrime m : ℝ) ≠ 0 := by
    exact (D_pos (by linarith [(le_max_right (max A (N : ℝ)) 2).trans_lt hP])).ne'
  have hFm : F m - K = (r - 1) * z + (z - K) := by
    dsimp [F, r, z]
    field_simp [hDP]
    <;> ring
  refine ⟨m, lambda, hNm, hl, hm, hr, ?_⟩
  rw [hFm]
  exact (abs_add_le _ _).trans_lt (by
    have hzε : |z - K| < ε / 2 := hz.trans_le (min_le_right _ _)
    linarith)

private lemma linear_identity {n : ℕ} (hn : 0 < n) (ha : 1 < Real.log (n : ℝ)) :
    T n = E * D (Real.log (n : ℝ)) * (1 - Real.exp (-robinLogMargin n)) := by
  have hz : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (ne_of_gt hn)))
      (Nat.cast_pos.mpr hn)
  have hl := Real.log_pos ha
  have hexp : Real.exp (-robinLogMargin n) =
      ((ArithmeticFunction.sigma 1 n : ℝ) / n) / (E * Real.log (Real.log (n : ℝ))) := by
    rw [show -robinLogMargin n = Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) -
      Real.eulerMascheroniConstant - Real.log (Real.log (Real.log (n : ℝ))) by
        dsimp [robinLogMargin]; ring]
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hz, Real.exp_log hl]
    simp only [E, div_div, mul_assoc]
  rw [hexp]
  dsimp [T, D, E]
  field_simp [hl.ne', (Nat.cast_pos.mpr hn).ne',
    Real.exp_ne_zero Real.eulerMascheroniConstant]

private lemma linear_le_log {n : ℕ} (hn : 0 < n) (ha : 1 < Real.log (n : ℝ)) :
    T n ≤ E * F n := by
  rw [linear_identity hn ha]
  have h := Real.add_one_le_exp (-robinLogMargin n)
  have hh : 1 - Real.exp (-robinLogMargin n) ≤ robinLogMargin n := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh
    (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) (D_pos ha)).le
  simpa only [F, mul_assoc] using hmul

private lemma exponential_proxy (q : ℝ) (hq : 0 < q) :
    Tendsto (fun t : ℝ => t * (1 - Real.exp (-q / t))) atTop (𝓝 q) := by
  have hs : Tendsto (fun d : ℝ => (Real.exp d - 1) / d) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [Real.exp_zero, zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hu : Tendsto (fun t : ℝ => -q / t) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_id.const_div_atTop (-q)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      change -q / t ≠ 0
      exact div_ne_zero (neg_ne_zero.mpr hq.ne') ht.ne'
  have hh := (hs.comp hu).const_mul q
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  change q * ((Real.exp (-q / t) - 1) / (-q / t)) =
    t * (1 - Real.exp (-q / t))
  field_simp [ht.ne', hq.ne']
  <;> ring

private lemma linear_lower (hRH : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, E * K - ε < T n := by
  have hK : 0 < K := by
    have hM : firstLiMass < (1 / 3 : ℝ) := by
      rw [firstLiMass_split]
      have h2 : (2 / 3 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      have h3 : (1 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
      have hp := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) Real.pi_gt_three
      linarith [Real.eulerMascheroniConstant_lt_two_thirds]
    have hs : (4 / 3 : ℝ) < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    dsimp [K]
    linarith
  have hE := Real.exp_pos Real.eulerMascheroniConstant
  obtain ⟨q, hqlo, hqK⟩ := exists_between (show max 0 (K - ε / E) < K by
    apply max_lt_iff.mpr
    exact ⟨hK, by have := div_pos hε hE; linarith⟩)
  have hq : 0 < q := (le_max_left _ _).trans_lt hqlo
  have hqε : E * K - ε < E * q := by
    have hh := (le_max_right _ _).trans_lt hqlo
    have hmul := mul_lt_mul_of_pos_left hh hE
    have hcancel : E * (ε / E) = ε := by field_simp [hE.ne']
    nlinarith
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hproxy : Tendsto (fun n : ℕ => E * (D (Real.log (n : ℝ)) *
      (1 - Real.exp (-q / D (Real.log (n : ℝ)))))) atTop (𝓝 (E * q)) :=
    ((exponential_proxy q hq).comp (D_atTop.comp hlog)).const_mul E
  filter_upwards [log_lower hRH (K - q) (sub_pos.mpr hqK),
    hlog.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ),
    hproxy.eventually_const_lt hqε] with n hFn hn hn0 hp
  have hD := D_pos hn
  have hd : q / D (Real.log (n : ℝ)) < robinLogMargin n := by
    apply (div_lt_iff₀ hD).mpr
    dsimp [F] at hFn
    linarith
  have he : Real.exp (-robinLogMargin n) < Real.exp (-q / D (Real.log (n : ℝ))) := by
    simpa only [neg_div] using Real.exp_lt_exp.mpr (neg_lt_neg hd)
  have hmul := mul_lt_mul_of_pos_left (sub_lt_sub_left he 1) (mul_pos hE hD)
  rw [linear_identity hn0 hn]
  exact hp.trans (by simpa only [mul_assoc] using hmul)

/-- All-integer lower envelopes, simultaneous sharp attainment at actual
strict original records, and paid real liminf equalities. RH is the only
headline hypothesis. The original-record endpoint is a public imported result. -/
theorem all_integer_sharp_margin (hRH : RiemannHypothesis) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K - ε < F n ∧ Real.exp Real.eulerMascheroniConstant * K - ε < T n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |F m - K| < ε ∧ |T m - Real.exp Real.eulerMascheroniConstant * K| < ε) ∧
    Filter.liminf F atTop = K ∧
    Filter.liminf T atTop = Real.exp Real.eulerMascheroniConstant * K := by
  have hlo : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K - ε < F n ∧ E * K - ε < T n := by
    intro ε hε
    exact eventually_atTop.mp ((log_lower hRH ε hε).and (linear_lower hRH ε hε))
  have hatt : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |F m - K| < ε ∧ |T m - E * K| < ε := by
    intro ε hε N
    let η := min ε (ε / (E + 1))
    have hE := Real.exp_pos Real.eulerMascheroniConstant
    have hη : 0 < η := lt_min hε (div_pos hε (by linarith))
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨L, hL⟩ := eventually_atTop.mp
      ((linear_lower hRH ε hε).and (hlog.eventually_gt_atTop 1))
    obtain ⟨m, lambda, hNm, hl, hm, hr, hf⟩ := log_attainment hRH η hη (max N L)
    have hlate := hL m ((le_max_right _ _).trans hNm)
    have hupper := linear_le_log (by omega : 0 < m) hlate.2
    have hEη : E * η < ε := by
      have hmul := (le_div_iff₀ (by linarith : 0 < E + 1)).mp (min_le_right ε (ε / (E + 1)))
      change η * (E + 1) ≤ ε at hmul
      nlinarith
    refine ⟨m, lambda, (le_max_left _ _).trans hNm, hl, hm, hr,
      hf.trans_le (min_le_left _ _), abs_lt.mpr ⟨?_, ?_⟩⟩
    · linarith [hlate.1]
    · have hFupper := (abs_lt.mp hf).2
      have hh := mul_lt_mul_of_pos_left hFupper hE
      nlinarith
  -- atTop on Nat is nonempty. Neither sequence is assumed bounded above:
  -- the lower bound and arbitrarily late upper witnesses pay the two
  -- conditionally-complete-lattice obligations in the accepted pattern.
  have pay (f : ℕ → ℝ) (c : ℝ)
      (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, c - ε < f n)
      (hu : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |f n - c| < ε) :
      Filter.liminf f atTop = c := by
    have hlower (b : ℝ) (hb : b < c) : ∀ᶠ n : ℕ in atTop, b ≤ f n := by
      filter_upwards [hl (c - b) (sub_pos.mpr hb)] with n hn
      linarith
    have hupper (b : ℝ) (hb : c < b) : ∃ᶠ n : ℕ in atTop, f n ≤ b := by
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, he⟩ := hu (b - c) (sub_pos.mpr hb) N
      exact ⟨n, hn, by linarith [(abs_lt.mp he).2]⟩
    have hbounded : IsBoundedUnder (· ≥ ·) atTop f :=
      isBoundedUnder_of_eventually_ge (hlower (c - 1) (by linarith))
    have hcobounded : IsCoboundedUnder (· ≥ ·) atTop f :=
      IsCoboundedUnder.of_frequently_le (hupper (c + 1) (by linarith))
    exact le_antisymm ((liminf_le_iff' hcobounded hbounded).mpr hupper)
      ((le_liminf_iff' hcobounded hbounded).mpr hlower)
  refine ⟨hlo, hatt, pay F K (log_lower hRH) ?_, pay T (E * K) (linear_lower hRH) ?_⟩
  · intro ε hε N
    obtain ⟨m, lambda, hmN, _, _, _, hf, _⟩ := hatt ε hε N
    exact ⟨m, hmN, hf⟩
  · intro ε hε N
    obtain ⟨m, lambda, hmN, _, _, _, _, ht⟩ := hatt ε hε N
    exact ⟨m, hmN, ht⟩

end D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
