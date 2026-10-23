/- GID: D5/S3/Arith/Robin/ActualTwoPriceDefect
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualTwoPriceDefect
   mirror-E: none(waiver:general-analytic-results-no-numerical-evidence-artifact)
   anchors: []
   utility: none
   digest: General strict and weak layer optimizers and source-preserving pressure integral identities at positive prices. -/

/-
Project input: 79635cbec3aca2eaed7f64dcc3ce6ce4ba13a0db.
Mathlib API: 56a005855ea17e0b0958f73ec801ae140b0a1679.

The source integer remains the project's least strict all-layer optimizer.
The comparison integer is the finite product of ALL weak prime layers.
Pressure is a total sSup expression; its real supremum and attainment
claims here are on positive prices. No claim is made for nonpositive prices.
The proof uses its strict left stability, including at activation events,
and the upstream right-derivative FTC after reflection. No derivative or
integral identity is an input. No prime-distribution estimate is used.
-/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.Robin.EulerLayerPhaseSeparation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.ActualTwoPriceDefect

open Set Filter Finset MeasureTheory
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.Robin.EulerLayerPhaseSeparation

/-- The existing project's strict inventory, with every positive layer counted. -/
def strictInteger (q : ℝ) : ℕ :=
  if hq : 0 < q then Classical.choose (optimal_layer_count_spec hq) else 1

private theorem strictInteger_spec {q : ℝ} (hq : 0 < q) :
    1 ≤ strictInteger q ∧
    (∀ p : ℕ, (strictInteger q).factorization p = optimalLayerCount q p) ∧
    IsGoldenResourceOptimal q (strictInteger q) ∧
    ∀ m : ℕ, 1 ≤ m → IsGoldenResourceOptimal q m → strictInteger q ∣ m := by
  simpa only [strictInteger, dif_pos hq] using
    (Classical.choose_spec (optimal_layer_count_spec hq))

theorem strictInteger_pos {q : ℝ} (hq : 0 < q) : 1 ≤ strictInteger q :=
  (strictInteger_spec hq).1

theorem strictInteger_counts {q : ℝ} (hq : 0 < q) (p : ℕ) :
    (strictInteger q).factorization p = optimalLayerCount q p :=
  (strictInteger_spec hq).2.1 p

private theorem strictInteger_optimal {q : ℝ} (hq : 0 < q) :
    IsGoldenResourceOptimal q (strictInteger q) :=
  (strictInteger_spec hq).2.2.1

/-- Exact membership, so equality-price layers are excluded even at events. -/
theorem strict_layer_iff {q : ℝ} (hq : 0 < q) {p k : ℕ} (hp : p.Prime)
    (hk : 1 ≤ k) :
    k ≤ (strictInteger q).factorization p ↔ q < goldenLayerMarginal p k := by
  have h := positive_layers_eq_count_interval hq hp
  have hm : (1 ≤ k ∧ p.Prime ∧ q < goldenLayerMarginal p k) ↔
      k ∈ Set.Icc 1 (optimalLayerCount q p) := by rw [← h]; rfl
  rw [strictInteger_counts hq]
  simpa only [Set.mem_Icc, hk, hp, true_and] using hm.symm

/-- Literal finite product for the SAME chosen strict integer, with all its
prime directions and the original strict counts. -/
theorem strictInteger_eq_product {q : ℝ} (hq : 0 < q) :
    strictInteger q =
      ∏ p ∈ (strictInteger q).primeFactors, p ^ optimalLayerCount q p := by
  have h := Nat.prod_factorization_pow_eq_self
    (show strictInteger q ≠ 0 by have := strictInteger_pos hq; omega)
  simpa only [Finsupp.prod, Nat.support_factorization, strictInteger_counts hq] using h.symm

/-- All weak layers, including every equality layer, have finite support.
There is no restriction on either the prime or the positive layer index. -/
theorem weak_layers_finite {q : ℝ} (hq : 0 < q) :
    {pk : ℕ × ℕ | 1 ≤ pk.2 ∧ pk.1.Prime ∧
      q ≤ goldenLayerMarginal pk.1 pk.2}.Finite := by
  apply (positive_part_sum_finite_support (half_pos hq)).subset
  intro pk hpk
  exact ⟨hpk.1, hpk.2.1, (half_lt_self hq).trans_le hpk.2.2⟩

/-- This counts weak layers, rather than changing the strict source counts. -/
def weakLayerCount (q : ℝ) (p : ℕ) : ℕ :=
  {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k}.ncard

/-- Strict decrease turns each finite weak layer set into a full prefix. -/
theorem weak_layers_eq_count_interval {q : ℝ} (hq : 0 < q)
    {p : ℕ} (hp : p.Prime) :
    {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k} =
      Set.Icc 1 (weakLayerCount q p) := by
  classical
  let hfinite : {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k}.Finite :=
    (weak_layers_finite hq).preimage (fun _ _ _ _ h => (Prod.mk.inj h).2)
  let s := hfinite.toFinset
  let a := s.sup id
  have hmem (k : ℕ) : k ∈ s ↔ 1 ≤ k ∧ p.Prime ∧
      q ≤ goldenLayerMarginal p k := by simp [s]
  have hs : s = Finset.Icc 1 a := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_Icc.mpr ⟨((hmem k).mp hk).1, le_sup (f := id) hk⟩
    · intro hk
      obtain ⟨hk, hka⟩ := Finset.mem_Icc.mp hk
      have hne : s.Nonempty := by
        by_contra h
        have hz : a = 0 := by simp [a, Finset.not_nonempty_iff_eq_empty.mp h]
        omega
      obtain ⟨b, hb, hab⟩ := exists_mem_eq_sup s hne id
      have hba : b = a := hab.symm
      have hgain := ((hmem b).mp hb).2.2
      rw [hba] at hgain
      apply (hmem k).mpr
      refine ⟨hk, hp, ?_⟩
      rcases eq_or_lt_of_le hka with rfl | hlt
      · exact hgain
      · exact hgain.trans (golden_layer_strict_decrease hp hk hlt).le
  have hcount : weakLayerCount q p = a := by
    rw [weakLayerCount, Set.ncard_eq_toFinset_card _ hfinite]
    change s.card = a
    rw [hs, Nat.card_Icc]
    omega
  rw [hcount]
  ext k
  change (1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k) ↔ _
  rw [← hmem k, hs]
  simp

private theorem weak_count_zero_of_not_prime (q : ℝ) {p : ℕ} (hp : ¬p.Prime) :
    weakLayerCount q p = 0 := by
  simp [weakLayerCount, hp]

private theorem weak_count_last {q : ℝ} (hq : 0 < q) {p : ℕ} (hp : p.Prime)
    (ha : 1 ≤ weakLayerCount q p) :
    q ≤ goldenLayerMarginal p (weakLayerCount q p) := by
  have hmem : weakLayerCount q p ∈
      {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k} := by
    rw [weak_layers_eq_count_interval hq hp]
    exact ⟨ha, le_rfl⟩
  exact hmem.2.2

private theorem weak_count_next_lt {q : ℝ} (hq : 0 < q) {p : ℕ} (hp : p.Prime) :
    goldenLayerMarginal p (weakLayerCount q p + 1) < q := by
  apply lt_of_not_ge
  intro hgain
  have hmem : weakLayerCount q p + 1 ∈
      {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k} :=
    ⟨by omega, hp, hgain⟩
  rw [weak_layers_eq_count_interval hq hp] at hmem
  have := (Set.mem_Icc.mp hmem).2
  omega

/-- Finite exponent data defined from the actual weak layers, with no
optimality or tie-closure certificate as an input. -/
def weakLayerExponents (q : ℝ) (hq : 0 < q) : ℕ →₀ ℕ :=
  Finsupp.onFinset ((weak_layers_finite hq).toFinset.image Prod.fst)
    (weakLayerCount q) (by
      intro p ha
      have hp : p.Prime := by
        by_contra h
        exact ha (weak_count_zero_of_not_prime q h)
      have ha1 : 1 ≤ weakLayerCount q p := Nat.one_le_iff_ne_zero.mpr ha
      exact mem_image.mpr ⟨(p, weakLayerCount q p),
        (weak_layers_finite hq).mem_toFinset.mpr
          ⟨ha1, hp, weak_count_last hq hp ha1⟩, rfl⟩)

/-- A constructed finite natural prime-power product at every positive price.
The value 1 off that domain is only a total-definition convention. -/
def maximalInteger (q : ℝ) : ℕ :=
  if hq : 0 < q then (weakLayerExponents q hq).prod (· ^ ·) else 1

/-- Every optimal exponent lies between the strict and the weak counts. -/
theorem optimizer_exponent_bounds {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal q n) (p : ℕ) :
    optimalLayerCount q p ≤ n.factorization p ∧
      n.factorization p ≤ weakLayerCount q p := by
  have hn0 : n ≠ 0 := by omega
  constructor
  · have hd := (strictInteger_spec hq).2.2.2 n hn hopt
    have hle := (Nat.factorization_le_iff_dvd
      (show strictInteger q ≠ 0 by have := strictInteger_pos hq; omega) hn0).mpr hd p
    simpa only [strictInteger_counts hq] using hle
  · by_cases hp : p.Prime
    · by_cases he : n.factorization p = 0
      · rw [he]; exact Nat.zero_le _
      · have he1 : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr he
        have hpn : p ∣ n := (hp.dvd_iff_one_le_factorization hn0).mpr he1
        have hlast := ((golden_resource_optimal_iff_layer_thresholds hq hn).mp hopt).2 p hp hpn
        have hmem : n.factorization p ∈
            {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k} :=
          ⟨he1, hp, hlast⟩
        rw [weak_layers_eq_count_interval hq hp] at hmem
        exact hmem.2
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _

/-- Actual existence, global optimality and divisibility maximum of the
constructed weak product. Neither optimality nor finite closure is assumed. -/
theorem maximalInteger_spec {q : ℝ} (hq : 0 < q) :
    1 ≤ maximalInteger q ∧
    (∀ p : ℕ, (maximalInteger q).factorization p = weakLayerCount q p) ∧
    IsGoldenResourceOptimal q (maximalInteger q) ∧
    ∀ n : ℕ, 1 ≤ n → IsGoldenResourceOptimal q n →
      n ∣ maximalInteger q ∧ n ≤ maximalInteger q := by
  classical
  let t := weakLayerExponents q hq
  have ht (p : ℕ) : t p = weakLayerCount q p := rfl
  have htprime : ∀ p ∈ t.support, p.Prime := by
    intro p hp
    by_contra h
    have hz : t p = 0 := by rw [ht, weak_count_zero_of_not_prime q h]
    exact (Finsupp.mem_support_iff.mp hp) hz
  have hprod : maximalInteger q = t.prod (· ^ ·) := by
    simp only [maximalInteger, dif_pos hq]
    rfl
  have hfac : (maximalInteger q).factorization = t := by
    rw [hprod]
    exact Nat.factorization_prod_pow_eq_self htprime
  have hn0 : maximalInteger q ≠ 0 := by
    rw [hprod]
    apply Finsupp.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (htprime p hp).ne_zero
  have hn : 1 ≤ maximalInteger q := Nat.one_le_iff_ne_zero.mpr hn0
  have hcounts (p : ℕ) : (maximalInteger q).factorization p = weakLayerCount q p := by
    rw [hfac]
    exact ht p
  refine ⟨hn, hcounts, ?_, ?_⟩
  · apply (golden_resource_optimal_iff_layer_thresholds hq hn).mpr
    constructor
    · intro p hp
      rw [hcounts]
      exact (weak_count_next_lt hq hp).le
    · intro p hp hpn
      have ha : 1 ≤ weakLayerCount q p := by
        rw [← hcounts]
        exact hp.factorization_pos_of_dvd hn0 hpn
      rw [hcounts]
      exact weak_count_last hq hp ha
  · intro n hn hopt
    have hd : n ∣ maximalInteger q := by
      apply (Nat.factorization_le_iff_dvd (by omega) hn0).mp
      intro p
      rw [hcounts]
      exact (optimizer_exponent_bounds hq hn hopt p).2
    exact ⟨hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd⟩


/-!
The complete maximalInteger_all_ties assertion and proof are preserved as
transient evidence in transient/ActualTwoPriceDefect.pre-repair.lean and
the extracted block. Its unconsumed proposed canonical binding is removed
from this candidate; all strict/weak classifiers, endpoint definitions and
the original global consumer remain unchanged.
-/

def price (x : ℝ) : ℝ := 1 / (x * Real.log x)

def weight (x : ℝ) : ℝ := (1 + Real.log x) / (x ^ 2 * Real.log x ^ 2)

def integerAt (x : ℝ) : ℕ := strictInteger (price x)

/-- This is the original integer's logarithm, never replaced by its price parameter. -/
def clock (x : ℝ) : ℝ := Real.log (integerAt x)

def W (n : ℕ) : ℝ := Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)

/-- Total sSup expression. Real bounded-supremum and existence assertions
in this module concern q > 0 only; no nonpositive-price attainment is asserted. -/
def pressure (q : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ n : ℕ, 1 ≤ n ∧ v = goldenResourceObjective q n}

def defect (a : ℝ) (n : ℕ) : ℝ :=
  pressure (price a) - W n + price a * Real.log n

private theorem price_pos {x : ℝ} (hx : 1 < x) : 0 < price x := by
  exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hx))

private theorem price_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    price y ≤ price x := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  · exact (price_strictAnti hx hxy).le

private theorem price_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt price (-weight x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv
    (mul_ne_zero hx0 hl0)
  convert hd using 1
  · funext y
    change 1 / (y * Real.log y) = (y * Real.log y)⁻¹
    rw [one_div]
  · dsimp [weight]
    field_simp [hx0, hl0]
    <;> ring

private theorem weight_continuousAt {x : ℝ} (hx : 1 < x) : ContinuousAt weight x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  exact (continuousAt_const.add (Real.continuousAt_log hx0)).div
    ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hl0))

/-- A single finite all-layer set covers a whole compact interval, including
weak equality layers. There is no exponent cutoff in this assertion. -/
theorem compact_layer_support {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∃ S : Finset (ℕ × ℕ),
      (∀ pk ∈ S, 1 ≤ pk.2 ∧ pk.1.Prime) ∧
      ∀ u ∈ Set.Icc a b, ∀ p k : ℕ, 1 ≤ k → p.Prime →
        price u ≤ goldenLayerMarginal p k → (p, k) ∈ S := by
  classical
  have hb : 1 < b := ha.trans_le hab
  let hfinite := positive_part_sum_finite_support (half_pos (price_pos hb))
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro pk hpk
    exact ⟨((hfinite.mem_toFinset).mp hpk).1,
      ((hfinite.mem_toFinset).mp hpk).2.1⟩
  · intro u hu p k hk hp hgain
    apply hfinite.mem_toFinset.mpr
    refine ⟨hk, hp, ?_⟩
    exact (half_lt_self (price_pos hb)).trans_le
      ((price_antitone (ha.trans_le hu.1) hu.2).trans hgain)

/-- As price falls, the exact strict integer grows by divisibility. -/
private theorem strictInteger_dvd {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hrq : r ≤ q) : strictInteger q ∣ strictInteger r := by
  apply (Nat.factorization_le_iff_dvd
    (by have := strictInteger_pos hq; omega)
    (by have := strictInteger_pos hr; omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hk : (strictInteger q).factorization p = 0
    · rw [hk]; exact Nat.zero_le _
    · have hk1 : 1 ≤ (strictInteger q).factorization p := by omega
      exact (strict_layer_iff hr hp hk1).mpr
        (hrq.trans_lt ((strict_layer_iff hq hp hk1).mp le_rfl))
  · simpa only [Nat.factorization_eq_zero_of_not_prime _ hp] using (le_refl (0 : ℕ))

private theorem log_inventory_nonneg {q : ℝ} (hq : 0 < q) :
    0 ≤ Real.log (strictInteger q) :=
  Real.log_nonneg (by exact_mod_cast strictInteger_pos hq)

private theorem log_inventory_antitone {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hrq : r ≤ q) : Real.log (strictInteger q) ≤ Real.log (strictInteger r) := by
  apply Real.log_le_log
  · exact_mod_cast (show 0 < strictInteger q from strictInteger_pos hq)
  · exact_mod_cast Nat.le_of_dvd
      (show 0 < strictInteger r from strictInteger_pos hr) (strictInteger_dvd hq hr hrq)

theorem clock_monotone : MonotoneOn clock (Set.Ioi 1) := by
  intro x hx y hy hxy
  exact log_inventory_antitone (price_pos hx) (price_pos hy) (price_antitone hx hxy)

/-- A supplied optimizer bounds and attains this sSup. This conditional
statement preserves the original header; it asserts no optimizer exists.
Every invocation below has an explicit positive-price proof in scope. -/
theorem pressure_eq_of_optimal {q : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal q n) :
    pressure q = goldenResourceObjective q n := by
  unfold pressure
  apply le_antisymm
  · apply csSup_le
    · exact ⟨goldenResourceObjective q n, n, hn, rfl⟩
    · rintro v ⟨m, hm, rfl⟩
      exact hopt m hm
  · apply le_csSup
    · exact ⟨goldenResourceObjective q n, by
        rintro v ⟨m, hm, rfl⟩
        exact hopt m hm⟩
    · exact ⟨n, hn, rfl⟩

/-- At positive prices the constructed maximum bounds the actual objective
set and attains its sSup. The bound is obtained from proved optimality. -/
theorem pressure_maximal_spec {q : ℝ} (hq : 0 < q) :
    BddAbove {v : ℝ | ∃ n : ℕ, 1 ≤ n ∧ v = goldenResourceObjective q n} ∧
      pressure q = goldenResourceObjective q (maximalInteger q) := by
  have hs := maximalInteger_spec hq
  constructor
  · refine ⟨goldenResourceObjective q (maximalInteger q), ?_⟩
    rintro v ⟨n, hn, rfl⟩
    exact hs.2.2.1 n hn
  · exact pressure_eq_of_optimal hs.1 hs.2.2.1

private theorem pressure_eq_inventory {q : ℝ} (hq : 0 < q) :
    pressure q = goldenResourceObjective q (strictInteger q) :=
  pressure_eq_of_optimal (strictInteger_pos hq) (strictInteger_optimal hq)

private theorem pressure_sub_bounds {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    (q - r) * Real.log (strictInteger q) ≤ pressure r - pressure q ∧
    pressure r - pressure q ≤ (q - r) * Real.log (strictInteger r) := by
  have h₁ := strictInteger_optimal hr (strictInteger q) (strictInteger_pos hq)
  have h₂ := strictInteger_optimal hq (strictInteger r) (strictInteger_pos hr)
  rw [pressure_eq_inventory hr, pressure_eq_inventory hq]
  dsimp [goldenResourceObjective] at h₁ h₂ ⊢
  constructor <;> linarith

private theorem pressure_abs_sub_le {q₀ q r : ℝ} (h₀ : 0 < q₀)
    (h₀q : q₀ ≤ q) (h₀r : q₀ ≤ r) :
    |pressure r - pressure q| ≤ |r - q| * Real.log (strictInteger q₀) := by
  have hq := h₀.trans_le h₀q
  have hr := h₀.trans_le h₀r
  have hbq : |(q - r) * Real.log (strictInteger q)| ≤
      |r - q| * Real.log (strictInteger q₀) := by
    rw [abs_mul, abs_of_nonneg (log_inventory_nonneg hq), abs_sub_comm q r]
    exact mul_le_mul_of_nonneg_left (log_inventory_antitone hq h₀ h₀q) (abs_nonneg _)
  have hbr : |(q - r) * Real.log (strictInteger r)| ≤
      |r - q| * Real.log (strictInteger q₀) := by
    rw [abs_mul, abs_of_nonneg (log_inventory_nonneg hr), abs_sub_comm q r]
    exact mul_le_mul_of_nonneg_left (log_inventory_antitone hr h₀ h₀r) (abs_nonneg _)
  have hs := pressure_sub_bounds hq hr
  exact abs_le.mpr ⟨((neg_le_neg hbq).trans (neg_abs_le _)).trans hs.1,
    hs.2.trans ((le_abs_self _).trans hbr)⟩

private theorem pressure_continuousAt {q : ℝ} (hq : 0 < q) :
    ContinuousAt pressure q := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let B := Real.log (strictInteger (q / 2))
  have hB : 0 ≤ B := log_inventory_nonneg (half_pos hq)
  have hB1 : 0 < B + 1 := by linarith
  refine ⟨min (q / 2) (ε / (B + 1)), lt_min (half_pos hq) (div_pos hε hB1), ?_⟩
  intro r hr
  rw [Real.dist_eq] at hr ⊢
  have hsmall := hr.trans_le (min_le_left _ _)
  have hnear := hr.trans_le (min_le_right _ _)
  have hr₀ : q / 2 ≤ r := by
    have := neg_abs_le (r - q)
    linarith
  have hbound := pressure_abs_sub_le (half_pos hq) (by linarith : q / 2 ≤ q) hr₀
  have hprod : |r - q| * (B + 1) < ε := (lt_div_iff₀ hB1).mp hnear
  exact hbound.trans_lt (by change |r - q| * B < ε; nlinarith [abs_nonneg (r - q)])

/-- Strict full inventory is locally constant from the left, even at a tie.
Common finite layer support is used to preserve every currently active layer;
monotonicity excludes new layers on that side. -/
private theorem inventory_locally_left {x : ℝ} (hx : 1 < x) :
    (fun y => integerAt y) =ᶠ[𝓝[Set.Iic x] x] (fun _ => integerAt x) := by
  classical
  let a := (x + 1) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have hax : a ≤ x := by dsimp [a]; linarith
  obtain ⟨S, _, hcover⟩ := compact_layer_support ha hax
  have heach : ∀ pk ∈ S, ∀ᶠ y in 𝓝 x,
      price x < goldenLayerMarginal pk.1 pk.2 →
        price y < goldenLayerMarginal pk.1 pk.2 := by
    intro pk hpk
    by_cases hgain : price x < goldenLayerMarginal pk.1 pk.2
    · have he := (price_hasDerivAt hx).continuousAt.eventually
        (isOpen_Iio.mem_nhds hgain)
      filter_upwards [he] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall fun _ h => (hgain h).elim
  have hall := (Filter.eventually_all_finset S).mpr heach
  have hdomain : ∀ᶠ y in 𝓝 x, 1 < y := isOpen_Ioi.mem_nhds hx
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds,
    hdomain.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hy1 hyx
  apply Nat.eq_of_factorization_eq
    (by
      have hn : 1 ≤ integerAt y := strictInteger_pos (price_pos hy1)
      omega)
    (by
      have hn : 1 ≤ integerAt x := strictInteger_pos (price_pos hx)
      omega)
  intro p
  change (strictInteger (price y)).factorization p = (strictInteger (price x)).factorization p
  rw [strictInteger_counts (price_pos hy1), strictInteger_counts (price_pos hx)]
  unfold optimalLayerCount
  apply congrArg Set.ncard
  ext k
  constructor
  · rintro ⟨hk, hp, hgain⟩
    exact ⟨hk, hp, (price_antitone hy1 hyx).trans_lt hgain⟩
  · rintro ⟨hk, hp, hgain⟩
    have hpk := hcover x ⟨hax, le_rfl⟩ p k hk hp hgain.le
    exact ⟨hk, hp, hy (p, k) hpk hgain⟩

/-- The pressure envelope's actual left derivative is derived, not assumed.
At an event this is the strict inventory, with all tied layers excluded. -/
private theorem pressure_left_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivWithinAt (fun u => pressure (price u)) (clock x * weight x) (Set.Iio x) x := by
  have hloc := (inventory_locally_left hx).filter_mono
    (nhdsWithin_mono x Set.Iio_subset_Iic_self)
  have hdomain : ∀ᶠ y in 𝓝[Set.Iio x] x, 1 < y := by
    have he : ∀ᶠ y in 𝓝 x, 1 < y := isOpen_Ioi.mem_nhds hx
    exact he.filter_mono nhdsWithin_le_nhds
  have heq : (fun u => pressure (price u)) =ᶠ[𝓝[Set.Iio x] x]
      (fun u => goldenResourceObjective (price u) (integerAt x)) := by
    filter_upwards [hloc, hdomain] with u hu hu1
    rw [pressure_eq_inventory (price_pos hu1)]
    change goldenResourceObjective (price u) (integerAt u) = _
    rw [hu]
  have hd : HasDerivAt (fun u => goldenResourceObjective (price u) (integerAt x))
      (clock x * weight x) x := by
    have h := (hasDerivAt_const x
      (Real.log (∑ d ∈ (integerAt x).divisors, (d : ℝ)⁻¹))).sub
      ((price_hasDerivAt hx).mul_const (Real.log (integerAt x)))
    convert h using 1
    · funext u
      dsimp [goldenResourceObjective]
    · dsimp [clock]
      ring
  exact hd.hasDerivWithinAt.congr_of_eventuallyEq heq
    (pressure_eq_inventory (price_pos hx))

private theorem interval_above_one {a b u : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hu : u ∈ Set.uIcc a b) : 1 < u :=
  (lt_min ha hb).trans_le hu.1

private theorem clock_weight_integrable {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun u => clock u * weight u) volume a b := by
  have hm : MonotoneOn clock (Set.uIcc a b) :=
    clock_monotone.mono fun u hu => interval_above_one ha hb hu
  exact hm.intervalIntegrable.mul_continuousOn
    (fun u hu => (weight_continuousAt (interval_above_one ha hb hu)).continuousWithinAt)

/-- Genuine pressure-envelope integration, proved across every activation event
by reflecting the derived left derivative into the library's right FTC. -/
theorem pressure_integral {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ u in a..b, clock u * weight u) = pressure (price b) - pressure (price a) := by
  have hdomain {t : ℝ} (ht : t ∈ Set.uIcc (-b) (-a)) : 1 < -t := by
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le (neg_le_neg hab)] at ht
      linarith [ht.1, ht.2]
    · rw [Set.uIcc_of_ge (neg_le_neg hba)] at ht
      linarith [ht.1, ht.2]
  have hc : ContinuousOn (fun t => pressure (price (-t))) (Set.uIcc (-b) (-a)) := by
    intro t ht
    exact (((pressure_continuousAt (price_pos (hdomain ht))).comp
      (price_hasDerivAt (hdomain ht)).continuousAt).comp continuousAt_neg).continuousWithinAt
  have hd : ∀ t ∈ Set.Ioo (min (-b) (-a)) (max (-b) (-a)),
      HasDerivWithinAt (fun t => pressure (price (-t)))
        (-(clock (-t) * weight (-t))) (Set.Ioi t) t := by
    intro t ht
    have ht1 := hdomain (show t ∈ Set.uIcc (-b) (-a) from ⟨ht.1.le, ht.2.le⟩)
    have hm : Set.MapsTo (fun u : ℝ => -u) (Set.Ioi t) (Set.Iio (-t)) := by
      intro u hu
      change -u < -t
      exact neg_lt_neg hu
    simpa only [Function.comp_def, mul_neg_one] using
      (pressure_left_deriv ht1).comp t ((hasDerivAt_id t).neg.hasDerivWithinAt) hm
  have hi : IntervalIntegrable (fun t => -(clock (-t) * weight (-t))) volume (-b) (-a) :=
    ((IntervalIntegrable.iff_comp_neg (a := b) (b := a)
      (f := fun u => clock u * weight u) (by finiteness)).mp
        (clock_weight_integrable ha hb).symm).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right hc hd hi
  have hn := congrArg (fun r : ℝ => -r) h
  rw [intervalIntegral.integral_neg] at hn
  simp only [neg_neg, neg_sub] at hn
  have hreflect := intervalIntegral.integral_comp_neg
    (fun u => clock u * weight u) (a := -b) (b := -a)
  rw [hreflect] at hn
  simpa only [neg_neg] using hn

private theorem weight_integral {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ u in a..b, weight u) = price a - price b := by
  have hd : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun u => -price u) (weight u) u := by
    intro u hu
    simpa only [neg_neg] using (price_hasDerivAt (interval_above_one ha hb hu)).fun_neg
  have hi : IntervalIntegrable weight volume a b :=
    (show ContinuousOn weight (Set.uIcc a b) from
      fun u hu => (weight_continuousAt (interval_above_one ha hb hu)).continuousWithinAt).intervalIntegrable
  simpa only [neg_sub_neg] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- The exact same integer is kept at the two arbitrary prices. -/
theorem two_price_oriented {x a : ℝ} (hx : 1 < x) (ha : 1 < a) :
    defect a (integerAt x) = ∫ u in x..a, (clock u - clock x) * weight u := by
  let P : ℕ := ∏ p ∈ (strictInteger (price x)).primeFactors,
    p ^ optimalLayerCount (price x) p
  have hproduct : integerAt x = P := strictInteger_eq_product (price_pos hx)
  have hP : 1 ≤ P := by
    rw [← hproduct]
    exact strictInteger_pos (price_pos hx)
  have hsource : pressure (price x) = W (integerAt x) - price x * clock x := by
    have hs := pressure_eq_inventory (price_pos hx)
    change pressure (price x) = goldenResourceObjective (price x) (integerAt x) at hs
    dsimp only [W, clock]
    rw [hproduct] at hs ⊢
    exact hs.trans (golden_resource_sigma_identity (price x) hP)
  have hmax := (pressure_maximal_spec (price_pos ha)).2
  have hcomparison :
      goldenResourceObjective (price a) (maximalInteger (price a)) -
          goldenResourceObjective (price a) (integerAt x) =
        (pressure (price a) - pressure (price x)) - clock x * (price x - price a) := by
    rw [← hmax, golden_resource_sigma_identity (n := integerAt x) _
        (strictInteger_pos (price_pos hx))]
    dsimp only [W, clock] at hsource ⊢
    linarith
  have hw : IntervalIntegrable weight volume x a :=
    (show ContinuousOn weight (Set.uIcc x a) from
      fun u hu => (weight_continuousAt (interval_above_one hx ha hu)).continuousWithinAt).intervalIntegrable
  calc
    defect a (integerAt x) =
        goldenResourceObjective (price a) (maximalInteger (price a)) -
          goldenResourceObjective (price a) (integerAt x) := by
      rw [← hmax, golden_resource_sigma_identity (n := integerAt x) _
        (strictInteger_pos (price_pos hx))]
      dsimp only [defect, W]
      ring
    _ = (pressure (price a) - pressure (price x)) -
        clock x * (price x - price a) := hcomparison
    _ = (∫ u in x..a, clock u * weight u) -
        clock x * (∫ u in x..a, weight u) := by
      rw [pressure_integral hx ha, weight_integral hx ha]
    _ = ∫ u in x..a, (clock u - clock x) * weight u := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (clock_weight_integrable hx ha) (hw.const_mul (clock x))]
      apply intervalIntegral.integral_congr
      intro u hu
      ring

private theorem oriented_eq_absolute {x a : ℝ} (hx : 1 < x) (ha : 1 < a) :
    (∫ u in x..a, (clock u - clock x) * weight u) =
      ∫ u in min x a..max x a, |clock u - clock x| * weight u := by
  rcases le_total x a with hxa | hax
  · rw [min_eq_left hxa, max_eq_right hxa]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hxa] at hu
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr
      (clock_monotone hx (hx.trans_le hu.1) hu.1))]
  · rw [min_eq_right hax, max_eq_left hax, intervalIntegral.integral_symm]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hax] at hu
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr
      (clock_monotone (ha.trans_le hu.1) hx hu.2))]
    ring

/-- NPC5, first equality, with the source's own clock A = log N_x. -/
theorem npc5_oriented {x : ℝ} (hx : 1 < x) (hA : 1 < clock x) :
    defect (clock x) (integerAt x) =
      ∫ u in x..clock x, (clock u - clock x) * weight u :=
  two_price_oriented hx hA

/-- NPC5, absolute form, valid for both price orders and all ties. -/
theorem npc5 {x : ℝ} (hx : 1 < x) (hA : 1 < clock x) :
    defect (clock x) (integerAt x) =
      ∫ u in min x (clock x)..max x (clock x), |clock u - clock x| * weight u := by
  rw [npc5_oriented hx hA]
  exact oriented_eq_absolute hx hA

/-- Any comparison optimizer at the own price, including the maximal tied
optimizer, gives exactly the same cost and the same source-preserving integral. -/
theorem npc5_any_comparison_optimizer {x : ℝ} (hx : 1 < x) (hA : 1 < clock x)
    {C : ℕ} (hC : 1 ≤ C) (hopt : IsGoldenResourceOptimal (price (clock x)) C) :
    goldenResourceObjective (price (clock x)) C -
        goldenResourceObjective (price (clock x)) (integerAt x) =
      ∫ u in min x (clock x)..max x (clock x), |clock u - clock x| * weight u := by
  calc
    goldenResourceObjective (price (clock x)) C -
        goldenResourceObjective (price (clock x)) (integerAt x) =
        defect (clock x) (integerAt x) := by
      rw [← pressure_eq_of_optimal hC hopt,
        golden_resource_sigma_identity (n := integerAt x) _
        (strictInteger_pos (price_pos hx))]
      dsimp [defect, W]
      ring
    _ = _ := npc5 hx hA

end D5.S3.Arith.Robin.ActualTwoPriceDefect
