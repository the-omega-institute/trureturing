/- GID: D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Seeded actual-root coefficients and the exact finite paid-prefix price transfer. -/
import D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
import D5.S3.Diophantine.StablePositiveSemigroup
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
import D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
import D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
import D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
import D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. This file proves finite COMPONENTS; it does not
claim the final paid-prefix repair existence theorem. The root owner and all
completed source suppliers remain uncompiled. The exposure patch is UNAPPLIED.
The remaining finite prime selection/factorization/cost obligations are stated
in the result envelope, not supplied as hypotheses to a purported final theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
open D5.S3.Diophantine.StablePositiveSemigroup
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)

/-- The seed turns even zero original slack into a large target. Coefficients
use the ACTUAL root offsets; b has a fixed finite bound, a+b is O(log X).
Every constant and threshold precedes X, original slack, and seed prime value.
The shell premise is deliberately on a real f, so no primality is invented for
the natural cutoff Q in Budget.spec. The arithmetic producer must supply f. -/
theorem seeded_two_layer_coefficients :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ C T : ℝ, 0 < C ∧ 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ δ₀ f : ℝ,
        0 ≤ δ₀ → δ₀ ≤ log (2 * X) → f ∈ Set.Icc (X / 2) (2 * X) →
        ∃ a b : ℕ, b ≤ B ∧ (a + b : ℝ) ≤ C * log X ∧
          log X - log 2 ≤ δ₀ + log f ∧
          δ₀ + log f ≤ 2 * log X + 2 * log 2 ∧
          δ₀ + log f - ε / 2 ≤
            (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +
            (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ∧
          (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +
            (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ≤
              δ₀ + log f - ε / 4 := by
  intro ε hε
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  obtain ⟨B, D, T, hmesh⟩ := stable_positive_mesh h2 h3
    irrational_log_three_div_log_two
    (by simpa using fixed_layer_root_offset_tendsto (by norm_num : 2 ≤ 2))
    (by simpa using fixed_layer_root_offset_tendsto (by norm_num : 2 ≤ 3)) ε hε
  have hlarge : ∀ᶠ X : ℝ in atTop,
      4 < X ∧ T ≤ X ∧ max 1 (D + log 2) ≤ log X := by
    filter_upwards [eventually_gt_atTop (4 : ℝ), eventually_ge_atTop T,
      tendsto_log_atTop.eventually_ge_atTop (max 1 (D + log 2))] with X hX hT hL
    exact ⟨hX, hT, hL⟩
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlarge
  let C : ℝ := 8 / log 2 + (B : ℝ) + 1
  refine ⟨B, C, max U 2, by dsimp [C]; positivity,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX δ₀ f hd0 hd hf
  obtain ⟨hX4, hXT, hL⟩ := hU X ((le_max_left U 2).trans hX)
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ log X := (le_max_left _ _).trans hL
  have hf0 : 0 < f := lt_of_lt_of_le (by positivity : 0 < X / 2) hf.1
  have hfl := log_le_log (by positivity : 0 < X / 2) hf.1
  have hfu := log_le_log hf0 hf.2
  rw [log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hfl
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at hfu hd
  have hseedlo : log X - log 2 ≤ δ₀ + log f := by linarith
  have hseedhi : δ₀ + log f ≤ 2 * log X + 2 * log 2 := by linarith
  have hseedD : D ≤ δ₀ + log f := by
    have hh := (le_max_right (1 : ℝ) (D + log 2)).trans hL
    linarith
  obtain ⟨a, b, hb, ha, hlo, hhi⟩ := hmesh X hXT (δ₀ + log f) hseedD
  have hlog2 : log (2 : ℝ) ≤ log X := log_le_log (by norm_num) (by linarith)
  have hΔ : δ₀ + log f ≤ 4 * log X := by linarith
  have ha' : (a : ℝ) ≤ (8 / log 2) * log X := by
    apply ha.trans
    apply (div_le_iff₀ h2).mpr
    have hh := mul_le_mul_of_nonneg_left hΔ (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [h2.ne']
    nlinarith only [hh]
  have hb' : (b : ℝ) ≤ (B : ℝ) * log X := by
    have hbc : (b : ℝ) ≤ B := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_left hL1 (Nat.cast_nonneg B)
    linarith
  refine ⟨a, b, hb, ?_, hseedlo, hseedhi, hlo, hhi⟩
  dsimp [C]
  push_cast
  nlinarith only [ha', hb', hL1]

/-- Direct natural construction with the entire canonical higher core and a
shorter first-layer prefix. There are no divisions or intermediate execution
assumptions. The two finite rosters are disjoint, and the FULL residual is the
sum of the inserted j=2 and j=3 losses. The higher-mass ledger includes all
added log mass, rather than bounding it by the old slack. -/
theorem two_roster_integer_ledger_at_layers {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
    {X : ℝ} (hX : 4 < X) {Q : ℕ}
    (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (hsupport : ∀ p : ℕ, p.Prime →
      2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)
    (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)
    (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = i - 1)
    (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = j - 1) :
    let n := strictInteger (referencePrice X)
    let base := higherCore n * prefixInteger Q
    let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
      (∀ p : ℕ, k.factorization p =
        base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧
      log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      log (higherCore k : ℝ) = log (higherCore n : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      actualDefect X k - completeFirstLayerLoss X k =
        (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p i) * log p) +
        (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p j) * log p) ∧
      (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ l : ℕ, 2 ≤ l →
        (l ≤ k.factorization p ↔ l ≤ optimalLayerCount (referencePrice X) p)) := by
  classical
  dsimp only
  let n := strictInteger (referencePrice X)
  let base := higherCore n * prefixInteger Q
  let k₂ := base * ∏ p ∈ A₂, p
  let k := k₂ * ∏ p ∈ A₃, p
  obtain ⟨hb2, hbp, hbl, hbh⟩ := prefix_budget_integer hQ2 hsupport
  change 2 ≤ base at hb2
  change base.primeFactors = Nat.primesLE Q at hbp
  change log (base : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) at hbl
  have hLambda : 0 < referencePrice X := by
    dsimp [referencePrice]
    exact one_div_pos.mpr (mul_pos (by linarith) (log_pos (by linarith)))
  have hbasehigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      (j ≤ base.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p) := by
    intro p hp j hj
    simpa only [strictInteger_counts hLambda] using hbh p hp j hj
  have hbasezero : actualDefect X base - completeFirstLayerLoss X base = 0 := by
    rw [defect_eq_first_of_optimizer_higher_layers (by linarith : 1 < X)
      (by omega : 1 ≤ base) hbasehigher, sub_self]
  have base_exp (p : ℕ) (hp : p.Prime) (hpQ : p ≤ Q)
      (l : ℕ) (hl : 2 ≤ l)
      (hopt : optimalLayerCount (referencePrice X) p = l - 1) :
      base.factorization p = l - 1 := by
    have hone : 1 ≤ base.factorization p := by
      have hmem : p ∈ base.primeFactors := hbp.symm ▸ Nat.mem_primesLE.mpr ⟨hpQ, hp⟩
      exact (hp.dvd_iff_one_le_factorization (by omega : base ≠ 0)).mp
        (Nat.dvd_of_mem_primeFactors hmem)
    have hnext := hbasehigher p hp l hl
    have hprev := hbasehigher p hp (l - 1)
    rw [hopt] at hnext hprev
    by_cases hl2 : l = 2
    · subst l
      norm_num at hnext ⊢
      omega
    · have hl3 : 2 ≤ l - 1 := by omega
      have hpast := (hprev hl3).mpr le_rfl
      omega
  have ha₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ base.factorization p = i - 1 := by
    intro p hp
    obtain ⟨hprime, hpQ, hopt⟩ := hA₂ p hp
    exact ⟨hprime, hpQ, base_exp p hprime hpQ i hi hopt⟩
  obtain ⟨hk₂, hkp₂, hkl₂, hkf₂, hkr₂⟩ := insert_roster_at_prefix hX hb2 hbp hQ hr hroot
    (by omega : 1 ≤ i) A₂ ha₂
  change 2 ≤ k₂ at hk₂
  change k₂.primeFactors = Nat.primesLE Q at hkp₂
  change log (k₂ : ℝ) - log (base : ℝ) = _ at hkl₂
  change (∀ p, k₂.factorization p = base.factorization p + if p ∈ A₂ then 1 else 0) at hkf₂
  change actualDefect X k₂ - completeFirstLayerLoss X k₂ = _ at hkr₂
  rw [hbasezero, zero_add] at hkr₂
  have ha₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ k₂.factorization p = j - 1 := by
    intro p hp
    obtain ⟨hprime, hpQ, hopt⟩ := hA₃ p hp
    have hnot : p ∉ A₂ := fun hp₂ => (Finset.disjoint_left.mp hdis) hp₂ hp
    rw [hkf₂, if_neg hnot, add_zero]
    exact ⟨hprime, hpQ, base_exp p hprime hpQ j hj hopt⟩
  obtain ⟨hk, hkp, hkl, hkf, hkr⟩ := insert_roster_at_prefix hX hk₂ hkp₂ hQ hr hroot
    (by omega : 1 ≤ j) A₃ ha₃
  change 2 ≤ k at hk
  change k.primeFactors = Nat.primesLE Q at hkp
  change log (k : ℝ) - log (k₂ : ℝ) = _ at hkl
  change (∀ p, k.factorization p = k₂.factorization p + if p ∈ A₃ then 1 else 0) at hkf
  change actualDefect X k - completeFirstLayerLoss X k = _ at hkr
  have hlog : log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +
      (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) := by
    linarith only [hkl, hkl₂, hbl]
  refine ⟨hk, hkp, ?_, hlog, ?_, ?_, ?_⟩
  · intro p
    rw [hkf, hkf₂]
  · rw [higher_core_log (by omega : 0 < k) hkp, hlog]
    ring
  · rw [hkr, hkr₂]
  · intro p hp hnot l hl
    have hp₂ : p ∉ A₂ := fun h => hnot (mem_union_left _ h)
    have hp₃ : p ∉ A₃ := fun h => hnot (mem_union_right _ h)
    rw [hkf, hkf₂, if_neg hp₂, if_neg hp₃, add_zero, add_zero]
    exact hbasehigher p hp l hl

/-- Exact finite price transfer for ANY actual paid repair k. This is the
finite algebraic implication, not an existence supplier for the final repair.
The old delta is confined to the old theta identity. The price term contains
X-log k. Equality k=m is handled by the reused total-defect comparison. -/
theorem finite_paid_prefix_comparison {η X μ : ℝ} (hX : 4 < X)
    {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ))
    (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (b : Budget) (hb : b.spec X)
    (hslack : 0 ≤ X - log (k : ℝ))
    (hpaid : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +
      (actualDefect X k - completeFirstLayerLoss X k) +
        referencePrice X * (X - log (k : ℝ)) ≤ η / (X * log X)) :
    k ≤ m ∧ 0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧
      actualDefect X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤
        η / (X * log X) +
        6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
          |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
            (X ^ 2 * log (X / 2)) := by
  obtain ⟨hkm, hcompare⟩ := two_price_compare hm hk hμ hrecord hclock hslack
  obtain ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩ := hb
  have hmprefix := (price_record_prime_structure hm hμ hrecord).2
  have hcancel := complete_first_layer_prefix_cancellation hX
    hmprefix hpref hP hQ hr hroot
  have hlogb : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
    rw [hbdef, Nat.cast_mul,
      log_mul (by exact_mod_cast (higher_core_pos (strictInteger (referencePrice X))).ne')
        (by exact_mod_cast (prefix_integer_pos b.Q).ne'), prefix_integer_log, ← hhdef]
  have hmass : Chebyshev.theta (largestPrime m : ℝ) - Chebyshev.theta (b.Q : ℝ) =
      b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ)) := by
    rw [hlogb] at hbudget
    rw [hclock] at hbudget
    linarith only [hbudget]
  rw [hmass] at hcancel
  have hfirst := le_abs_self (completeFirstLayerLoss X b.k - completeFirstLayerLoss X m)
  have hchange := le_abs_self (completeFirstLayerLoss X k - completeFirstLayerLoss X b.k)
  refine ⟨hkm, residual_nonneg (by linarith : 1 < X) (by omega : 1 ≤ m), ?_⟩
  nlinarith only [hcompare, hpaid, hfirst.trans hcancel, hchange]

#print axioms seeded_two_layer_coefficients
#print axioms finite_paid_prefix_comparison
end D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
