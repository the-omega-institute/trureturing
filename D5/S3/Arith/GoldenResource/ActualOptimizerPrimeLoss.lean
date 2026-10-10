/- GID: D5/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite weighted prime loss from Chebyshev theta and its same-state reserve-paid consumer.

   Source continuation of pinned 1d75c9bcdab3ea88a77f139a1d7cb3f6f638ff32.
   The actual weighted bridges and directed step integrals are derived below;
   no selection or charge bridge is a premise of Q. Every positive original
   optimizer and every original-price tie choice remain in scope. The primitive
   theta interval supplier and the actual reserve-band count are still inputs.
   This source has NOT been compiled in this attempt: the caller's verified
   canonical one-thread mechanism has not yet been supplied. The printed axiom
   commands are requests for future evidence, not axiom-closure receipts.
   New public theorem escape audits use the existing linked-issue exception:
   https://github.com/the-omega-institute/trureturing/issues/5214. The inherited
   Reg mirror is uncompiled and does not register Q or its reserve consumer.
   No signed margin, full all-integer coverage, or RH conclusion is asserted.
-/

import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask

namespace D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open MeasureTheory

noncomputable section

def price (t : ℝ) : ℝ := 1 / (t * Real.log t)

def curvature (t : ℝ) : ℝ :=
  (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)

def actualPressure (lambda : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ goldenResourceObjective lambda n = x}

def actualDefect (x b : ℝ) (n : ℕ) : ℝ :=
  actualPressure (price x) - goldenResourceObjective (price x) n

def forwardBand (b x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter fun p =>
    p.Prime ∧ b < p ∧ p ≤ x - 1

def reverseBand (x b : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor b + 1)).filter fun p =>
    p.Prime ∧ x < p ∧ p ≤ b - 1

def forwardWeightedMass (b x : ℝ) : ℝ :=
  ∑ p ∈ forwardBand b x, Real.log p * (price (p + 1) - price x)

def reverseWeightedMass (x b : ℝ) : ℝ :=
  ∑ p ∈ reverseBand x b, Real.log p * (price x - price p)

def rho (epsilon H : ℝ) : ℝ := (1 - epsilon) * (1 - 1 / H)

def ThetaIntervalSupplier (X epsilon H0 : ℝ) : Prop :=
  ∀ u v : ℝ, X ≤ u → u < v → v ≤ 2 * X → H0 ≤ v - u →
    (1 - epsilon) * (v - u) ≤ Chebyshev.theta v - Chebyshev.theta u

theorem price_pos {t : ℝ} (ht : 1 < t) : 0 < price t := by
  unfold price
  exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht))

theorem curvature_pos {t : ℝ} (ht : 1 < t) : 0 < curvature t := by
  unfold curvature
  have hlog : 0 < Real.log t := Real.log_pos ht
  positivity

theorem price_strictAnti {u v : ℝ} (hu : 1 < u) (huv : u < v) :
    price v < price u := by
  unfold price
  apply one_div_lt_one_div_of_lt
  · exact mul_pos (by linarith) (Real.log_pos hu)
  · have hmono := Real.mul_log_strictMonoOn
      (show u ∈ Set.Ici (Real.exp (-1)) by
        have : Real.exp (-1) < (1 : ℝ) := by
          simpa using (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num))
        exact this.le.trans hu.le)
      (show v ∈ Set.Ici (Real.exp (-1)) by
        have : Real.exp (-1) < (1 : ℝ) := by
          simpa using (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num))
        exact this.le.trans (hu.trans huv).le)
      huv
    exact hmono

theorem price_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    price v ≤ price u := by
  rcases huv.eq_or_lt with rfl | huv
  · rfl
  · exact (price_strictAnti hu huv).le

theorem first_layer_between_prices {p : ℕ} (hp : p.Prime) :
    price (p + 1) < goldenLayerMarginal p 1 ∧
      goldenLayerMarginal p 1 < price p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hy : 0 < (1 + 1 / (p : ℝ)) := by positivity
  have hgt : (1 : ℝ) < 1 + 1 / (p : ℝ) := by
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hinvPos : 0 < 1 / (p : ℝ) := one_div_pos.mpr hpPos
    linarith
  have hupper := Real.log_lt_sub_one_of_pos hy (ne_of_gt hgt)
  have hinv : 0 < (1 + 1 / (p : ℝ))⁻¹ := inv_pos.mpr hy
  have hneq : (1 + 1 / (p : ℝ))⁻¹ ≠ 1 := by
    intro h
    have hle := (inv_lt_one₀ hy).mpr hgt
    linarith
  have hlow' := Real.log_lt_sub_one_of_pos hinv hneq
  rw [Real.log_inv] at hlow'
  have hlow : (1 / ((p : ℝ) + 1)) < Real.log (1 + 1 / (p : ℝ)) := by
    have hcalc : 1 - (1 + 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) + 1) := by
      field_simp
      ring
    calc
      1 / ((p : ℝ) + 1) = 1 - (1 + 1 / (p : ℝ))⁻¹ := hcalc.symm
      _ < Real.log (1 + 1 / (p : ℝ)) := by linarith
  have hMarg := golden_layer_marginal_one_eq_log_one_add_inv hp
  have hlogp1 : Real.log (p : ℝ) < Real.log ((p : ℝ) + 1) := by
    exact Real.strictMonoOn_log
      (by change (0 : ℝ) < p; exact_mod_cast hp.pos)
      (by change (0 : ℝ) < (p : ℝ) + 1; positivity)
      (by exact_mod_cast (show p < p + 1 by omega))
  have hprod : ((p : ℝ) + 1) * Real.log p <
      ((p : ℝ) + 1) * Real.log ((p : ℝ) + 1) := by
    exact mul_lt_mul_of_pos_left hlogp1 (by positivity)
  constructor
  · unfold price
    rw [hMarg]
    calc
      1 / (((p : ℝ) + 1) * Real.log ((p : ℝ) + 1)) <
          1 / (((p : ℝ) + 1) * Real.log p) :=
        one_div_lt_one_div_of_lt (by positivity) hprod
      _ = (1 / ((p : ℝ) + 1)) / Real.log p := by field_simp
      _ < Real.log (1 + 1 / (p : ℝ)) / Real.log p :=
        div_lt_div_of_pos_right hlow hlogp
  · unfold price
    rw [hMarg]
    calc
      Real.log (1 + 1 / (p : ℝ)) / Real.log p <
          (1 / (p : ℝ)) / Real.log p := by
        apply div_lt_div_of_pos_right _ hlogp
        simpa [one_div] using hupper
      _ = 1 / ((p : ℝ) * Real.log p) := by field_simp

theorem actual_defect_nonneg {x b : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ actualDefect x b n := by
  unfold actualDefect actualPressure
  obtain ⟨m, hm, hcounts, hopt, _⟩ := optimal_layer_count_spec (price_pos hx)
  have hsup := golden_resource_supremum_eq_positive_part_sum (price_pos hx)
  have hobj := objective_at_optimal_eq_positive_part_sum (price_pos hx) hm hcounts
  rw [hsup, ← hobj]
  exact sub_nonneg.mpr (hopt n hn)

private theorem forward_prime_absent {b : ℝ} (hb : 1 < b)
    {n p : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n)
    (hp : p.Prime) (hpb : b < p) : n.factorization p = 0 := by
  have hupper := (golden_resource_optimal_iff_layer_thresholds
    (price_pos hb) hn).1 hopt |>.1 p hp
  have hbp : price p < price b := price_strictAnti hb hpb
  have hfirst := (first_layer_between_prices hp).2
  have hlt : goldenLayerMarginal p 1 < price b := hfirst.trans hbp
  by_contra hne
  have hpos : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hne
  have hdec : goldenLayerMarginal p (n.factorization p) ≤
      goldenLayerMarginal p 1 := by
    rcases eq_or_lt_of_le hpos with heq | hltk
    · rw [← heq]
    · exact (golden_layer_strict_decrease hp (by omega) hltk).le
  have hdiv : p ∣ n := by
    apply Nat.dvd_of_mem_primeFactors
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hne
  have hge := (golden_resource_optimal_iff_layer_thresholds
    (price_pos hb) hn).1 hopt |>.2 p hp hdiv
  exact (not_lt_of_ge (hge.trans hdec)) hlt

private theorem reverse_prime_adopted {x b : ℝ} (hx : 1 < x) (hxb : x < b)
    {n p : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n)
    (hp : p.Prime) (hpx : x < p) (hpb : p ≤ b - 1) :
    1 ≤ n.factorization p := by
  have hupper := (golden_resource_optimal_iff_layer_thresholds
    (price_pos (lt_trans hx hxb)) hn).1 hopt |>.1 p hp
  have hxp : price b ≤ price (p + 1) := by
    have hp1 : (1 : ℝ) < (p : ℝ) + 1 := by
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    have hp1b : (p : ℝ) + 1 ≤ b := by linarith
    exact price_anti hp1 hp1b
  have hfirst := (first_layer_between_prices hp).1
  have hge : price b < goldenLayerMarginal p 1 := hxp.trans_lt hfirst
  by_contra hzero
  have hz : n.factorization p = 0 := by omega
  have hle : goldenLayerMarginal p 1 ≤ price b := by simpa [hz] using hupper
  exact (not_lt_of_ge hle) hge

theorem forward_band_selection {b x : ℝ} (hb : 1 < b) (hbx : b < x)
    {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n) :
    ∀ p ∈ forwardBand b x, n.factorization p = 0 := by
  intro p hp
  have hmem := mem_filter.mp hp
  exact forward_prime_absent hb hn hopt hmem.2.1 hmem.2.2.1

theorem reverse_band_selection {x b : ℝ} (hx : 1 < x) (hxb : x < b)
    {n : ℕ} (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal (price b) n) :
    ∀ p ∈ reverseBand x b, 1 ≤ n.factorization p := by
  intro p hp
  have hmem := mem_filter.mp hp
  exact reverse_prime_adopted hx hxb hn hopt hmem.2.1 hmem.2.2.1 hmem.2.2.2

/- The pressure attainer is used only to decompose the full finite objective
   difference. Its tie convention is irrelevant to the local maximum. -/
private theorem pressure_eq_of_optimal {x : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hopt : IsGoldenResourceOptimal (price x) m) :
    actualPressure (price x) = goldenResourceObjective (price x) m := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨m, hm, rfl⟩, ?_⟩
  rintro y ⟨k, hk, rfl⟩
  exact hopt k hk

private theorem local_gap_nonneg {x : ℝ} (hx : 1 < x) {m : ℕ}
    (hm : 1 ≤ m) (hopt : IsGoldenResourceOptimal (price x) m)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    0 ≤ goldenPrimeLocalObjective (price x) p (m.factorization p) -
      goldenPrimeLocalObjective (price x) p a := by
  have h := (golden_resource_optimal_iff_layer_thresholds (price_pos hx) hm).mp hopt
  apply sub_nonneg.mpr
  apply golden_prime_local_objective_maximal_of_threshold hp (price x) (h.1 p hp)
  by_cases hpm : p ∣ m
  · exact Or.inr (h.2 p hp hpm)
  · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hpm)

private theorem defect_eq_prime_gap {x b : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal (price x) m)
    (s : Finset ℕ) (hms : m.primeFactors ⊆ s) (hns : n.primeFactors ⊆ s) :
    actualDefect x b n = ∑ p ∈ s,
      goldenPrimeLocalObjective (price x) p (m.factorization p) -
      goldenPrimeLocalObjective (price x) p (n.factorization p) := by
  rw [actualDefect, pressure_eq_of_optimal hm hopt,
    golden_resource_objective_sum_on (price x) hm s hms,
    golden_resource_objective_sum_on (price x) hn s hns, sum_sub_distrib]

private theorem local_zero (lambda : ℝ) {p : ℕ} (hp : p.Prime) :
    goldenPrimeLocalObjective lambda p 0 = 0 := by
  rw [local_eq_layer_sum lambda hp 0]
  simp

private theorem local_one (lambda : ℝ) {p : ℕ} (hp : p.Prime) :
    goldenPrimeLocalObjective lambda p 1 =
      Real.log p * (goldenLayerMarginal p 1 - lambda) := by
  rw [local_eq_layer_sum lambda hp 1]
  simp

/-- The full actual defect dominates the forward weighted first-prime loss.
Every complementary prime direction is retained and nonnegative. -/
theorem forward_weighted_mass_le_defect {b x : ℝ} (hb : 1 < b) (hbx : b < x)
    {n : ℕ} (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal (price b) n) :
    forwardWeightedMass b x ≤ actualDefect x b n := by
  classical
  have hx : 1 < x := hb.trans hbx
  obtain ⟨m, hm, _, hmopt, _⟩ := optimal_layer_count_spec (price_pos hx)
  let s := m.primeFactors ∪ n.primeFactors ∪ forwardBand b x
  have hsprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact (mem_filter.mp hp).2.1
  have hband : forwardBand b x ⊆ s := subset_union_right
  rw [defect_eq_prime_gap hm hn hmopt s
    (subset_union_left.trans subset_union_left)
    (subset_union_right.trans subset_union_left)]
  refine le_trans (b := ∑ p ∈ forwardBand b x,
    goldenPrimeLocalObjective (price x) p (m.factorization p) -
      goldenPrimeLocalObjective (price x) p (n.factorization p))
    (sum_le_sum ?_) ?_
  · intro p hp
    have h := (mem_filter.mp hp).2
    have hz := forward_band_selection hb hbx hn hopt p hp
    have hl := local_gap_nonneg hx hm hmopt h.1 1
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [hz, local_zero (price x) h.1, sub_zero]
    rw [local_one (price x) h.1] at hl
    exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (first_layer_between_prices h.1).1.le _) hlog).trans
      (by linarith)
  · apply sum_le_sum_of_subset_of_nonneg hband
    intro p hp _
    exact local_gap_nonneg hx hm hmopt (hsprime p hp) _

private theorem local_prefix_le_first {x : ℝ} {p a : ℕ} (hp : p.Prime)
    (ha : 1 ≤ a) (hfirst : goldenLayerMarginal p 1 < price x) :
    goldenPrimeLocalObjective (price x) p a ≤
      Real.log p * (goldenLayerMarginal p 1 - price x) := by
  rw [local_eq_layer_sum (price x) hp a]
  have hmem : 1 ∈ Icc 1 a := mem_Icc.mpr ⟨le_rfl, ha⟩
  rw [← sum_erase_add _ _ hmem]
  have hrest : (∑ k ∈ (Icc 1 a).erase 1,
      Real.log p * (goldenLayerMarginal p k - price x)) ≤ 0 := by
    apply sum_nonpos
    intro k hk
    have hka := mem_Icc.mp (mem_erase.mp hk).2
    have horder : goldenLayerMarginal p k ≤ goldenLayerMarginal p 1 := by
      rcases eq_or_lt_of_le hka.1 with rfl | hlt
      · rfl
      · exact (golden_layer_strict_decrease hp (by omega) hlt).le
    exact mul_nonpos_of_nonneg_of_nonpos (Real.log_natCast_nonneg p)
      (sub_nonpos.mpr (horder.trans hfirst.le))
  linarith

/-- The shifted reverse band is paid by actual adopted first-layer deficits.
The original weak threshold criterion permits every tie outside this band. -/
theorem reverse_weighted_mass_le_defect {x b : ℝ} (hx : 1 < x) (hxb : x < b)
    {n : ℕ} (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal (price b) n) :
    reverseWeightedMass x b ≤ actualDefect x b n := by
  classical
  obtain ⟨m, hm, _, hmopt, _⟩ := optimal_layer_count_spec (price_pos hx)
  let s := m.primeFactors ∪ n.primeFactors ∪ reverseBand x b
  have hsprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact (mem_filter.mp hp).2.1
  have hband : reverseBand x b ⊆ s := subset_union_right
  rw [defect_eq_prime_gap hm hn hmopt s
    (subset_union_left.trans subset_union_left)
    (subset_union_right.trans subset_union_left)]
  refine le_trans (b := ∑ p ∈ reverseBand x b,
    goldenPrimeLocalObjective (price x) p (m.factorization p) -
      goldenPrimeLocalObjective (price x) p (n.factorization p))
    (sum_le_sum ?_) ?_
  · intro p hp
    have h := (mem_filter.mp hp).2
    have hz := forward_prime_absent hx hm hmopt h.1 h.2.1
    have ha := reverse_band_selection hx hxb hn hopt p hp
    have hfirst : goldenLayerMarginal p 1 < price x :=
      (first_layer_between_prices h.1).2.trans (price_strictAnti hx h.2.1)
    have hl := local_prefix_le_first h.1 ha hfirst
    have hweight := mul_le_mul_of_nonneg_left
      (sub_le_sub_left (first_layer_between_prices h.1).2.le (price x))
      (Real.log_natCast_nonneg p)
    rw [hz, local_zero (price x) h.1]
    nlinarith
  · apply sum_le_sum_of_subset_of_nonneg hband
    intro p hp _
    exact local_gap_nonneg hx hm hmopt (hsprime p hp) _

/- Finite prime atoms, not a free theta variable. The strict reverse atom is
   active on s<p; the forward atom activates at p+1. -/
private def forwardStep (b x s : ℝ) : ℝ :=
  ∑ p ∈ forwardBand b x, if (p : ℝ) + 1 ≤ s then Real.log p else 0

private def reverseStep (x b s : ℝ) : ℝ :=
  ∑ p ∈ reverseBand x b, if s < (p : ℝ) then Real.log p else 0

private theorem forward_step_nonneg (b x s : ℝ) : 0 ≤ forwardStep b x s := by
  apply sum_nonneg
  intro p _
  split_ifs <;> simp [Real.log_natCast_nonneg]

private theorem reverse_step_nonneg (x b s : ℝ) : 0 ≤ reverseStep x b s := by
  apply sum_nonneg
  intro p _
  split_ifs <;> simp [Real.log_natCast_nonneg]

private theorem theta_sub_eq_sdiff {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u =
      ∑ p ∈ Nat.primesLE ⌊v⌋₊ \ Nat.primesLE ⌊u⌋₊, Real.log p := by
  have hsub : Nat.primesLE ⌊u⌋₊ ⊆ Nat.primesLE ⌊v⌋₊ := by
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨h.1.trans (Nat.floor_mono huv), h.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← sum_sdiff hsub]
  ring

private theorem forward_step_eq_theta {b x s : ℝ} (hb : 1 < b)
    (hs : s ∈ Set.Icc b x) :
    forwardStep b x s =
      if b ≤ s - 1 then Chebyshev.theta (s - 1) - Chebyshev.theta b else 0 := by
  classical
  by_cases hbs : b ≤ s - 1
  · rw [if_pos hbs, theta_sub_eq_sdiff hbs]
    unfold forwardStep
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [forwardBand, mem_filter, mem_range, Nat.lt_succ_iff, mem_sdiff,
      Nat.mem_primesLE, Nat.le_floor_iff (by linarith : 0 ≤ x),
      Nat.le_floor_iff (by linarith : 0 ≤ s - 1),
      Nat.le_floor_iff (by linarith : 0 ≤ b)]
    constructor <;> intro h <;> grind
  · rw [if_neg hbs]
    apply sum_eq_zero
    intro p hp
    have h := (mem_filter.mp hp).2
    have hno : ¬ (p : ℝ) + 1 ≤ s := by linarith [h.2.1]
    simp [hno]

private theorem reverse_step_eq_theta {x b s : ℝ} (hx : 1 < x)
    (hs : s ∈ Set.Icc x b) :
    reverseStep x b s =
      if s ≤ b - 1 then Chebyshev.theta (b - 1) - Chebyshev.theta s else 0 := by
  classical
  by_cases hsb : s ≤ b - 1
  · rw [if_pos hsb, theta_sub_eq_sdiff hsb]
    unfold reverseStep
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [reverseBand, mem_filter, mem_range, Nat.lt_succ_iff, mem_sdiff,
      Nat.mem_primesLE, Nat.le_floor_iff (by linarith : 0 ≤ b),
      Nat.le_floor_iff (by linarith [hs.1] : 0 ≤ s),
      Nat.le_floor_iff (by linarith [hs.1] : 0 ≤ b - 1)]
    constructor <;> intro h <;> grind
  · rw [if_neg hsb]
    apply sum_eq_zero
    intro p hp
    have h := (mem_filter.mp hp).2
    have hno : ¬ s < (p : ℝ) := by linarith [h.2.2]
    simp [hno]

private theorem curvature_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn curvature (Set.Icc a b) := by
  intro s hs
  have hs1 : 1 < s := ha.trans_le hs.1
  have hs0 : s ≠ 0 := by linarith
  have hl : Real.log s ≠ 0 := (Real.log_pos hs1).ne'
  unfold curvature
  fun_prop

private theorem curvature_integrableOn {a b : ℝ} (ha : 1 < a) :
    IntegrableOn curvature (Set.Icc a b) :=
  (curvature_continuousOn ha).integrableOn_Icc

private theorem price_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt price (-curvature s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hl : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have hd := ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs0)).inv
    (mul_ne_zero hs0 hl)
  convert hd using 1 <;> simp only [price, curvature, one_div] <;>
    field_simp <;> ring

private theorem curvature_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ s in Set.Icc a b, curvature s) = price a - price b := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hcont : ContinuousOn (fun s => -price s) (Set.Icc a b) := by
    intro s hs
    exact ((price_hasDerivAt (ha.trans_le hs.1)).neg).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable curvature volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
    exact (curvature_integrableOn ha).mono_set Set.Ioc_subset_Icc_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun s hs => by simpa using (price_hasDerivAt (ha.trans hs.1)).neg) hi
  simpa only [neg_sub_neg] using h

private theorem curvature_anti {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    curvature v ≤ curvature u := by
  have hv : 1 < v := hu.trans_le huv
  have hlu := Real.log_pos hu
  have hlv := Real.log_pos hv
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  have repr (t : ℝ) (ht : 1 < t) :
      curvature t = (1 + 1 / Real.log t) / (t ^ 2 * Real.log t) := by
    unfold curvature
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    field_simp
    ring
  rw [repr v hv, repr u hu]
  have hnum : 1 + 1 / Real.log v ≤ 1 + 1 / Real.log u := by
    exact add_le_add_left (one_div_le_one_div_of_le hlu hlog) _
  have hden : u ^ 2 * Real.log u ≤ v ^ 2 * Real.log v := by
    gcongr
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

private theorem forward_atom_integrable {b x : ℝ} (hb : 1 < b) (p : ℕ) :
    IntegrableOn (fun s => curvature s *
      (if (p : ℝ) + 1 ≤ s then Real.log p else 0)) (Set.Icc b x) := by
  have h : IntegrableOn ((Set.Ici ((p : ℝ) + 1)).indicator
      (fun s => curvature s * Real.log p)) (Set.Icc b x) :=
    ((curvature_integrableOn hb).mul_const (Real.log p)).indicator measurableSet_Ici
  convert h using 1
  ext s
  simp only [Set.indicator_apply, Set.mem_Ici]
  split_ifs <;> simp [mul_comm]

private theorem reverse_atom_integrable {x b : ℝ} (hx : 1 < x) (p : ℕ) :
    IntegrableOn (fun s => curvature s *
      (if s < (p : ℝ) then Real.log p else 0)) (Set.Icc x b) := by
  have h : IntegrableOn ((Set.Iio (p : ℝ)).indicator
      (fun s => curvature s * Real.log p)) (Set.Icc x b) :=
    ((curvature_integrableOn hx).mul_const (Real.log p)).indicator measurableSet_Iio
  convert h using 1
  ext s
  simp only [Set.indicator_apply, Set.mem_Iio]
  split_ifs <;> simp [mul_comm]

private theorem forward_integrable {b x : ℝ} (hb : 1 < b) :
    IntegrableOn (fun s => curvature s * forwardStep b x s) (Set.Icc b x) := by
  simp only [forwardStep, mul_sum]
  exact integrable_finsetSum _ (fun p _ => forward_atom_integrable hb p)

private theorem reverse_integrable {x b : ℝ} (hx : 1 < x) :
    IntegrableOn (fun s => curvature s * reverseStep x b s) (Set.Icc x b) := by
  simp only [reverseStep, mul_sum]
  exact integrable_finsetSum _ (fun p _ => reverse_atom_integrable hx p)

private theorem forward_weighted_mass_eq_integral {b x : ℝ} (hb : 1 < b) :
    forwardWeightedMass b x = ∫ s in Set.Icc b x, curvature s * forwardStep b x s := by
  classical
  simp only [forwardStep, mul_sum]
  rw [integral_finsetSum _ (fun p _ => forward_atom_integrable hb p)]
  apply sum_congr rfl
  intro p hp
  have h := (mem_filter.mp hp).2
  have hp1 : 1 < (p : ℝ) + 1 := by
    have hpp := h.1.one_lt
    exact_mod_cast (show 1 < p + 1 by omega)
  have hpx : (p : ℝ) + 1 ≤ x := by linarith [h.2.2]
  have heq : (fun s : ℝ => curvature s *
      (if (p : ℝ) + 1 ≤ s then Real.log p else 0)) =
      (Set.Ici ((p : ℝ) + 1)).indicator (fun s => Real.log p * curvature s) := by
    ext s
    simp only [Set.indicator_apply, Set.mem_Ici]
    split_ifs <;> simp [mul_comm]
  rw [heq, setIntegral_indicator measurableSet_Ici]
  have hinter : Set.Icc b x ∩ Set.Ici ((p : ℝ) + 1) =
      Set.Icc ((p : ℝ) + 1) x := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor <;> intro hs <;> grind
  rw [hinter, integral_const_mul, curvature_integral hp1 hpx]

private theorem reverse_weighted_mass_eq_integral {x b : ℝ} (hx : 1 < x) :
    reverseWeightedMass x b = ∫ s in Set.Icc x b, curvature s * reverseStep x b s := by
  classical
  simp only [reverseStep, mul_sum]
  rw [integral_finsetSum _ (fun p _ => reverse_atom_integrable hx p)]
  apply sum_congr rfl
  intro p hp
  have h := (mem_filter.mp hp).2
  have heq : (fun s : ℝ => curvature s *
      (if s < (p : ℝ) then Real.log p else 0)) =
      (Set.Iio (p : ℝ)).indicator (fun s => Real.log p * curvature s) := by
    ext s
    simp only [Set.indicator_apply, Set.mem_Iio]
    split_ifs <;> simp [mul_comm]
  rw [heq, setIntegral_indicator measurableSet_Iio]
  have hinter : Set.Icc x b ∩ Set.Iio (p : ℝ) = Set.Ico x p := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor <;> intro hs <;> grind
  rw [hinter, ← integral_Icc_eq_integral_Ico,
    integral_const_mul, curvature_integral hx h.2.1.le]

private theorem rho_nonneg {epsilon H : ℝ} (heps : epsilon ≤ 1) (hH : 1 ≤ H) :
    0 ≤ rho epsilon H := by
  unfold rho
  apply mul_nonneg (sub_nonneg.mpr heps)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hH)

private theorem rho_le_one {epsilon H : ℝ} (heps0 : 0 ≤ epsilon)
    (hH : 1 ≤ H) : rho epsilon H ≤ 1 := by
  have hfactor : 0 ≤ 1 - 1 / H := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hH)
  have hinv : 0 ≤ 1 / H := by positivity
  unfold rho
  calc
    (1 - epsilon) * (1 - 1 / H) ≤ 1 * (1 - 1 / H) :=
      mul_le_mul_of_nonneg_right (by linarith) hfactor
    _ ≤ 1 := by linarith

private theorem shifted_mass_lower {epsilon H t : ℝ} (heps : epsilon ≤ 1)
    (hH : 0 < H) (ht : H ≤ t) :
    rho epsilon H * t ≤ (1 - epsilon) * (t - 1) := by
  have hscale : 1 ≤ t / H := (one_le_div hH).mpr ht
  have hshift : (1 - 1 / H) * t ≤ t - 1 := by
    nlinarith [hscale]
  exact mul_le_mul_of_nonneg_left hshift (sub_nonneg.mpr heps)

private theorem forward_long_mass {X epsilon H0 b x s : ℝ}
    (heps : epsilon ≤ 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hb : 1 < b) (hXb : X ≤ b) (hx2 : x ≤ 2 * X)
    (hs : s ∈ Set.Icc (b + (H0 + 1)) x) :
    rho epsilon (H0 + 1) * (s - b) ≤ forwardStep b x s := by
  have hbs : b ≤ s - 1 := by linarith [hs.1]
  rw [forward_step_eq_theta hb ⟨by linarith [hs.1], hs.2⟩, if_pos hbs]
  apply (shifted_mass_lower heps (by linarith : 0 < H0 + 1)
    (by linarith [hs.1] : H0 + 1 ≤ s - b)).trans
  exact htheta b (s - 1) hXb (by linarith [hs.1])
    (by linarith [hs.2]) (by linarith [hs.1])

private theorem reverse_long_mass {X epsilon H0 x b s : ℝ}
    (heps : epsilon ≤ 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hx : 1 < x) (hXx : X ≤ x) (hb2 : b ≤ 2 * X)
    (hs : s ∈ Set.Icc x (b - (H0 + 1))) :
    rho epsilon (H0 + 1) * (b - s) ≤ reverseStep x b s := by
  have hsb : s ≤ b - 1 := by linarith [hs.2]
  rw [reverse_step_eq_theta hx ⟨hs.1, by linarith [hs.2]⟩, if_pos hsb]
  apply (shifted_mass_lower heps (by linarith : 0 < H0 + 1)
    (by linarith [hs.2] : H0 + 1 ≤ b - s)).trans
  exact htheta s (b - 1) (hXx.trans hs.1) (by linarith [hs.2])
    (by linarith) (by linarith [hs.2])

private theorem linear_integral (q : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ s in Set.Icc a b, s - q) = ((b - q) ^ 2 - (a - q) ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (f := fun s : ℝ => (s - q) ^ 2 / 2)
    (by fun_prop)
    (fun s _ => by
      convert (((hasDerivAt_id s).sub_const q).pow 2).div_const 2 using 1 <;> ring)
    (by exact (continuous_id.sub continuous_const).intervalIntegrable _ _)
  convert h using 1 <;> ring

private theorem reverse_linear_integral (q : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ s in Set.Icc a b, q - s) = ((q - a) ^ 2 - (q - b) ^ 2) / 2 := by
  have heq : (fun s : ℝ => q - s) = fun s => -(s - q) := by funext s; ring
  rw [heq, integral_neg, linear_integral q hab]
  ring

private theorem forward_long_charge {X epsilon H0 b x : ℝ}
    (heps : epsilon ≤ 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hb : 1 < b) (hXb : X ≤ b) (hx2 : x ≤ 2 * X)
    (hlong : b + (H0 + 1) ≤ x) :
    rho epsilon (H0 + 1) / 2 * curvature x *
      ((x - b) ^ 2 - (H0 + 1) ^ 2) ≤ forwardWeightedMass b x := by
  let H := H0 + 1
  let r := rho epsilon H
  have hr : 0 ≤ r := rho_nonneg heps (by dsimp [H]; linarith)
  have hsub : Set.Icc (b + H) x ⊆ Set.Icc b x := by
    intro s hs
    exact ⟨by dsimp [H] at hs; linarith [hs.1], hs.2⟩
  have hmodel : IntegrableOn (fun s => curvature x * r * (s - b))
      (Set.Icc (b + H) x) := by
    exact ((continuous_const.mul continuous_const).mul
      (continuous_id.sub continuous_const)).continuousOn.integrableOn_Icc
  have hstep := forward_integrable (x := x) hb
  have hpoint : ∀ s ∈ Set.Icc (b + H) x,
      curvature x * r * (s - b) ≤ curvature s * forwardStep b x s := by
    intro s hs
    have hmass := forward_long_mass heps hH0 htheta hb hXb hx2 hs
    have hcurv := curvature_anti (hb.trans_le (hsub hs).1) hs.2
    have ht : 0 ≤ s - b := by linarith [(hsub hs).1]
    calc
      curvature x * r * (s - b) = curvature x * (r * (s - b)) := by ring
      _ ≤ curvature s * (r * (s - b)) :=
        mul_le_mul_of_nonneg_right hcurv (mul_nonneg hr ht)
      _ ≤ curvature s * forwardStep b x s :=
        mul_le_mul_of_nonneg_left hmass (curvature_pos (hb.trans_le (hsub hs).1)).le
  have hmono := setIntegral_mono_on hmodel (hstep.mono_set hsub)
    measurableSet_Icc hpoint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc b x)]
      (fun s => curvature s * forwardStep b x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (curvature_pos (hb.trans_le hs.1)).le (forward_step_nonneg b x s)
  have hdiscard := setIntegral_mono_set hstep hnonneg
    (Filter.Eventually.of_forall fun s hs => hsub hs)
  rw [integral_const_mul, linear_integral b hlong] at hmono
  rw [← forward_weighted_mass_eq_integral hb] at hdiscard
  have heq : curvature x * r * (((x - b) ^ 2 - ((b + H) - b) ^ 2) / 2) =
      rho epsilon (H0 + 1) / 2 * curvature x *
        ((x - b) ^ 2 - (H0 + 1) ^ 2) := by dsimp [r, H]; ring
  rw [heq] at hmono
  exact hmono.trans hdiscard

private theorem reverse_long_charge {X epsilon H0 x b : ℝ}
    (heps : epsilon ≤ 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hx : 1 < x) (hXx : X ≤ x) (hb2 : b ≤ 2 * X)
    (hlong : x ≤ b - (H0 + 1)) :
    rho epsilon (H0 + 1) / 2 * curvature b *
      ((x - b) ^ 2 - (H0 + 1) ^ 2) ≤ reverseWeightedMass x b := by
  let H := H0 + 1
  let r := rho epsilon H
  have hr : 0 ≤ r := rho_nonneg heps (by dsimp [H]; linarith)
  have hsub : Set.Icc x (b - H) ⊆ Set.Icc x b := by
    intro s hs
    exact ⟨hs.1, by dsimp [H] at hs; linarith [hs.2]⟩
  have hmodel : IntegrableOn (fun s => curvature b * r * (b - s))
      (Set.Icc x (b - H)) := by
    exact ((continuous_const.mul continuous_const).mul
      (continuous_const.sub continuous_id)).continuousOn.integrableOn_Icc
  have hstep := reverse_integrable (b := b) hx
  have hpoint : ∀ s ∈ Set.Icc x (b - H),
      curvature b * r * (b - s) ≤ curvature s * reverseStep x b s := by
    intro s hs
    have hmass := reverse_long_mass heps hH0 htheta hx hXx hb2 hs
    have hcurv := curvature_anti (hx.trans_le hs.1) (hsub hs).2
    have ht : 0 ≤ b - s := by linarith [(hsub hs).2]
    calc
      curvature b * r * (b - s) = curvature b * (r * (b - s)) := by ring
      _ ≤ curvature s * (r * (b - s)) :=
        mul_le_mul_of_nonneg_right hcurv (mul_nonneg hr ht)
      _ ≤ curvature s * reverseStep x b s :=
        mul_le_mul_of_nonneg_left hmass (curvature_pos (hx.trans_le hs.1)).le
  have hmono := setIntegral_mono_on hmodel (hstep.mono_set hsub)
    measurableSet_Icc hpoint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc x b)]
      (fun s => curvature s * reverseStep x b s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (curvature_pos (hx.trans_le hs.1)).le (reverse_step_nonneg x b s)
  have hdiscard := setIntegral_mono_set hstep hnonneg
    (Filter.Eventually.of_forall fun s hs => hsub hs)
  rw [integral_const_mul, reverse_linear_integral b hlong] at hmono
  rw [← reverse_weighted_mass_eq_integral hx] at hdiscard
  have heq : curvature b * r * (((b - x) ^ 2 - (b - (b - H)) ^ 2) / 2) =
      rho epsilon (H0 + 1) / 2 * curvature b *
        ((x - b) ^ 2 - (H0 + 1) ^ 2) := by dsimp [r, H]; ring
  rw [heq] at hmono
  exact hmono.trans hdiscard

/-- The primitive supplier is about Mathlib's actual Chebyshev theta.
No selection, weighted-defect, or quadratic-charge bridge is a premise. -/
def thetaCharge (epsilon H : ℝ) (x b : ℝ) : ℝ :=
  rho epsilon H / 2 * curvature (max x b) * max ((x - b) ^ 2 - H ^ 2) 0

/-- Q for every original-price optimizer, including every original equality
choice. The whole defect is used, the strict bands retain their one-unit
activation shift, and short distances (including equality) use nonnegativity. -/
theorem actual_optimizer_defect_ge_of_theta_interval_lower
    {X epsilon H0 x b : ℝ} (hX : 1 < X) (heps0 : 0 ≤ epsilon)
    (heps1 : epsilon < 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hxbounds : X ≤ x ∧ x ≤ 2 * X ∧ X ≤ b ∧ b ≤ 2 * X)
    {n : ℕ} (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal (price b) n) :
    thetaCharge epsilon (H0 + 1) x b ≤ actualDefect x b n := by
  have hx : 1 < x := hX.trans_le hxbounds.1
  have hb : 1 < b := hX.trans_le hxbounds.2.2.1
  by_cases hshort : (x - b) ^ 2 - (H0 + 1) ^ 2 ≤ 0
  · have hz : thetaCharge epsilon (H0 + 1) x b = 0 := by
      simp [thetaCharge, max_eq_right hshort]
    rw [hz]
    exact actual_defect_nonneg hx hn
  · have hsq : (H0 + 1) ^ 2 < (x - b) ^ 2 := by linarith
    by_cases hdir : b ≤ x
    · have hlong : b + (H0 + 1) ≤ x := by nlinarith
      have hcharge := forward_long_charge heps1.le hH0 htheta hb
        hxbounds.2.2.1 hxbounds.2.1 hlong
      have hweighted := forward_weighted_mass_le_defect hb (by linarith) hn hopt
      simpa [thetaCharge, max_eq_left (by linarith :
        0 ≤ (x - b) ^ 2 - (H0 + 1) ^ 2), max_eq_left hdir] using
        hcharge.trans hweighted
    · have hdir' : x ≤ b := le_of_not_ge hdir
      have hlong : x ≤ b - (H0 + 1) := by nlinarith
      have hcharge := reverse_long_charge heps1.le hH0 htheta hx
        hxbounds.1 hxbounds.2.2.2 hlong
      have hweighted := reverse_weighted_mass_le_defect hx (by linarith) hn hopt
      simpa [thetaCharge, max_eq_left (by linarith :
        0 ≤ (x - b) ^ 2 - (H0 + 1) ^ 2), max_eq_right hdir'] using
        hcharge.trans hweighted

/-- Exactly the real prime band (2 sqrt X,4 sqrt X], with no sampled substitute. -/
def reserveBand (X : ℝ) : Finset ℕ :=
  forwardBand (2 * Real.sqrt X) (4 * Real.sqrt X + 1)

/-- The ordinary band-count floor paid by the existing actual reserve supplier. -/
def reserveFloor (X : ℝ) : ℝ :=
  1 / (8 * (4 * Real.sqrt X + 1) * Real.log (4 * Real.sqrt X))

def paymentFraction (X H : ℝ) : ℝ :=
  curvature X * H ^ 2 / (2 * reserveFloor X)

private theorem reserve_band_mask {X A : ℝ} (hX : 25 ≤ X)
    (hA : X ≤ A ∧ A ≤ 2 * X) :
    D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.PrimeMask
      A (reserveBand X) := by
  intro p hp
  have h := (mem_filter.mp hp).2
  have hX0 : 0 ≤ X := by linarith
  have hu : 5 ≤ Real.sqrt X := by
    exact (Real.le_sqrt (by norm_num) hX0).mpr (by norm_num <;> linarith)
  have hu2 := Real.sq_sqrt hX0
  have hpl : 2 * Real.sqrt X < (p : ℝ) := h.2.1
  have hpu : (p : ℝ) ≤ 4 * Real.sqrt X := by linarith [h.2.2]
  have hsqp : (2 * Real.sqrt X) ^ 2 ≤ (p : ℝ) ^ 2 := by gcongr
  have hmargin := mul_nonneg (sub_nonneg.mpr hu)
    (show 0 ≤ Real.sqrt X + 1 by positivity)
  exact ⟨h.1, by nlinarith [hA.2], by nlinarith [hA.1]⟩

private theorem reserve_floor_pos {X : ℝ} (hX : 25 ≤ X) : 0 < reserveFloor X := by
  have hu : 5 ≤ Real.sqrt X :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num <;> linarith)
  have hlog : 0 < Real.log (4 * Real.sqrt X) := Real.log_pos (by linarith)
  unfold reserveFloor
  positivity

private theorem actual_reserve_ge_band_floor {X A : ℝ} (hX : 25 ≤ X)
    (hA : X ≤ A ∧ A ≤ 2 * X)
    (hcount : 2 * Real.sqrt X / (2 * Real.log (4 * Real.sqrt X)) ≤
      (reserveBand X).card) :
    reserveFloor X ≤
      D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.actualReserve A := by
  have hA1 : 1 < A := by linarith [hA.1]
  have hmask := reserve_band_mask hX hA
  have hsupply :=
    D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.actual_reserve_prime_mask
      hA1 (reserveBand X) hmask (n := 1) le_rfl
  let Y := 2 * Real.sqrt X
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hlog : 0 < Real.log (2 * Y) := by
    apply Real.log_pos
    have hu : 5 ≤ Real.sqrt X :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num <;> linarith)
    dsimp [Y]
    linarith
  have hterm : ∀ p ∈ reserveBand X,
      1 / (4 * Y * (2 * Y + 1)) ≤ 1 / (2 * (p : ℝ) * ((p : ℝ) + 1)) := by
    intro p hp
    have h := (mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast h.1.pos
    have hpu : (p : ℝ) ≤ 2 * Y := by dsimp [Y]; linarith [h.2.2]
    apply one_div_le_one_div_of_le (by positivity)
    have hden : 2 * (p : ℝ) * ((p : ℝ) + 1) ≤ 4 * Y * (2 * Y + 1) := by
      calc
        2 * (p : ℝ) * ((p : ℝ) + 1) ≤ 2 * (2 * Y) * (2 * Y + 1) := by gcongr
        _ = _ := by ring
    exact hden
  have hsum := sum_le_sum hterm
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hcount' : Y / (2 * Real.log (2 * Y)) ≤ (reserveBand X).card := by
    simpa [Y] using hcount
  have hcountmass := mul_le_mul_of_nonneg_right hcount'
    (show 0 ≤ 1 / (4 * Y * (2 * Y + 1)) by positivity)
  have hnorm : Y / (2 * Real.log (2 * Y)) * (1 / (4 * Y * (2 * Y + 1))) =
      reserveFloor X := by
    unfold reserveFloor
    have hYne := hY.ne'
    have hlne := hlog.ne'
    dsimp [Y] at *
    field_simp
    ring
  rw [hnorm] at hcountmass
  exact hcountmass.trans (hsum.trans (hsupply.1.trans hsupply.2.1))

/-- The live same-state consumer of Q. At A=log n the existing unrestricted
reserve pays c H²; the conclusion retains (1-omega) Res(A) and c(A-b)².
The count premise concerns the actual finite prime band, not the desired
reserve, charge, or signed Robin conclusion. No optimizer-size asymptotic is
used to manufacture the explicitly retained dyadic bounds. -/
theorem actual_optimizer_reserve_paid
    {X epsilon H0 b : ℝ} (hX : 25 ≤ X) (heps0 : 0 ≤ epsilon)
    (heps1 : epsilon < 1) (hH0 : 0 < H0)
    (htheta : ThetaIntervalSupplier X epsilon H0)
    (hcount : 2 * Real.sqrt X / (2 * Real.log (4 * Real.sqrt X)) ≤
      (reserveBand X).card)
    {n : ℕ} (hn : 1 ≤ n)
    (hAbounds : X ≤ Real.log n ∧ Real.log n ≤ 2 * X)
    (hbbounds : X ≤ b ∧ b ≤ 2 * X)
    (hopt : IsGoldenResourceOptimal (price b) n) :
    (1 - paymentFraction X (H0 + 1)) *
        D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.actualReserve
          (Real.log n) +
      rho epsilon (H0 + 1) / 2 * curvature (max (Real.log n) b) *
        (Real.log n - b) ^ 2 ≤
    D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.actualReserve
      (Real.log n) + actualDefect (Real.log n) b n := by
  let A := Real.log n
  let H := H0 + 1
  let c := rho epsilon H / 2 * curvature (max A b)
  let R := D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask.actualReserve A
  let w := paymentFraction X H
  have hX1 : 1 < X := by linarith
  have hA1 : 1 < A := hX1.trans_le hAbounds.1
  have hmax1 : 1 < max A b := hA1.trans_le (le_max_left _ _)
  have hrho0 : 0 ≤ rho epsilon H := rho_nonneg heps1.le (by dsimp [H]; linarith)
  have hrho1 : rho epsilon H ≤ 1 := rho_le_one heps0
    (by dsimp [H]; linarith)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (div_nonneg hrho0 (by norm_num)) (curvature_pos hmax1).le
  have hcurv : curvature (max A b) ≤ curvature X :=
    curvature_anti hX1 (hAbounds.1.trans (le_max_left _ _))
  have hc : c ≤ curvature X / 2 := by
    have hh := mul_le_mul (show rho epsilon H / 2 ≤ 1 / 2 by linarith)
      hcurv (curvature_pos hmax1).le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    dsimp [c]
    linarith
  have hr : 0 < reserveFloor X := reserve_floor_pos hX
  have hR : reserveFloor X ≤ R := actual_reserve_ge_band_floor hX hAbounds hcount
  have hw : 0 ≤ w := by
    dsimp [w, paymentFraction]
    exact div_nonneg (mul_nonneg (curvature_pos hX1).le (sq_nonneg H)) (by positivity)
  have hnorm : w * reserveFloor X = curvature X * H ^ 2 / 2 := by
    dsimp [w, paymentFraction]
    field_simp [hr.ne']
    ring
  have hpay : c * H ^ 2 ≤ w * R := by
    calc
      c * H ^ 2 ≤ curvature X / 2 * H ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg H)
      _ = w * reserveFloor X := by rw [hnorm]; ring
      _ ≤ w * R := mul_le_mul_of_nonneg_left hR hw
  have hQ := actual_optimizer_defect_ge_of_theta_interval_lower hX1 heps0 heps1 hH0
    htheta ⟨hAbounds.1, hAbounds.2, hbbounds.1, hbbounds.2⟩ hn hopt
  change c * max ((A - b) ^ 2 - H ^ 2) 0 ≤ actualDefect A b n at hQ
  have hraw := (mul_le_mul_of_nonneg_left
    (le_max_left ((A - b) ^ 2 - H ^ 2) 0) hc0).trans hQ
  change (1 - w) * R + c * (A - b) ^ 2 ≤ R + actualDefect A b n
  nlinarith [hpay, hraw]

end

end D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss

#print axioms D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.forward_weighted_mass_le_defect
#print axioms D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.reverse_weighted_mass_le_defect
#print axioms D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.actual_optimizer_defect_ge_of_theta_interval_lower
#print axioms D5.S3.Arith.GoldenResource.ActualOptimizerPrimeLoss.actual_optimizer_reserve_paid
