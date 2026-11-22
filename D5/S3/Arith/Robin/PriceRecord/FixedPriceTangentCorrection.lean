/- GID: D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Exact unit tangent correction for the literal fixed-support integer prime prefixes. -/

import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
import D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Tangent curvature on finite prime prefixes

The fixed-price and nonlinear integer minima are both attained. Their clock
increments give the lower and upper tangent-remainder bounds for the gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection

open Filter Finset Real
open scoped BigOperators Topology
open FixedSupportIntegerActivationEnvelope
  (supportedAdmissible integerValues integerInfimum clockIncrement tailCost linearCost)
open FixedLayerFiniteActivation (fixedPriceMinimum sum_local_minima_isLeast)
open FixedLayerAggregate (integer_loss_forms eulerTerm_le_twice_power)
open FixedPriceMinimizerClock (IsMinimizer fixed_price_minimizer_clock_tendsto)
open RealInfimumPrimeBoundary
  (prefixH prefixEll prefixPrice prefixH_atTop prefixEll_atTop eventual_prefix_domains)
open OwnClockFixedSupport
  (primeSupport theta terminalCost clock phi baseline ownPrice theta_le_clock
    tangentRemainder tangent_remainder_nonnegative)
open BoundaryPrimePrice (benefit)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity)
open D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature (loglog_tangent_gap_quadratic)

private def integerCost (S : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  phi S (fun p => (a p : ℝ)) - baseline S

private def IsIntegerMinimizer (S : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  supportedAdmissible S a ∧
    ∀ b : ℕ → ℕ, supportedAdmissible S b → integerCost S a ≤ integerCost S b

private lemma clock_sublevel {S : Finset ℕ} (hS : primeSupport S) (hH : 1 < theta S)
    {a : ℕ → ℕ} (ha : supportedAdmissible S a) {c : ℝ} (hc : integerCost S a ≤ c) :
    let T := clock S (fun p => (a p : ℝ))
    theta S ≤ T ∧ log T ≤ log (theta S) * exp c := by
  dsimp only
  have hle := theta_le_clock hS (x := fun p => (a p : ℝ)) (fun p hp => by
    change (1 : ℝ) ≤ (a p : ℝ)
    exact_mod_cast ha p hp)
  have htail : 0 ≤ tailCost S a := by
    unfold tailCost
    exact sum_nonneg (fun p hp => (eulerTerm_le_twice_power (hS p hp) (k := a p)).1)
  have hcost : integerCost S a =
      log (log (clock S (fun p => (a p : ℝ)))) - log (log (theta S)) + tailCost S a :=
    (integer_loss_forms hS ha).1
  have hloglog : log (log (clock S (fun p => (a p : ℝ)))) ≤ log (log (theta S)) + c := by
    linarith only [hc, hcost, htail]
  have hT := hH.trans_le hle
  refine ⟨hle, ?_⟩
  simpa only [exp_add, exp_log (log_pos hH)] using
    (log_le_iff_le_exp (log_pos hT)).mp hloglog

/-- The sublevel through the all-ones vector has representatives in a finite
product of positive exponent intervals. The objective depends only on support. -/
private theorem integer_infimum_attained {S : Finset ℕ} (hS : primeSupport S)
    (hH : 1 < theta S) :
    ∃ a : ℕ → ℕ, IsIntegerMinimizer S a ∧ integerCost S a = integerInfimum S := by
  classical
  let B := exp (log (theta S) * exp (integerCost S (fun _ => 1)))
  let K : ℕ → ℕ := fun p => Nat.ceil (B / log (p : ℝ))
  let extend : (∀ p : S, Fin (K p.val + 1)) → ℕ → ℕ :=
    fun v p => if hp : p ∈ S then (v ⟨p, hp⟩).val + 1 else 1
  let zero : ∀ p : S, Fin (K p.val + 1) := fun p => ⟨0, Nat.zero_lt_succ _⟩
  obtain ⟨v, _, hv⟩ := (Finset.univ : Finset (∀ p : S, Fin (K p.val + 1))).exists_min_image
    (fun w => integerCost S (extend w)) ⟨zero, mem_univ _⟩
  have hcongr (a b : ℕ → ℕ) (hab : ∀ p ∈ S, a p = b p) :
      integerCost S a = integerCost S b := by
    have hclock : clock S (fun p => (a p : ℝ)) = clock S (fun p => (b p : ℝ)) := by
      unfold clock
      exact sum_congr rfl (fun p hp => by
        change (a p : ℝ) * log (p : ℝ) = (b p : ℝ) * log (p : ℝ)
        rw [hab p hp])
    have hbenefit : (∑ p ∈ S, benefit (p : ℝ) (a p : ℝ)) =
        ∑ p ∈ S, benefit (p : ℝ) (b p : ℝ) :=
      sum_congr rfl (fun p hp => by rw [hab p hp])
    unfold integerCost phi
    rw [hclock, hbenefit]
  have ha : supportedAdmissible S (extend v) := by
    intro p hp
    simpa only [extend, dite_eq_left hp] using Nat.succ_le_succ (Nat.zero_le (v ⟨p, hp⟩).val)
  have hmin (b : ℕ → ℕ) (hb : supportedAdmissible S b) : integerCost S (extend v) ≤
      integerCost S b := by
    by_cases hbsub : integerCost S b ≤ integerCost S (fun _ => 1)
    · obtain ⟨hle, hlog⟩ := clock_sublevel hS hH hb hbsub
      have hB : clock S (fun p => (b p : ℝ)) ≤ B :=
        (log_le_iff_le_exp (zero_lt_one.trans (hH.trans_le hle))).mp hlog
      have hcap (p : S) : b p.val - 1 < K p.val + 1 := by
        have hterm : (b p.val : ℝ) * log (p.val : ℝ) ≤ clock S (fun q => (b q : ℝ)) := by
          unfold clock
          exact single_le_sum
            (fun q hq => mul_nonneg (Nat.cast_nonneg (b q)) (hS q hq).log_pos.le) p.property
        have hp : 0 < log (p.val : ℝ) := (hS p.val p.property).log_pos
        have hR : (b p.val : ℝ) ≤ (K p.val : ℝ) :=
          ((le_div_iff₀ hp).2 (hterm.trans hB)).trans (Nat.le_ceil _)
        have hN : b p.val ≤ K p.val := by exact_mod_cast hR
        exact Nat.lt_succ_of_le ((Nat.sub_le _ _).trans hN)
      let w : ∀ p : S, Fin (K p.val + 1) := fun p => ⟨b p.val - 1, hcap p⟩
      have hrep : integerCost S (extend w) = integerCost S b := by
        apply hcongr
        intro p hp
        simpa only [extend, dite_eq_left hp, w] using Nat.sub_add_cancel (hb p hp)
      exact (hv w (mem_univ w)).trans_eq hrep
    · have hrep : integerCost S (extend zero) = integerCost S (fun _ => 1) := by
        apply hcongr
        intro p hp
        simp [extend, hp, zero]
      exact ((hv zero (mem_univ zero)).trans_eq hrep).trans (le_of_lt (lt_of_not_ge hbsub))
  have hleast : IsLeast (integerValues S) (integerCost S (extend v)) := by
    refine ⟨⟨extend v, ha, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hmin b hb
  exact ⟨extend v, ⟨ha, hmin⟩, hleast.csInf_eq.symm⟩

/-- Take the supporting slope at the clock of the nonlinear minimizer.
For the general concave-coordinate rule, see Oleg R. Musin,
*Higher-order colossally abundant numbers*, arXiv:2609.33794v2, Theorem 2.2.
The primewise rule used by the clock theorem goes back to Alaoglu and Erdős,
*On highly composite and similar numbers* (1944), §3, Theorem 10.
Musin's §2.1 includes the treatment of ties. -/
private theorem own_price_minimizer {S : Finset ℕ} (hS : primeSupport S)
    (hH : 1 < theta S) {a : ℕ → ℕ} (ha : IsIntegerMinimizer S a) :
    IsMinimizer S (ownPrice S (fun p => (a p : ℝ))) a := by
  refine ⟨ha.1, ?_⟩
  intro b hb
  let Ta := clock S (fun p => (a p : ℝ))
  let Tb := clock S (fun p => (b p : ℝ))
  have hT (x : ℕ → ℕ) (hx : supportedAdmissible S x) :
      1 < clock S (fun p => (x p : ℝ)) :=
    hH.trans_le (theta_le_clock hS (fun p hp => by exact_mod_cast hx p hp))
  have hrem : 0 ≤ tangentRemainder Ta Tb :=
    (tangent_remainder_nonnegative (hT a ha.1) (hT b hb)).1
  have hDa : integerCost S a = terminalCost Ta - terminalCost (theta S) + tailCost S a :=
    (integer_loss_forms hS ha.1).1
  have hDb : integerCost S b = terminalCost Tb - terminalCost (theta S) + tailCost S b :=
    (integer_loss_forms hS hb).1
  have hmin := ha.2 b hb
  rw [hDa, hDb] at hmin
  have hlinear (x : ℕ → ℕ) :
      linearCost S (g Ta) x =
        g Ta * (clock S (fun p => (x p : ℝ)) - theta S) + tailCost S x := by
    calc
      _ = g Ta * clockIncrement S x + tailCost S x := by
        simp only [linearCost, clockIncrement, tailCost, mul_sum, sum_add_distrib, mul_assoc]
      _ = _ := by simp only [clockIncrement, clock, theta, sub_mul, one_mul, sum_sub_distrib]
  change linearCost S (g Ta) a ≤ linearCost S (g Ta) b
  rw [hlinear a, hlinear b]
  change g Ta * (Ta - theta S) + tailCost S a ≤ g Ta * (Tb - theta S) + tailCost S b
  unfold tangentRemainder at hrem
  nlinarith only [hrem, hmin]

private theorem log_mul_infimum_tendsto_zero :
    Tendsto (fun P => prefixEll P * integerInfimum (Nat.primesLE P)) atTop (𝓝 0) := by
  have h := IntegerInfimumSecondOrder.actual_integer_infimum_second_order.div_atTop prefixEll_atTop
  have hcentered : Tendsto (fun P => sqrt (prefixH P) * prefixEll P *
      integerInfimum (Nat.primesLE P) - 2 * sqrt 2) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards [prefixEll_atTop.eventually_gt_atTop 0] with P hL
    exact mul_div_cancel_left₀ _ hL.ne'
  have hlead := hcentered.add_const (2 * sqrt 2)
  simp only [sub_add_cancel, zero_add] at hlead
  apply (hlead.div_atTop (tendsto_sqrt_atTop.comp prefixH_atTop)).congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
  dsimp only [Function.comp_apply]
  rw [mul_assoc, mul_div_cancel_left₀ _ (sqrt_pos.mpr hH).ne']

private theorem own_price_ratio {a : ℕ → ℕ → ℕ}
    (ha : ∀ᶠ P in atTop, supportedAdmissible (Nat.primesLE P) (a P) ∧
      integerCost (Nat.primesLE P) (a P) = integerInfimum (Nat.primesLE P)) :
    Tendsto (fun P => ownPrice (Nat.primesLE P) (fun p => (a P p : ℝ)) / prefixPrice P)
      atTop (𝓝 1) := by
  let I : ℕ → ℝ := fun P => integerInfimum (Nat.primesLE P)
  let q : ℕ → ℝ := fun P =>
    ownPrice (Nat.primesLE P) (fun p => (a P p : ℝ)) / prefixPrice P
  have hI : Tendsto I atTop (𝓝 0) := by
    apply (log_mul_infimum_tendsto_zero.div_atTop prefixEll_atTop).congr'
    filter_upwards [prefixEll_atTop.eventually_gt_atTop 0] with P hL
    exact mul_div_cancel_left₀ _ hL.ne'
  have hbound : ∀ᶠ P in atTop, 0 ≤ 1 - q P ∧ 1 - q P ≤ 4 * (prefixEll P * I P) := by
    filter_upwards [ha, eventual_prefix_domains, prefixH_atTop.eventually_gt_atTop 1,
      hI.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with P hAP hd hH hIlt
    let H := prefixH P
    let T := clock (Nat.primesLE P) (fun p => (a P p : ℝ))
    let x := log (T / H)
    have hL1 : 1 ≤ log H := hd.2.2.1
    have hH0 : 0 < H := zero_lt_one.trans hH
    have hL : 0 < log H := log_pos hH
    obtain ⟨hle, hlog⟩ := clock_sublevel hd.1 hH hAP.1 hAP.2.le
    have hHT : H ≤ T := hle
    have hT : 1 < T := hH.trans_le hHT
    have hT0 : 0 < T := zero_lt_one.trans hT
    have hlogs : log H ≤ log T := log_le_log hH0 hHT
    have hx : x = log T - log H := log_div hT0.ne' hH0.ne'
    have hx0 : 0 ≤ x := by rw [hx]; exact sub_nonneg.mpr hlogs
    have hlog' : log T ≤ log H * exp (I P) := hlog
    have hI0 : 0 ≤ I P := by
      apply Real.one_le_exp_iff.mp
      apply (mul_le_mul_iff_of_pos_left hL).mp
      rw [mul_one]
      exact hlogs.trans hlog'
    have hexp : exp (I P) - 1 ≤ 2 * I P :=
      (FixedLayerAggregate.exp_sub_one_bounds hI0 hIlt.le).2
    have hxupper : x ≤ 2 * (log H * I P) := by
      rw [hx]
      nlinarith only [hlog', mul_le_mul_of_nonneg_left hexp hL.le]
    have hq : q P = (H / T) * (log H / log T) := by
      change (1 / (T * log T)) / (1 / (H * log H)) = _
      field_simp [hH0.ne', hT0.ne', hL.ne', (log_pos hT).ne'] <;> ring
    have hr0 : 0 ≤ H / T := div_nonneg hH0.le hT0.le
    have hr1 : H / T ≤ 1 := (div_le_iff₀ hT0).2 (by simpa only [one_mul] using hHT)
    have hs0 : 0 ≤ log H / log T := div_nonneg hL.le (log_pos hT).le
    have hs1 : log H / log T ≤ 1 :=
      (div_le_iff₀ (log_pos hT)).2 (by simpa only [one_mul] using hlogs)
    have hr : 1 - H / T ≤ x := by
      simpa only [inv_div] using one_sub_inv_le_log_of_pos (div_pos hT0 hH0)
    have hs : 1 - log H / log T ≤ x := by
      rw [one_sub_div (log_pos hT).ne', ← hx]
      exact div_le_self hx0 (hL1.trans hlogs)
    refine ⟨sub_nonneg.mpr ?_, ?_⟩
    · rw [hq]
      calc
        (H / T) * (log H / log T) ≤ 1 * (log H / log T) :=
          mul_le_mul_of_nonneg_right hr1 hs0
        _ ≤ 1 := by simpa only [one_mul] using hs1
    · change 1 - q P ≤ 4 * (log H * I P)
      calc
        1 - q P = (1 - H / T) + H / T * (1 - log H / log T) := by rw [hq]; ring
        _ ≤ x + x := add_le_add hr
          ((mul_le_mul_of_nonneg_left hs hr0).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hx0))
        _ ≤ _ := by linarith only [hxupper]
  have hu := (log_mul_infimum_tendsto_zero.const_mul 4).const_sub 1
  simp only [mul_zero, sub_zero] at hu
  change Tendsto q atTop (𝓝 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hu tendsto_const_nhds
    (hbound.mono fun _ h => by linarith only [h.2])
    (hbound.mono fun _ h => by linarith only [h.1])

private theorem scaled_quadratic_tendsto {T u : ℕ → ℝ}
    (hHT : ∀ᶠ P in atTop, prefixH P ≤ T P)
    (hrel : Tendsto (fun P => T P / prefixH P) atTop (𝓝 1))
    (hu : Tendsto (fun P => u P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2))) :
    Tendsto (fun P => prefixH P * log (prefixH P) * (activationDensity (T P) * u P ^ 2 / 2))
      atTop (𝓝 1) := by
  have hT : ∀ᶠ P in atTop, 1 < T P := by
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1, hHT] with P hH hle
    exact hH.trans_le hle
  have htop : Tendsto (fun P => log (T P)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_mono' atTop hHT prefixH_atTop)
  have hequiv := Asymptotics.isEquivalent_of_tendsto_one (u := T) (v := prefixH) hrel
  have hlogRel : Tendsto (fun P => log (T P) / log (prefixH P)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (prefixEll_atTop.eventually_ne_atTop 0)).mp
      (hequiv.log prefixH_atTop)
  have hu₂ := (hu.pow 2).div_const 2
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), div_self (by norm_num : (2 : ℝ) ≠ 0)] at hu₂
  have hden := (hrel.pow 2).mul hlogRel
  simp only [one_pow, one_mul] at hden
  have hlog := (htop.const_div_atTop (1 : ℝ)).const_add 1
  rw [add_zero] at hlog
  have h := (hu₂.div hden one_ne_zero).mul hlog
  simp only [div_one, one_mul] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, hT] with P hH hTP
  have hH0 := zero_lt_one.trans hH
  change (u P / sqrt (prefixH P)) ^ 2 / 2 /
      ((T P / prefixH P) ^ 2 * (log (T P) / log (prefixH P))) * (1 + 1 / log (T P)) =
    prefixH P * log (prefixH P) * (activationDensity (T P) * u P ^ 2 / 2)
  rw [div_pow, sq_sqrt hH0.le]
  unfold activationDensity
  field_simp [hH0.ne', (log_pos hH).ne', (zero_lt_one.trans hTP).ne', (log_pos hTP).ne']

private theorem scaled_remainder_tendsto {u : ℕ → ℝ}
    (hu₀ : ∀ᶠ P in atTop, 0 ≤ u P)
    (hu : Tendsto (fun P => u P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2))) :
    Tendsto (fun P => prefixH P * log (prefixH P) *
      tangentRemainder (prefixH P) (prefixH P + u P)) atTop (𝓝 1) := by
  have hHT : ∀ᶠ P in atTop, prefixH P ≤ prefixH P + u P :=
    hu₀.mono fun _ h => le_add_of_nonneg_right h
  have hrel : Tendsto (fun P => (prefixH P + u P) / prefixH P) atTop (𝓝 1) := by
    have h := (hu.div_atTop (tendsto_sqrt_atTop.comp prefixH_atTop)).const_add 1
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    change 1 + u P / sqrt (prefixH P) / sqrt (prefixH P) = (prefixH P + u P) / prefixH P
    rw [div_div, ← pow_two, sq_sqrt hH.le, add_div, div_self hH.ne']
  have hbase : Tendsto (fun P => prefixH P / prefixH P) atTop (𝓝 1) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [prefixH_atTop.eventually_ne_atTop 0] with P hH
    exact (div_self hH).symm
  have hbounds : ∀ᶠ P in atTop,
      let H := prefixH P
      let T := H + u P
      H * log H * (activationDensity T * u P ^ 2 / 2) ≤ H * log H * tangentRemainder H T ∧
      H * log H * tangentRemainder H T ≤ H * log H * (activationDensity H * u P ^ 2 / 2) := by
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1, hHT] with P hH hle
    let H := prefixH P
    let T := H + u P
    have hHT' : H ≤ T := hle
    have hT : 1 < T := hH.trans_le hHT'
    have hdiff : T - H = u P := by dsimp only [T]; ring
    have hq := loglog_tangent_gap_quadratic (a := H) hH hT
    dsimp only at hq
    rw [max_eq_right hHT', min_eq_left hHT'] at hq
    have hq' : activationDensity T * u P ^ 2 / 2 ≤ tangentRemainder H T ∧
        tangentRemainder H T ≤ activationDensity H * u P ^ 2 / 2 := by
      have hrem : tangentRemainder H T =
          log (log H) + (T - H) / (H * log H) - log (log T) := by
        simp only [tangentRemainder, terminalCost, g, div_eq_mul_inv]
        ring
      rw [hrem]
      simpa only [activationDensity, add_comm (log T) 1, add_comm (log H) 1, hdiff] using hq
    have hpos : 0 ≤ H * log H := mul_nonneg (zero_lt_one.trans hH).le (log_pos hH).le
    exact ⟨mul_le_mul_of_nonneg_left hq'.1 hpos, mul_le_mul_of_nonneg_left hq'.2 hpos⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (scaled_quadratic_tendsto hHT hrel hu)
    (scaled_quadratic_tendsto (Eventually.of_forall fun _ => le_rfl) hbase hu)
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- On the literal prime prefix, the fixed-price minimum minus the nonlinear
integer infimum is asymptotic to `1 / (H * log H)`. -/
theorem fixed_price_tangent_correction_tendsto :
    Tendsto (fun P : ℕ =>
      prefixH P * log (prefixH P) *
        (fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) -
          integerInfimum (Nat.primesLE P))) atTop (𝓝 1) := by
  classical
  have hex (P : ℕ) : ∃ a b : ℕ → ℕ,
      (1 < prefixH P ∧ primeSupport (Nat.primesLE P) ∧ 0 < prefixPrice P) →
      (IsMinimizer (Nat.primesLE P) (prefixPrice P) a ∧
        linearCost (Nat.primesLE P) (prefixPrice P) a =
          fixedPriceMinimum (Nat.primesLE P) (prefixPrice P)) ∧
      (IsIntegerMinimizer (Nat.primesLE P) b ∧
        integerCost (Nat.primesLE P) b = integerInfimum (Nat.primesLE P)) := by
    by_cases hd : 1 < prefixH P ∧ primeSupport (Nat.primesLE P) ∧ 0 < prefixPrice P
    · have hleast := sum_local_minima_isLeast hd.2.1 hd.2.2
      obtain ⟨a, ha, hva⟩ := hleast.1
      have hmin : IsMinimizer (Nat.primesLE P) (prefixPrice P) a := by
        refine ⟨ha, fun c hc => ?_⟩
        exact hva.le.trans (hleast.2 ⟨c, hc, rfl⟩)
      have hVa : linearCost (Nat.primesLE P) (prefixPrice P) a =
          fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) :=
        hva.trans hleast.csInf_eq.symm
      obtain ⟨b, hb⟩ := integer_infimum_attained hd.2.1 hd.1
      exact ⟨a, b, fun _ => ⟨⟨hmin, hVa⟩, hb⟩⟩
    · exact ⟨fun _ => 1, fun _ => 1, fun h => (hd h).elim⟩
  choose a b hab using hex
  have hdomain : ∀ᶠ P in atTop,
      1 < prefixH P ∧ primeSupport (Nat.primesLE P) ∧ 0 < prefixPrice P := by
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1, eventual_prefix_domains] with P hH hd
    exact ⟨hH, hd.1, hd.2.2.2.1⟩
  have ha : ∀ᶠ P in atTop, IsMinimizer (Nat.primesLE P) (prefixPrice P) (a P) :=
    hdomain.mono fun P hd => (hab P hd).1.1
  have hrel₀ : Tendsto (fun P => prefixPrice P / prefixPrice P) atTop (𝓝 1) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hdomain] with P hd
    exact (div_self hd.2.2.ne').symm
  have hrel₁ := own_price_ratio (a := b) (hdomain.mono fun P hd =>
    ⟨(hab P hd).2.1.1, (hab P hd).2.2⟩)
  have hown : ∀ᶠ P in atTop,
      IsMinimizer (Nat.primesLE P) (ownPrice (Nat.primesLE P) (fun p => (b P p : ℝ))) (b P) :=
    hdomain.mono fun P hd => own_price_minimizer hd.2.1 hd.1 (hab P hd).2.1
  have haClock := fixed_price_minimizer_clock_tendsto hrel₀ ha
  have hbClock := fixed_price_minimizer_clock_tendsto hrel₁ hown
  have hclock (P : ℕ) (x : ℕ → ℕ) :
      clock (Nat.primesLE P) (fun p => (x p : ℝ)) =
        prefixH P + clockIncrement (Nat.primesLE P) x := by
    have hinc : clockIncrement (Nat.primesLE P) x =
        clock (Nat.primesLE P) (fun p => (x p : ℝ)) - prefixH P := by
      simp only [clockIncrement, clock, prefixH, theta, sub_mul, one_mul, sum_sub_distrib]
    rw [hinc]
    ring
  have hnonneg (P : ℕ) (hs : primeSupport (Nat.primesLE P)) {x : ℕ → ℕ}
      (hx : supportedAdmissible (Nat.primesLE P) x) : 0 ≤ clockIncrement (Nat.primesLE P) x := by
    have hle : prefixH P ≤ clock (Nat.primesLE P) (fun p => (x p : ℝ)) :=
      theta_le_clock hs (fun p hp => by exact_mod_cast hx p hp)
    rw [hclock] at hle
    linarith only [hle]
  have ha₀ : ∀ᶠ P in atTop, 0 ≤ clockIncrement (Nat.primesLE P) (a P) :=
    hdomain.mono fun P hd => hnonneg P hd.2.1 (hab P hd).1.1.1
  have hb₀ : ∀ᶠ P in atTop, 0 ≤ clockIncrement (Nat.primesLE P) (b P) :=
    hdomain.mono fun P hd => hnonneg P hd.2.1 (hab P hd).2.1.1
  have hbounds : ∀ᶠ P in atTop,
      let H := prefixH P
      let V := fixedPriceMinimum (Nat.primesLE P) (prefixPrice P)
      let I := integerInfimum (Nat.primesLE P)
      H * log H * tangentRemainder H (H + clockIncrement (Nat.primesLE P) (a P)) ≤
          H * log H * (V - I) ∧
        H * log H * (V - I) ≤
          H * log H * tangentRemainder H (H + clockIncrement (Nat.primesLE P) (b P)) := by
    filter_upwards [hdomain] with P hd
    dsimp only
    rw [← hclock P (a P), ← hclock P (b P)]
    obtain ⟨⟨haP, hVa⟩, ⟨hbP, hIb⟩⟩ := hab P hd
    have hforms (x : ℕ → ℕ) (hx : supportedAdmissible (Nat.primesLE P) x) :
        linearCost (Nat.primesLE P) (prefixPrice P) x = integerCost (Nat.primesLE P) x +
          tangentRemainder (prefixH P) (clock (Nat.primesLE P) (fun p => (x p : ℝ))) :=
      (integer_loss_forms hd.2.1 hx).2
    have hfa := hforms (a P) haP.1
    have hfb := hforms (b P) hbP.1
    have hlinear := haP.2 (b P) hbP.1
    have hinteger := hbP.2 (a P) haP.1
    have hs : 0 ≤ prefixH P * log (prefixH P) :=
      mul_nonneg (zero_lt_one.trans hd.1).le (log_pos hd.1).le
    constructor <;> apply mul_le_mul_of_nonneg_left _ hs
    · linarith only [hfa, hVa, hinteger, hIb]
    · linarith only [hfb, hVa, hlinear, hIb]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (scaled_remainder_tendsto ha₀ haClock) (scaled_remainder_tendsto hb₀ hbClock)
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

end D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
