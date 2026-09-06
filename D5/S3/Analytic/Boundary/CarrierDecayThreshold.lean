/- GID: D5/S3/Analytic/Boundary/CarrierDecayThreshold
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/CarrierDecayThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A power-log counting bound gives the exact strict and endpoint summability thresholds. -/

/- Six-route duplicate and library-search audit (2026-09-04):
   * D5 searches covered counting functions, partial summation, sparse series, decay thresholds,
     `Nat.count`, logarithmic weights, and summability. No exact frozen owner was found.
   * The closest D5 result, `summable_log_moment_of_dyadic_count`, assumes supplied shells,
     natural log exponents, and the special weight `(log n)^m/n`, so it is not an exact hit.
   * Pinned Mathlib has no theorem giving these two thresholds from an eventual counting bound.
     Its exact shell-partition, natural-count, p-series, subpower-log, and geometric-series lemmas
     are applied below, as is D5's G-plane logarithmic quotient limit.
   * GitHub code searches for `Nat.count` with `Summable` and for summable counting functions in
     Lean returned no third-party hit. The source atom remains residual-open on current dev.
-/

import D5.S3.Weil.ZetaPntBase.LogBasic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped BigOperators Topology

namespace D5.S3.Analytic.Boundary.CarrierDecayThreshold

/-- The counting function of `A`, counting its elements strictly below the natural cutoff. -/
noncomputable def carrierCountingFunction (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (· ∈ A) n

private lemma tendsto_count_majorant_zero_of_delta_neg
    (C delta beta : ℝ) (hdelta : delta < 0) :
    Tendsto (fun n : ℕ => C * (n : ℝ) ^ delta / Real.log n ^ beta)
      atTop (𝓝 0) := by
  have hreal :
      Tendsto (fun x : ℝ => C * x ^ delta / Real.log x ^ beta) atTop (𝓝 0) := by
    have hbase := Real.tendsto_pow_log_div_pow_atTop (-delta) (-beta) (by linarith)
    have hmul := hbase.const_mul C
    simpa only [mul_zero] using hmul.congr' (by
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hx0 : 0 ≤ x := by linarith
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
      have hxpow : x ^ delta = (x ^ (-delta))⁻¹ := by
        calc
          x ^ delta = x ^ (-(-delta)) := by congr 1; ring
          _ = (x ^ (-delta))⁻¹ := Real.rpow_neg hx0 (-delta)
      rw [Real.rpow_neg hlog0, hxpow]
      ring)
  exact hreal.comp tendsto_natCast_atTop_atTop

private lemma tendsto_count_majorant_zero_of_delta_zero
    (C delta beta : ℝ) (hdelta : delta = 0) (hbeta : 0 < beta) :
    Tendsto (fun n : ℕ => C * (n : ℝ) ^ delta / Real.log n ^ beta)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ (-beta)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hbeta
  have hlogpow : Tendsto (fun x : ℝ => Real.log x ^ (-beta)) atTop (𝓝 0) :=
    hpow.comp Real.tendsto_log_atTop
  have hmul := hlogpow.const_mul C
  have hreal :
      Tendsto (fun x : ℝ => C * x ^ delta / Real.log x ^ beta) atTop (𝓝 0) := by
    simpa only [mul_zero] using hmul.congr' (by
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
      rw [hdelta, Real.rpow_zero, Real.rpow_neg hlog0]
      ring)
  exact hreal.comp tendsto_natCast_atTop_atTop

private lemma finite_of_eventually_count_le_of_majorant_tendsto_zero
    (A : Set ℕ) (g : ℕ → ℝ)
    (hcount : ∀ᶠ n : ℕ in atTop, (carrierCountingFunction A n : ℝ) ≤ g n)
    (hg : Tendsto g atTop (𝓝 0)) :
    A.Finite := by
  classical
  by_contra hfinite
  have hsmall : ∀ᶠ n : ℕ in atTop, g n < 1 :=
    hg.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hcount.and hsmall)
  obtain ⟨a, haA, haN⟩ := Set.Infinite.exists_gt hfinite N
  have h := hN (a + 1) (by omega)
  have hcount_one : 1 ≤ carrierCountingFunction A (a + 1) := by
    rw [carrierCountingFunction, Nat.count_succ, if_pos haA]
    omega
  have hcount_one_real : (1 : ℝ) ≤ (carrierCountingFunction A (a + 1) : ℝ) := by
    exact_mod_cast hcount_one
  linarith

private noncomputable def shell (A : Set ℕ) (j : ℕ) : Finset A := by
  classical
  exact (((Finset.range (2 ^ (j + 1))).subtype (· ∈ A)).filter
    (fun n => Nat.log 2 n = j))

private lemma mem_shell_iff (A : Set ℕ) (j : ℕ) (n : A) :
    n ∈ shell A j ↔ Nat.log 2 n = j := by
  classical
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    have hnupper : (n : ℕ) < 2 ^ (j + 1) := by
      by_cases hn0 : (n : ℕ) = 0
      · rw [hn0]
        positivity
      · simpa [hn, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n : ℕ)
    simp [shell, hn, hnupper]

private lemma shell_card_le_count (A : Set ℕ) (j : ℕ) :
    (shell A j).card ≤ carrierCountingFunction A (2 ^ (j + 1)) := by
  classical
  calc
    (shell A j).card ≤ ((Finset.range (2 ^ (j + 1))).subtype (· ∈ A)).card :=
      Finset.card_filter_le _ _
    _ = carrierCountingFunction A (2 ^ (j + 1)) := by
      rw [carrierCountingFunction, Nat.count_eq_card_filter_range]
      simp

private lemma summable_on_finite_set (A : Set ℕ) (hA : A.Finite) (q : ℝ) :
    Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-q)) := by
  classical
  let _ : Finite A := hA
  rw [← summable_subtype_iff_indicator]
  exact Summable.of_finite

private lemma summable_of_shell_majorant
    (A : Set ℕ) (q : ℝ) (hq : 0 < q) (g : ℕ → ℝ)
    (hg : Summable g)
    (hcount : ∀ᶠ j : ℕ in atTop,
      (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) *
          (2 : ℝ) ^ (-(q * j)) ≤ g j) :
    Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-q)) := by
  classical
  let moment : A → ℝ := fun n => ((n : ℕ) : ℝ) ^ (-q)
  have hmoment_nonneg : ∀ n, 0 ≤ moment n := by
    intro n
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hshell_unique :
      ∀ n : A, ∃! j : ℕ, n ∈ ({x : A | x ∈ shell A j} : Set A) := by
    intro n
    refine ⟨Nat.log 2 n, (mem_shell_iff A (Nat.log 2 n) n).2 rfl, ?_⟩
    intro j hj
    exact (mem_shell_iff A j n).1 hj |>.symm
  rw [← summable_subtype_iff_indicator]
  change Summable moment
  rw [summable_partition hmoment_nonneg hshell_unique]
  constructor
  · intro j
    exact Summable.of_finite
  · refine Summable.of_norm_bounded_eventually_nat hg ?_
    filter_upwards [hcount] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => hmoment_nonneg _)]
    let shellMajorant : ℝ := (2 : ℝ) ^ (-(q * j))
    have hshellMajorant_nonneg : 0 ≤ shellMajorant := Real.rpow_nonneg (by norm_num) _
    have hterm : ∀ n ∈ shell A j, moment n ≤ shellMajorant := by
      intro n hn
      by_cases hn0 : (n : ℕ) = 0
      · have hnegq : -q ≠ 0 := by linarith
        rw [show moment n = 0 by simp [moment, hn0, Real.zero_rpow hnegq]]
        exact hshellMajorant_nonneg
      · have hlowerNat : 2 ^ j ≤ (n : ℕ) := by
          simpa [(mem_shell_iff A j n).1 hn] using Nat.pow_log_le_self 2 hn0
        have hlower : (2 : ℝ) ^ j ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hlowerNat
        calc
          moment n ≤ ((2 : ℝ) ^ j) ^ (-q) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlower (by linarith)
          _ = shellMajorant := by
            simp only [shellMajorant, ← Real.rpow_natCast]
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring
    have hsumBound :
        (∑' n : {x : A | x ∈ shell A j}, moment n) ≤
          ((shell A j).card : ℝ) * shellMajorant := by
      rw [tsum_fintype]
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul Finset.univ
          (fun n : {x : A | x ∈ shell A j} => moment n) shellMajorant
          (fun n _ => hterm n n.property)
    calc
      (∑' n : {x : A | x ∈ shell A j}, moment n) ≤
          ((shell A j).card : ℝ) * shellMajorant := hsumBound
      _ ≤ (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) * shellMajorant := by
        gcongr
        exact_mod_cast shell_card_le_count A j
      _ ≤ g j := by simpa [shellMajorant] using hj

private lemma dyadic_rpow_identity (a q : ℝ) (j : ℕ) :
    (((2 ^ (j + 1) : ℕ) : ℝ) ^ a) * (2 : ℝ) ^ (-(q * j)) =
      (2 : ℝ) ^ a * ((2 : ℝ) ^ (a - q)) ^ j := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

private lemma dyadic_tendsto_atTop :
    Tendsto (fun j : ℕ => 2 ^ (j + 1)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (r := 2) (by omega)).comp
    (tendsto_add_atTop_nat 1)

private lemma strict_case
    (A : Set ℕ) (C delta beta q : ℝ)
    (hcount : ∀ᶠ n : ℕ in atTop,
      (carrierCountingFunction A n : ℝ) ≤
        C * (n : ℝ) ^ delta / Real.log n ^ beta)
    (hdelta : 0 ≤ delta) (hq : delta < q) :
    Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-q)) := by
  have hqpos : 0 < q := hdelta.trans_lt hq
  let epsilon : ℝ := (q - delta) / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  by_cases hbeta : 0 ≤ beta
  · let ratio : ℝ := (2 : ℝ) ^ (delta - q)
    have hratio0 : 0 ≤ ratio := Real.rpow_nonneg (by norm_num) _
    have hratio1 : ratio < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    let g : ℕ → ℝ := fun j => |C| * (2 : ℝ) ^ delta * ratio ^ j
    have hg : Summable g := by
      exact (summable_geometric_of_lt_one hratio0 hratio1).mul_left
        (|C| * (2 : ℝ) ^ delta)
    apply summable_of_shell_majorant A q hqpos g hg
    have hbound := dyadic_tendsto_atTop.eventually hcount
    have hrealTop : Tendsto (fun j : ℕ => ((2 ^ (j + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp dyadic_tendsto_atTop
    have hloglarge : ∀ᶠ j : ℕ in atTop,
        1 ≤ Real.log (((2 ^ (j + 1) : ℕ) : ℝ)) :=
      (Real.tendsto_log_atTop.comp hrealTop).eventually_ge_atTop 1
    filter_upwards [hbound, hloglarge] with j hj hlog
    let U : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
    have hUpos : 0 < U := by dsimp [U]; positivity
    have hden : 1 ≤ Real.log U ^ beta := by
      exact Real.one_le_rpow hlog hbeta
    have hcountAbs : (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) ≤
        |C| * U ^ delta / Real.log U ^ beta := by
      exact hj.trans (by
        dsimp [U]
        gcongr
        exact le_abs_self C)
    calc
      (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) * (2 : ℝ) ^ (-(q * j)) ≤
          (|C| * U ^ delta / Real.log U ^ beta) *
            (2 : ℝ) ^ (-(q * j)) := by gcongr
      _ ≤ (|C| * U ^ delta) * (2 : ℝ) ^ (-(q * j)) := by
        gcongr
        exact div_le_self (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hUpos.le _)) hden
      _ = g j := by
        dsimp [g, ratio, U]
        rw [mul_assoc, dyadic_rpow_identity]
        ring
  · let ratio : ℝ := (2 : ℝ) ^ (delta + epsilon - q)
    have hratio0 : 0 ≤ ratio := Real.rpow_nonneg (by norm_num) _
    have hratio1 : ratio < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
        dsimp [ratio, epsilon]
        linarith)
    let g : ℕ → ℝ := fun j => |C| * (2 : ℝ) ^ (delta + epsilon) * ratio ^ j
    have hg : Summable g := by
      exact (summable_geometric_of_lt_one hratio0 hratio1).mul_left
        (|C| * (2 : ℝ) ^ (delta + epsilon))
    apply summable_of_shell_majorant A q hqpos g hg
    have hbound := dyadic_tendsto_atTop.eventually hcount
    have hrealTop : Tendsto (fun j : ℕ => ((2 ^ (j + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp dyadic_tendsto_atTop
    have hsubpowerReal :=
      (isLittleO_log_rpow_rpow_atTop (-beta) hepsilon).bound zero_lt_one
    have hsubpower := hrealTop.eventually hsubpowerReal
    have hlogpositive : ∀ᶠ j : ℕ in atTop,
        0 < Real.log (((2 ^ (j + 1) : ℕ) : ℝ)) :=
      (Real.tendsto_log_atTop.comp hrealTop).eventually_gt_atTop 0
    filter_upwards [hbound, hsubpower, hlogpositive] with j hj hsub hlogpos
    let U : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
    have hUpos : 0 < U := by dsimp [U]; positivity
    have hlogposU : 0 < Real.log U := by simpa [U] using hlogpos
    have hlogbound : Real.log U ^ (-beta) ≤ U ^ epsilon := by
      change ‖Real.log U ^ (-beta)‖ ≤ 1 * ‖U ^ epsilon‖ at hsub
      simpa only [Real.norm_eq_abs, one_mul,
        abs_of_nonneg (Real.rpow_nonneg hlogposU.le _),
        abs_of_nonneg (Real.rpow_nonneg hUpos.le _)] using hsub
    have hcountAbs : (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) ≤
        |C| * U ^ delta * Real.log U ^ (-beta) := by
      calc
        (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) ≤
            C * U ^ delta / Real.log U ^ beta := by simpa [U] using hj
        _ ≤ |C| * U ^ delta / Real.log U ^ beta := by
          gcongr
          exact le_abs_self C
        _ = |C| * U ^ delta * Real.log U ^ (-beta) := by
          rw [Real.rpow_neg hlogposU.le]
          ring
    calc
      (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) * (2 : ℝ) ^ (-(q * j)) ≤
          (|C| * U ^ delta * Real.log U ^ (-beta)) *
            (2 : ℝ) ^ (-(q * j)) := by gcongr
      _ ≤ (|C| * U ^ delta * U ^ epsilon) *
            (2 : ℝ) ^ (-(q * j)) := by gcongr
      _ = g j := by
        have hcombine : |C| * U ^ delta * U ^ epsilon =
            |C| * U ^ (delta + epsilon) := by
          rw [Real.rpow_add hUpos]
          ring
        rw [hcombine]
        dsimp [g, ratio, U]
        rw [mul_assoc, dyadic_rpow_identity]
        ring

private lemma log_dyadic (j : ℕ) :
    Real.log (((2 ^ (j + 1) : ℕ) : ℝ)) =
      ((j : ℝ) + 1) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  push_cast
  rfl

private lemma endpoint_case
    (A : Set ℕ) (C delta beta : ℝ)
    (hcount : ∀ᶠ n : ℕ in atTop,
      (carrierCountingFunction A n : ℝ) ≤
        C * (n : ℝ) ^ delta / Real.log n ^ beta)
    (hdelta : 0 < delta) (hbeta : 1 < beta) :
    Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-delta)) := by
  let K : ℝ := |C| * (2 : ℝ) ^ delta / Real.log 2 ^ beta
  let g : ℕ → ℝ := fun j => K * (((j : ℝ) + 1) ^ (-beta))
  have hbase : Summable (fun j : ℕ => (j : ℝ) ^ (-beta)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ (-beta))) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ (-beta)) 1).2 hbase
  have hg : Summable g := hshift.mul_left K
  apply summable_of_shell_majorant A delta hdelta g hg
  have hbound := dyadic_tendsto_atTop.eventually hcount
  filter_upwards [hbound] with j hj
  let U : ℝ := ((2 ^ (j + 1) : ℕ) : ℝ)
  have hcountAbs : (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) ≤
      |C| * U ^ delta / Real.log U ^ beta := by
    exact hj.trans (by
      dsimp [U]
      gcongr
      exact le_abs_self C)
  calc
    (carrierCountingFunction A (2 ^ (j + 1)) : ℝ) * (2 : ℝ) ^ (-(delta * j)) ≤
        (|C| * U ^ delta / Real.log U ^ beta) *
          (2 : ℝ) ^ (-(delta * j)) := by gcongr
    _ = g j := by
      have hnumerator : U ^ delta * (2 : ℝ) ^ (-(delta * j)) =
          (2 : ℝ) ^ delta := by
        dsimp [U]
        simpa using dyadic_rpow_identity delta delta j
      have hjpos : 0 < (j : ℝ) + 1 := by positivity
      have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hdenominator : Real.log U ^ beta =
          (((j : ℝ) + 1) ^ beta) * (Real.log 2 ^ beta) := by
        dsimp [U]
        rw [log_dyadic, Real.mul_rpow hjpos.le hlogtwo.le]
      dsimp [g, K]
      rw [hdenominator, Real.rpow_neg hjpos.le, ← hnumerator]
      field_simp

/-- If the counting function of `A` is eventually at most
`C * n^delta / (log n)^beta`, then the power series on `A` converges both strictly above
`delta` and at `delta` when `beta > 1`. -/
theorem carrier_decay_threshold
    (A : Set ℕ) (C delta beta q : ℝ)
    (hcount : ∀ᶠ n : ℕ in atTop,
      (carrierCountingFunction A n : ℝ) ≤
        C * (n : ℝ) ^ delta / Real.log n ^ beta) :
    (delta < q →
      Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-q))) ∧
    (q = delta → 1 < beta →
      Summable (A.indicator fun n : ℕ => (n : ℝ) ^ (-q))) := by
  constructor
  · intro hq
    by_cases hdelta : 0 ≤ delta
    · exact strict_case A C delta beta q hcount hdelta hq
    · have hdeltaNeg : delta < 0 := lt_of_not_ge hdelta
      have hfinite := finite_of_eventually_count_le_of_majorant_tendsto_zero
        A (fun n : ℕ => C * (n : ℝ) ^ delta / Real.log n ^ beta)
        hcount (tendsto_count_majorant_zero_of_delta_neg C delta beta hdeltaNeg)
      exact summable_on_finite_set A hfinite q
  · intro hq hbeta
    subst q
    by_cases hdelta : 0 < delta
    · exact endpoint_case A C delta beta hcount hdelta hbeta
    · have hdeltaNonpos : delta ≤ 0 := le_of_not_gt hdelta
      by_cases hdeltaZero : delta = 0
      · have hfinite := finite_of_eventually_count_le_of_majorant_tendsto_zero
          A (fun n : ℕ => C * (n : ℝ) ^ delta / Real.log n ^ beta)
          hcount (tendsto_count_majorant_zero_of_delta_zero C delta beta hdeltaZero (by linarith))
        exact summable_on_finite_set A hfinite delta
      · have hdeltaNeg : delta < 0 := lt_of_le_of_ne hdeltaNonpos hdeltaZero
        have hfinite := finite_of_eventually_count_le_of_majorant_tendsto_zero
          A (fun n : ℕ => C * (n : ℝ) ^ delta / Real.log n ^ beta)
          hcount (tendsto_count_majorant_zero_of_delta_neg C delta beta hdeltaNeg)
        exact summable_on_finite_set A hfinite delta

#print axioms carrier_decay_threshold

end D5.S3.Analytic.Boundary.CarrierDecayThreshold
