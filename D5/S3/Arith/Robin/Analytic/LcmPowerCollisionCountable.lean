/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Countability and nullity of collisions between distinct prime LCM power thresholds. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Analytic zero sets and distinct geometric decay rates of prime thresholds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen

namespace D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable

private lemma log_pow_limit {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => Real.log (1 - r ^ n) / r ^ n) atTop (𝓝 (-1)) := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hr).mpr hr1)
  have h := (Real.tendsto_mul_log_one_add_div_atTop (-1)).comp hp
  simp only [Function.comp_def, inv_pow, div_inv_eq_mul, neg_one_mul,
    ← sub_eq_add_neg] at h
  simpa only [div_eq_inv_mul] using h

private lemma log_pow_scaled_limit {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hsr : s < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => Real.log (1 - s ^ n) / r ^ n) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [zero_pow (by omega : n ≠ 0)]
  · have h := (log_pow_limit hs (hsr.trans hr1)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hs.le hr.le)
        ((div_lt_one hr).mpr hsr))
    simp only [mul_zero] at h
    exact h.congr (fun n => by rw [div_pow]; field_simp)

private lemma analytic_const_rpow {c κ : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) :
    AnalyticAt ℝ (fun t : ℝ => c ^ t) κ := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · refine (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) κ).congr ?_
    filter_upwards [Ioi_mem_nhds hκ] with t ht
    simp [Real.zero_rpow (ne_of_gt ht)]
  · simpa only [Real.rpow_def_of_pos hc, Pi.mul_apply, id_eq] using!
      ((analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => Real.log c) κ).mul
        analyticAt_id).rexp'

private lemma analyticOnNhd_lcmPowerF {x : ℝ} (hx : 1 < x)
    {n : ℕ} (hn : 1 ≤ n) :
    AnalyticOnNhd ℝ (fun κ : ℝ => lcmPowerF κ x n) (Ioi 1) := by
  intro κ hκ
  have hκ0 : 0 < κ := lt_trans zero_lt_one hκ
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hz : 0 < x ^ n := pow_pos hx0 n
  have hxn : x ≤ x ^ n := by
    simpa only [pow_one] using (pow_le_pow_right₀ hx.le hn)
  have ha : x ^ ((n : ℝ) + 1) = x ^ n * x := by
    rw [Real.rpow_add_one hx0.ne', Real.rpow_natCast]
  have hc : x ^ n < x ^ n * x := by nlinarith
  have hn0 : 0 ≤ x ^ (n : ℝ) - 1 := by
    rw [Real.rpow_natCast]
    linarith
  have hd0 : 0 ≤ x ^ (n : ℝ) - x := by
    rw [Real.rpow_natCast]
    linarith
  have hn1 : 0 ≤ x ^ ((n : ℝ) + 1) - 1 := by rw [ha]; nlinarith
  have hd1 : 0 ≤ x ^ ((n : ℝ) + 1) - x := by rw [ha]; nlinarith
  have hnum : 0 < (x ^ ((n : ℝ) + 1) - 1) ^ κ -
      (x ^ (n : ℝ) - 1) ^ κ := by
    exact sub_pos.mpr (Real.rpow_lt_rpow hn0
      (by rw [ha, Real.rpow_natCast]; linarith) hκ0)
  have hden : 0 < (x ^ ((n : ℝ) + 1) - x) ^ κ -
      (x ^ (n : ℝ) - x) ^ κ := by
    exact sub_pos.mpr (Real.rpow_lt_rpow hd0
      (by rw [ha, Real.rpow_natCast]; linarith) hκ0)
  have an := (analytic_const_rpow hn1 hκ0).sub (analytic_const_rpow hn0 hκ0)
  have ad := (analytic_const_rpow hd1 hκ0).sub (analytic_const_rpow hd0 hκ0)
  exact (((an.div ad hden.ne').log (div_pos hnum hden)).div
    ((analyticAt_id : AnalyticAt ℝ (fun t : ℝ => t) κ).mul analyticAt_const)
    (mul_ne_zero hκ0.ne' (Real.log_pos hx).ne'))

private lemma analytic_collision_countable {f g : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Ioi 1)) (hg : AnalyticOnNhd ℝ g (Ioi 1))
    (hne : ¬ EqOn f g (Ioi 1)) :
    {κ : ℝ | 1 < κ ∧ f κ = g κ}.Countable := by
  have he := (hf.eqOn_or_eventually_ne_of_preconnected hg
    (convex_Ioi (1 : ℝ)).isPreconnected).resolve_left hne
  have hd : IsDiscrete ({κ : ℝ | f κ = g κ} ∩ Ioi 1) :=
    isDiscrete_of_codiscreteWithin (by
      change ∀ᶠ x in codiscreteWithin (Ioi 1), f x ≠ g x
      exact he)
  simpa only [inter_def, mem_ofPred_eq, mem_Ioi, and_comm] using
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd

private def topBase (x : ℝ) (n : ℕ) : ℝ := x ^ n * x - 1
private def bottomBase (x : ℝ) (n : ℕ) : ℝ := x ^ n * x - x
private def rate (x : ℝ) (n : ℕ) : ℝ := (x ^ n - 1) / topBase x n
private def lowerRate (x : ℝ) (n : ℕ) : ℝ := (x ^ n - x) / bottomBase x n
private def limitValue (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (topBase x n / bottomBase x n) / Real.log x

private lemma ratio_bounds {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ lowerRate x n ∧ lowerRate x n < rate x n ∧
      0 < rate x n ∧ rate x n < 1 ∧
      1 / (x + 1) ≤ rate x n ∧ rate x n < 1 / x := by
  have hx0 : 0 < x := by linarith
  have hy : x ≤ x ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hx.le hn
  have hy0 : 0 < x ^ n := pow_pos hx0 n
  have hy1 : 1 < x ^ n := hx.trans_le hy
  have hprod : x ^ n < x ^ n * x := lt_mul_of_one_lt_right hy0 hx
  have hprod' : x < x ^ n * x := lt_mul_of_one_lt_left hx0 hy1
  have hA : 0 < x ^ n * x - 1 := by linarith
  have hC : 0 < x ^ n * x - x := by linarith
  dsimp only [lowerRate, rate, topBase, bottomBase]
  refine ⟨div_nonneg (sub_nonneg.mpr hy) hC.le,
    (div_lt_div_iff₀ hC hA).mpr ?_,
    div_pos (by linarith) hA, (div_lt_one hA).mpr ?_,
    (div_le_div_iff₀ (by linarith : 0 < x + 1) hA).mpr ?_,
    (div_lt_div_iff₀ hA hx0).mpr ?_⟩
  · nlinarith [mul_pos hy0 (sq_pos_of_pos (sub_pos.mpr hx))]
  · nlinarith
  · nlinarith
  · nlinarith

private lemma natural_factorization {x : ℝ} (hx : 1 < x)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    lcmPowerF (m : ℝ) x n = limitValue x n +
      (Real.log (1 - rate x n ^ m) - Real.log (1 - lowerRate x n ^ m)) /
        ((m : ℝ) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hy : x ≤ x ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ hx.le hn
  have hy1 : 1 < x ^ n := hx.trans_le hy
  have hprod : x < x ^ n * x := lt_mul_of_one_lt_left hx0 hy1
  have hA : 0 < topBase x n := by dsimp [topBase]; linarith
  have hC : 0 < bottomBase x n := by dsimp [bottomBase]; linarith
  obtain ⟨hs0, hsr, hr0, hr1, _, _⟩ := ratio_bounds hx hn
  have hrm : 0 < 1 - rate x n ^ m :=
    sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by omega))
  have hsm : 0 < 1 - lowerRate x n ^ m :=
    sub_pos.mpr (pow_lt_one₀ hs0 (hsr.trans hr1) (by omega))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hpow : x ^ ((n : ℝ) + 1) = x ^ n * x := by
    rw [Real.rpow_add_one hx0.ne', Real.rpow_natCast]
  have hfac (a b : ℝ) (ha : a ≠ 0) :
      a ^ m - b ^ m = a ^ m * (1 - (b / a) ^ m) := by
    rw [div_pow]
    field_simp [pow_ne_zero m ha]
  have hquot :
      ((topBase x n) ^ m - (x ^ n - 1) ^ m) /
        ((bottomBase x n) ^ m - (x ^ n - x) ^ m) =
      (topBase x n / bottomBase x n) ^ m *
        ((1 - rate x n ^ m) / (1 - lowerRate x n ^ m)) := by
    dsimp only [rate, lowerRate]
    rw [hfac _ _ hA.ne', hfac _ _ hC.ne', mul_div_mul_comm, ← div_pow]
  simp only [lcmPowerF, hpow, Real.rpow_natCast]
  change Real.log (((topBase x n) ^ m - (x ^ n - 1) ^ m) /
      ((bottomBase x n) ^ m - (x ^ n - x) ^ m)) /
        ((m : ℝ) * Real.log x) = _
  rw [hquot, Real.log_mul (pow_ne_zero m (div_pos hA hC).ne')
    (div_pos hrm hsm).ne', Real.log_pow, Real.log_div hrm.ne' hsm.ne']
  dsimp only [limitValue]
  field_simp [hm0, hlx]

private def correction (x : ℝ) (n m : ℕ) : ℝ :=
  Real.log (1 - rate x n ^ m) - Real.log (1 - lowerRate x n ^ m)

private lemma correction_scaled_limit {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun m : ℕ => correction x n m / rate x n ^ m) atTop (𝓝 (-1)) := by
  obtain ⟨hs0, hsr, hr0, hr1, _, _⟩ := ratio_bounds hx hn
  simpa [correction, sub_div] using
    (log_pow_limit hr0 hr1).sub (log_pow_scaled_limit hr0 hs0 hsr hr1)

private lemma correction_limit {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (correction x n) atTop (𝓝 0) := by
  obtain ⟨_, _, hr0, hr1, _, _⟩ := ratio_bounds hx hn
  have h := (correction_scaled_limit hx hn).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  simp only [mul_zero] at h
  exact h.congr (fun m => div_mul_cancel₀ _ (pow_ne_zero m hr0.ne'))

private lemma F_nat_limit {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun m : ℕ => lcmPowerF (m : ℝ) x n) atTop (𝓝 (limitValue x n)) := by
  have h := (tendsto_const_nhds (x := limitValue x n)).add
    (((correction_limit hx hn).mul tendsto_inv_atTop_nhds_zero_nat).div_const (Real.log x))
  simp only [zero_mul, zero_div, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [natural_factorization hx hn hm]
  simp only [correction, div_eq_mul_inv, mul_inv_rev]
  ring

private lemma not_eqOn_of_lt {p q i j : ℕ} (hp : 1 < p) (hpq : p < q)
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ¬ EqOn (fun κ : ℝ => lcmPowerF κ p i) (fun κ : ℝ => lcmPowerF κ q j) (Ioi 1) := by
  intro he
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (hp.trans hpq)
  obtain ⟨_, _, hrp0, hrp1, hrpl, _⟩ := ratio_bounds hp1 hi
  obtain ⟨hsq0, hsq, hrq0, hrq1, _, hrqu⟩ := ratio_bounds hq1 hj
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast (Nat.succ_le_iff.mpr hpq)
  have hrqp : rate q j < rate p i :=
    (hrqu.trans_le (one_div_le_one_div_of_le (by positivity) hpq')).trans_le hrpl
  have hef : (fun m : ℕ => lcmPowerF (m : ℝ) p i) =ᶠ[atTop]
      (fun m : ℕ => lcmPowerF (m : ℝ) q j) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
    exact he (by change (1 : ℝ) < (m : ℝ); exact_mod_cast (show 1 < m by omega))
  have hL : limitValue p i = limitValue q j :=
    tendsto_nhds_unique (F_nat_limit hp1 hi) ((F_nat_limit hq1 hj).congr' hef.symm)
  have hc : (fun m : ℕ => correction p i m / Real.log p / rate p i ^ m) =ᶠ[atTop]
      (fun m : ℕ => correction q j m / Real.log q / rate p i ^ m) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
    have hm1 : 1 ≤ m := by omega
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have he' := he (x := (m : ℝ))
      (by change (1 : ℝ) < (m : ℝ); exact_mod_cast (show 1 < m by omega))
    change lcmPowerF (m : ℝ) p i = lcmPowerF (m : ℝ) q j at he'
    rw [natural_factorization hp1 hi hm1, natural_factorization hq1 hj hm1, hL] at he'
    change limitValue q j + correction p i m / ((m : ℝ) * Real.log p) =
      limitValue q j + correction q j m / ((m : ℝ) * Real.log q) at he'
    have he'' := add_left_cancel he'
    congr 1
    field_simp [hm0, (Real.log_pos hp1).ne', (Real.log_pos hq1).ne'] at he'' ⊢
    nlinarith only [he'']
  have hleft : Tendsto (fun m : ℕ => correction p i m / Real.log p / rate p i ^ m)
      atTop (𝓝 (-1 / Real.log p)) := by
    simpa only [div_right_comm] using (correction_scaled_limit hp1 hi).div_const (Real.log p)
  have hright : Tendsto (fun m : ℕ => correction q j m / Real.log q / rate p i ^ m)
      atTop (𝓝 0) := by
    have h := ((log_pow_scaled_limit hrp0 hrq0.le hrqp hrp1).sub
      (log_pow_scaled_limit hrp0 hsq0 (hsq.trans hrqp) hrp1)).div_const (Real.log q)
    simpa [correction, sub_div, div_right_comm] using h
  have hz : -1 / Real.log (p : ℝ) = 0 := tendsto_nhds_unique hleft (hright.congr' hc.symm)
  exact (div_ne_zero (by norm_num) (Real.log_pos hp1).ne') hz

/-- Collision parameters for two distinct primes form a countable Lebesgue null set. -/
theorem collision_parameters_countable_null {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    {κ : ℝ | 1 < κ ∧ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j}.Countable ∧
    volume {κ : ℝ | 1 < κ ∧ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j} = 0 := by
  have hz (i j : {n : ℕ // 1 ≤ n}) :
      {κ : ℝ | 1 < κ ∧ lcmPowerF κ p i = lcmPowerF κ q j}.Countable := by
    apply analytic_collision_countable
      (analyticOnNhd_lcmPowerF (by exact_mod_cast hp.one_lt) i.property)
      (analyticOnNhd_lcmPowerF (by exact_mod_cast hq.one_lt) j.property)
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact not_eqOn_of_lt hp.one_lt hlt i.property j.property
    · intro he
      exact not_eqOn_of_lt hq.one_lt hgt j.property i.property he.symm
  have hu := Set.countable_iUnion (fun i => Set.countable_iUnion (hz i))
  have hc : {κ : ℝ | 1 < κ ∧ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j}.Countable := by
    apply hu.mono
    rintro κ ⟨hκ, i, j, hi, hj, he⟩
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, mem_iUnion.mpr ⟨⟨j, hj⟩, hκ, he⟩⟩
  exact ⟨hc, hc.measure_zero volume⟩

/-- All prime collisions are countable and null; almost every parameter separates all primes. -/
theorem all_collision_parameters_countable_null :
    {κ : ℝ | 1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j}.Countable ∧
    volume {κ : ℝ | 1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j} = 0 ∧
    (∀ᵐ κ : ℝ ∂volume, 1 < κ → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Disjoint ((fun i : ℕ => lcmPowerF κ p i) '' {i : ℕ | 1 ≤ i})
        ((fun j : ℕ => lcmPowerF κ q j) '' {j : ℕ | 1 ≤ j})) := by
  let S (p q : ℕ) : Set ℝ := {κ | 1 < κ ∧ ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧
    lcmPowerF κ p i = lcmPowerF κ q j}
  have hc (p q : {p : ℕ // p.Prime}) :
      (if p.val = q.val then (∅ : Set ℝ) else S p q).Countable := by
    split_ifs with h
    · exact countable_empty
    · exact (collision_parameters_countable_null p.property q.property h).1
  have hu := Set.countable_iUnion (fun p => Set.countable_iUnion (hc p))
  have hcount : {κ : ℝ | 1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j}.Countable := by
    apply hu.mono
    rintro κ ⟨hκ, p, q, i, j, hp, hq, hpq, hi, hj, he⟩
    apply mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩⟩
    simpa only [ite_eq_right hpq] using (show κ ∈ S p q from ⟨hκ, i, j, hi, hj, he⟩)
  have hnull := hcount.measure_zero volume
  refine ⟨hcount, hnull, ?_⟩
  have hae : ∀ᵐ κ : ℝ ∂volume, ¬ (1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with κ hκ hk p q hp hq hpq
  apply Set.disjoint_left.mpr
  rintro z ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
  exact hκ ⟨hk, p, q, i, j, hp, hq, hpq, hi, hj, he.symm⟩

end D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
