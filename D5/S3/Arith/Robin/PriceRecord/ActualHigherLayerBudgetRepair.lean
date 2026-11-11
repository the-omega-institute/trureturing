/- GID: D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Fixed-layer finite integer repair and arbitrary-positive-price original-record comparison. -/
import D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. Source-only proof candidate. The two small exposure
patches are unapplied integration inputs. The Budget and prefix owners are reused,
not copied. No higher-mass coercivity, energy consequence, native acceptance,
source binding, literature novelty or consensus is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.PrimeValuation5040Bridge (primeBlock_factorization)
open D5.S3.Factorization.PrimePowers.FiniteCrtJoin (primePowerProduct)

private theorem log_scale_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => log t / log (c * t)) atTop (𝓝 1) := by
  have hz : Tendsto (fun t : ℝ => log c / log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hi := (tendsto_const_nhds.add hz).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simp only [add_zero, inv_one] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_id.const_mul_atTop hc).eventually_gt_atTop 1] with t ht hct
  change (1 + log c / log t)⁻¹ = log t / log (c * t)
  have he : 1 + log c / log t = (log c + log t) / log t := by
    field_simp [(log_pos ht).ne'] <;> ring
  rw [he, inv_div, log_mul hc.ne' (by linarith : t ≠ 0)]

private theorem log_scale_over_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => log (c * t) / log t) atTop (𝓝 1) := by
  have hz : Tendsto (fun t : ℝ => log c / log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have h := hz.add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [log_mul hc.ne' (by linarith : t ≠ 0)]
  field_simp [(log_pos ht).ne']
  <;> ring

/- A finite maximal feasible subset. There is no divisibility, order or
positivity assumption on the weights in the maximality argument itself. -/
theorem finite_pack (S : Finset ℕ) (w : ℕ → ℝ) {d M : ℝ}
    (hd : 0 ≤ d) (hfull : d < ∑ p ∈ S, w p)
    (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ M) :
    ∃ A : Finset ℕ, A ⊆ S ∧ (∑ p ∈ A, w p) ≤ d ∧
      0 ≤ d - ∑ p ∈ A, w p ∧ d - ∑ p ∈ A, w p < M := by
  classical
  let F := S.powerset.filter (fun A => (∑ p ∈ A, w p) ≤ d)
  have hF : F.Nonempty := ⟨∅, by simp [F, hd]⟩
  obtain ⟨A, hA, hmax⟩ := F.exists_max_image card hF
  have hAS : A ⊆ S := mem_powerset.mp (mem_filter.mp hA).1
  have hAd : (∑ p ∈ A, w p) ≤ d := (mem_filter.mp hA).2
  have hne : S \ A ≠ ∅ := by
    intro he
    have hSA : S ⊆ A := sdiff_eq_empty_iff_subset.mp he
    have hEq : A = S := Subset.antisymm hAS hSA
    rw [hEq] at hAd
    exact hfull.not_ge hAd
  obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨hqS, hqA⟩ := mem_sdiff.mp hq
  have hnext : d < (∑ p ∈ A, w p) + w q := by
    by_contra! hn
    have hmem : insert q A ∈ F := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hqS hAS), ?_⟩
      simpa [sum_insert hqA, add_comm] using hn
    have hc := hmax (insert q A) hmem
    rw [card_insert_of_notMem hqA] at hc
    omega
  exact ⟨A, hAS, hAd, sub_nonneg.mpr hAd, by linarith [(hw q hqS).2]⟩

private theorem fixed_endpoints {J : ℕ} (hJ : 3 ≤ J) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) : ∃ a b : ℝ,
    0 < a ∧ a < b ∧ 1 - τ < (J : ℝ) / b ^ J ∧
      (J : ℝ) / b ^ J < (J : ℝ) / a ^ J ∧ (J : ℝ) / a ^ J < 1 := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let u : ℝ := (J : ℝ) / (1 - τ / 4)
  let v : ℝ := (J : ℝ) / (1 - τ / 2)
  have hu : 0 < u := div_pos hJ0 (by linarith)
  have hv : 0 < v := div_pos hJ0 (by linarith)
  have huv : u < v := by
    dsimp [u, v]
    exact div_lt_div_of_pos_left hJ0 (by linarith) (by linarith)
  let a := u ^ ((J : ℝ)⁻¹)
  let b := v ^ ((J : ℝ)⁻¹)
  have ha : 0 < a := rpow_pos_of_pos hu _
  have hab : a < b := rpow_lt_rpow hu.le huv (inv_pos.mpr hJ0)
  have hap : a ^ J = u := rpow_inv_natCast_pow hu.le (by omega)
  have hbp : b ^ J = v := rpow_inv_natCast_pow hv.le (by omega)
  have hqa : (J : ℝ) / a ^ J = 1 - τ / 4 := by
    rw [hap]; dsimp [u]
    field_simp [hJ0.ne', (show 1 - τ / 4 ≠ 0 by linarith)] <;> ring
  have hqb : (J : ℝ) / b ^ J = 1 - τ / 2 := by
    rw [hbp]; dsimp [v]
    field_simp [hJ0.ne', (show 1 - τ / 2 ≠ 0 by linarith)] <;> ring
  refine ⟨a, b, ha, hab, ?_, ?_, ?_⟩ <;> simp only [hqa, hqb] <;> linarith

/- All analytic choices precede the Budget. The PNT supplier has a fixed
cardinality and fixed multiplicative endpoints; J never varies with X. -/
set_option maxHeartbeats 800000 in
private theorem candidate_roster {η τ : ℝ} (hη : 0 < η)
    (hτ : 0 < τ) (hτ1 : τ < 1) {J : ℕ} (hJ : 3 ≤ J)
    (hJη : 1 / (J : ℝ) < η / 2) : ∀ᶠ X : ℝ in atTop,
    ∃ S : Finset ℕ,
      log (2 * X) < ∑ p ∈ S, log p ∧
      ∀ p ∈ S, p.Prime ∧ (p : ℝ) < X / 2 ∧
        log p ≤ (η / 2) * log X ∧
        (1 - τ) * referencePrice X ≤ goldenLayerMarginal p J ∧
        goldenLayerMarginal p J < referencePrice X ∧
        referencePrice X < goldenLayerMarginal p (J - 1) := by
  classical
  obtain ⟨a, b, ha, hab, hLgap, hLU, hUgap⟩ := fixed_endpoints hJ hτ hτ1
  have hb : 0 < b := ha.trans hab
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let U := fun t : ℝ => ((J : ℝ) / a ^ J) * (log t / log (a * t))
  let L := fun t : ℝ => (1 - (a * t)⁻¹) * ((J : ℝ) / b ^ J) *
    (log t / log (b * t))
  have hU : Tendsto U atTop (𝓝 ((J : ℝ) / a ^ J)) := by
    simpa [U] using (log_scale_ratio ha).const_mul ((J : ℝ) / a ^ J)
  have hinv : Tendsto (fun t : ℝ => (a * t)⁻¹) atTop (𝓝 0) :=
    (tendsto_id.const_mul_atTop ha).inv_tendsto_atTop
  have hL : Tendsto L atTop (𝓝 ((J : ℝ) / b ^ J)) := by
    simpa [L] using ((((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).mul_const
      ((J : ℝ) / b ^ J)).mul (log_scale_ratio hb))
  have hlogupper : Tendsto (fun t : ℝ => log (b * t) / log (t ^ J))
      atTop (𝓝 (1 / (J : ℝ))) := by
    have hh := (log_scale_over_log hb).div_const (J : ℝ)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [log_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hlogfull : Tendsto
      (fun t : ℝ => ((J + 2 : ℕ) : ℝ) * log (a * t) / log t -
        log (2 * t ^ J) / log t) atTop (𝓝 2) := by
    have hc : Tendsto (fun t : ℝ => log 2 / log t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_log_atTop
    have hh := ((log_scale_over_log ha).const_mul ((J + 2 : ℕ) : ℝ)).sub
      (hc.add_const (J : ℝ))
    have hlim : ((J + 2 : ℕ) : ℝ) * 1 - (0 + (J : ℝ)) = 2 := by
      push_cast; ring
    rw [hlim] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos (by linarith : 0 < t) J).ne', log_pow]
    field_simp [(log_pos ht).ne']
    <;> ring
  have hsize : Tendsto (fun t : ℝ => b * t / t ^ J) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => b / t ^ (J - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : J - 1 ≠ 0))
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hp : t ^ J = t ^ (J - 1) * t := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ J)] using pow_succ t (J - 1)
    rw [hp]
    field_simp [ht.ne'] <;> ring
  obtain ⟨Y, hY⟩ := fixed_cardinality_prime_window ha hab (J + 2)
  have hgood : ∀ᶠ t : ℝ in atTop,
      ∃ S : Finset ℕ, log (2 * t ^ J) < ∑ p ∈ S, log p ∧
      ∀ p ∈ S, p.Prime ∧ (p : ℝ) < t ^ J / 2 ∧
        log p ≤ (η / 2) * log (t ^ J) ∧
        (1 - τ) * referencePrice (t ^ J) ≤ goldenLayerMarginal p J ∧
        goldenLayerMarginal p J < referencePrice (t ^ J) ∧
        referencePrice (t ^ J) < goldenLayerMarginal p (J - 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop Y,
      (tendsto_id.const_mul_atTop ha).eventually_gt_atTop 1,
      (tendsto_id.const_mul_atTop hb).eventually_gt_atTop (1 / (1 - τ)),
      hU.eventually (eventually_lt_nhds hUgap),
      hL.eventually (eventually_gt_nhds hLgap),
      hlogupper.eventually (eventually_lt_nhds hJη),
      hlogfull.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2)),
      hsize.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with t ht htY hat hbt hUt hLt hlogt hfullt hsizet
    change 1 < a * t at hat
    change 1 / (1 - τ) < b * t at hbt
    obtain ⟨S, hcard, hS⟩ := hY t htY
    have ht0 : 0 < t := by linarith
    have hX1 : 1 < t ^ J := one_lt_pow₀ ht (by omega)
    have hLambda : 0 < referencePrice (t ^ J) := reference_price_pos hX1
    have halog : 0 < log (a * t) := log_pos hat
    have hblog : 0 < log (b * t) := log_pos (hat.trans (mul_lt_mul_of_pos_right hab ht0))
    have hlogX : 0 < log (t ^ J) := log_pos hX1
    have hbase : (1 - (a * t)⁻¹) * (b * t)⁻¹ ^ J =
        referencePrice (t ^ J) * log (b * t) * L t := by
      dsimp [L, referencePrice]
      rw [log_pow]
      simp only [mul_inv_rev, mul_pow, inv_pow]
      have htb_log : 0 < log (t * b) := by simpa [mul_comm] using hblog
      field_simp [ht0.ne', ha.ne', hb.ne', (log_pos ht).ne', hJ0.ne', hblog.ne', htb_log.ne']
      <;> ring
    have hupper : (a * t)⁻¹ ^ J =
        referencePrice (t ^ J) * log (a * t) * U t := by
      dsimp [U, referencePrice]
      rw [log_pow]
      simp only [mul_inv_rev, mul_pow, inv_pow]
      field_simp [ht0.ne', ha.ne', (log_pos ht).ne', hJ0.ne', halog.ne']
      <;> ring
    have hprevious : (1 - (a * t)⁻¹) * (b * t)⁻¹ ^ (J - 1) =
        (b * t) * (referencePrice (t ^ J) * log (b * t) * L t) := by
      rw [← hbase]
      have hp : (b * t)⁻¹ ^ J = (b * t)⁻¹ ^ (J - 1) * (b * t)⁻¹ := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ J)] using
          pow_succ ((b * t)⁻¹) (J - 1)
      rw [hp]
      field_simp [(mul_pos hb ht0).ne'] <;> ring
    refine ⟨S, ?_, ?_⟩
    · have hmin : ((J + 2 : ℕ) : ℝ) * log (a * t) ≤ ∑ p ∈ S, log p := by
        calc
          _ = ∑ _p ∈ S, log (a * t) := by simp [hcard]
          _ ≤ _ := sum_le_sum (fun p hp => log_le_log (by linarith)
            (hS p hp).2.1.le)
      have hfull : log (2 * t ^ J) < ((J + 2 : ℕ) : ℝ) * log (a * t) := by
        have hh := (sub_pos.mp hfullt)
        exact (div_lt_div_iff_of_pos_right (log_pos ht)).mp hh
      exact hfull.trans_le hmin
    · intro p hp
      obtain ⟨hpp, hap, hpb⟩ := hS p hp
      have hlp : 0 < log (p : ℝ) := hpp.log_pos
      have haplog : log (a * t) ≤ log (p : ℝ) := log_le_log (by linarith) hap.le
      have hpblog : log (p : ℝ) ≤ log (b * t) := log_le_log
        (by exact_mod_cast hpp.pos) hpb
      have hlow := gain_lower_window (fun q i hq hi => golden_layer_gain_lower hq hi)
        hpp (by omega : 1 ≤ J) le_rfl hat hap.le hpb
      have hup := gain_upper_window hpp (by omega : 1 ≤ J) le_rfl
        (show 0 < a * t by linarith) hap.le
      have hprev := gain_lower_window (fun q i hq hi => golden_layer_gain_lower hq hi)
        hpp (by omega : 1 ≤ J - 1) le_rfl hat hap.le hpb
      change _ ≤ goldenLayerMarginal p J * log p at hlow
      change goldenLayerMarginal p J * log p ≤ _ at hup
      change _ ≤ goldenLayerMarginal p (J - 1) * log p at hprev
      rw [hbase] at hlow
      rw [hupper] at hup
      rw [hprevious] at hprev
      have hJL : 0 < L t := (by linarith : 0 < 1 - τ).trans hLt
      have hprev1 : 1 < b * t * L t := by
        have hh := mul_lt_mul_of_pos_left hLt (mul_pos hb ht0)
        have hb1 := (div_lt_iff₀ (by linarith : 0 < 1 - τ)).mp hbt
        nlinarith
      refine ⟨hpp, ?_, ?_, ?_, ?_, ?_⟩
      · have hh := (div_lt_iff₀ (pow_pos ht0 J)).mp hsizet
        exact hpb.trans_lt (by linarith)
      · exact hpblog.trans ((div_lt_iff₀ hlogX).mp hlogt).le
      · apply (le_of_mul_le_mul_right ?_ hlp)
        have hm := mul_le_mul_of_nonneg_left hpblog
          (mul_nonneg (by linarith : 0 ≤ 1 - τ) hLambda.le)
        have hh := mul_le_mul_of_nonneg_left hLt.le (mul_pos hLambda hblog).le
        nlinarith
      · apply (lt_of_mul_lt_mul_right ?_ hlp.le)
        have hh := mul_lt_mul_of_pos_left hUt (mul_pos hLambda halog)
        have hm := mul_le_mul_of_nonneg_left haplog hLambda.le
        nlinarith
      · apply (lt_of_mul_lt_mul_right ?_ hlp.le)
        have hh := mul_lt_mul_of_pos_left hprev1 (mul_pos hLambda hblog)
        have hm := mul_le_mul_of_nonneg_left hpblog hLambda.le
        nlinarith
  have hT : Tendsto (fun X : ℝ => X ^ ((J : ℝ)⁻¹)) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hJ0)
  filter_upwards [hT.eventually hgood, eventually_gt_atTop (0 : ℝ)] with X hX hx
  simpa only [rpow_inv_natCast_pow hx.le (by omega : J ≠ 0)] using hX

theorem residual_nonneg {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ actualDefect X n - completeFirstLayerLoss X n := by
  have h := actual_defect_decomposition hX hn
  have h2 : 0 ≤ completeSecondLayerLoss X n :=
    sum_nonneg (fun p _ => layer_loss_nonneg X n p 2)
  have h3 : 0 ≤ completeHigherLayerLoss X n :=
    sum_nonneg (fun p _ => sum_nonneg (fun j _ => layer_loss_nonneg X n p j))
  linarith

/- The complete objective factorization, not a truncated inventory, supplies
this exact telescoping identity. A prime is inserted at most once. -/
/-- General finite insertion at an arbitrary complete prime prefix. The
initial higher loss is retained; this permits disjoint insertions at any layers.
This is the consumed generalization of the former Budget-only private helper. -/
theorem insert_roster_at_prefix {X : ℝ} (hX : 4 < X) {base Q : ℕ}
    (hb2 : 2 ≤ base) (hpref : base.primeFactors = Nat.primesLE Q)
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) {r : ℝ}
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    {J : ℕ} (hJ : 1 ≤ J) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p ≤ Q ∧ base.factorization p = J - 1) :
    let k := base * ∏ p ∈ A, p
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
      log (k : ℝ) - log (base : ℝ) = ∑ p ∈ A, log p ∧
      (∀ p, k.factorization p = base.factorization p + if p ∈ A then 1 else 0) ∧
      actualDefect X k - completeFirstLayerLoss X k =
        (actualDefect X base - completeFirstLayerLoss X base) +
          ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p := by
  classical
  let u := ∏ p ∈ A, p
  let k := base * u
  have hu : 0 < u := prod_pos (fun p hp => (hA p hp).1.pos)
  have hk : 0 < k := Nat.mul_pos (by omega) hu
  have huf (p : ℕ) : u.factorization p = if p ∈ A then 1 else 0 := by
    simpa [u, primePowerProduct] using
      (primeBlock_factorization (fun p hp => (hA p hp).1) (fun _ => 1) p)
  have hkf (p : ℕ) : k.factorization p = base.factorization p + if p ∈ A then 1 else 0 := by
    rw [show k = base * u from rfl, Nat.factorization_mul (by omega) hu.ne',
      Finsupp.add_apply, huf]
  have hAsub : A ⊆ base.primeFactors := by
    intro p hp; rw [hpref]
    exact Nat.mem_primesLE.mpr ⟨(hA p hp).2.1, (hA p hp).1⟩
  have hkprefix : k.primeFactors = Nat.primesLE Q := by
    rw [show k = base * u from rfl, Nat.primeFactors_mul (by omega) hu.ne']
    have hup : u.primeFactors = A := Nat.primeFactors_prod (fun p hp => (hA p hp).1)
    rw [hup, union_eq_left.mpr hAsub, hpref]
  have hk2 : 2 ≤ k := hb2.trans (Nat.le_mul_of_pos_right base hu)
  have hlogu : log (u : ℝ) = ∑ p ∈ A, log p := by
    rw [show (u : ℝ) = ∏ p ∈ A, (p : ℝ) by simp [u],
      log_prod (fun p hp => by exact_mod_cast (hA p hp).1.ne_zero)]
  have hlogk : log (k : ℝ) - log (base : ℝ) = ∑ p ∈ A, log p := by
    rw [show (k : ℝ) = (base : ℝ) * u by simp [k],
      log_mul (by exact_mod_cast (show base ≠ 0 by omega))
        (by exact_mod_cast hu.ne'), hlogu]
    ring
  have hfirst : completeFirstLayerLoss X k = completeFirstLayerLoss X base := by
    have hc := complete_first_layer_prefix_cancellation hX hpref hkprefix
      hQ hQ hr hroot
    simp only [sub_self, abs_zero, mul_zero, zero_div] at hc
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hc)
  have hobj : goldenResourceObjective (referencePrice X) k -
      goldenResourceObjective (referencePrice X) base =
      ∑ p ∈ A, (goldenLayerMarginal p J - referencePrice X) * log p := by
    rw [golden_resource_objective_sum_on _ (by omega : 1 ≤ k)
        base.primeFactors (by rw [hkprefix, hpref]),
      golden_resource_objective_sum_on _ (by omega : 1 ≤ base)
        base.primeFactors Subset.rfl, ← sum_sub_distrib]
    calc
      _ = ∑ p ∈ A, (goldenPrimeLocalObjective (referencePrice X) p (k.factorization p) -
          goldenPrimeLocalObjective (referencePrice X) p (base.factorization p)) := by
        symm
        apply sum_subset hAsub
        intro p hp hn
        rw [hkf, if_neg hn, add_zero, sub_self]
      _ = _ := by
        apply sum_congr rfl
        intro p hp
        rw [hkf, if_pos hp, golden_prime_local_objective_diff (hA p hp).1,
          (hA p hp).2.2, Nat.sub_add_cancel (by omega : 1 ≤ J)]
  refine ⟨hk2, hkprefix, hlogk, hkf, ?_⟩
  rw [hfirst]
  unfold actualDefect
  rw [show (∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p) =
    -(∑ p ∈ A, (goldenLayerMarginal p J - referencePrice X) * log p) by
      rw [← sum_neg_distrib]; apply sum_congr rfl; intro p hp; ring]
  linarith

theorem insert_roster {X : ℝ} (hX : 4 < X) {b : Budget} (hb : b.spec X)
    {J : ℕ} (hJ : 3 ≤ J) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧ b.k.factorization p = J - 1) :
    let k := b.k * ∏ p ∈ A, p
    2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧
      log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧
      (∀ p, k.factorization p = b.k.factorization p + if p ∈ A then 1 else 0) ∧
      actualDefect X k - completeFirstLayerLoss X k =
        ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p := by
  rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  obtain ⟨hk, hp, hl, hf, hc⟩ := insert_roster_at_prefix hX hb2 hpref hQ hr hroot
    (by omega : 1 ≤ J) A hA
  have hz := defect_eq_first_of_optimizer_higher_layers (by linarith : 1 < X)
    (by omega : 1 ≤ b.k) hhigher
  refine ⟨hk, hp, hl, hf, ?_⟩
  simpa only [hz, sub_self, zero_add] using hc

/-- A fixed higher layer repairs every admissible real-clock budget. The final
existential records the literal full telescope: actual integer, complete loss,
unchanged prime prefix, increment at each prime and exact finite loss sum. -/
theorem actual_higher_layer_budget_repair :
    ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, 1 < X0 ∧
    ∀ X : ℝ, X0 ≤ X → ∀ b : Budget, b.spec X →
    ∃ k : ℕ, 2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧
      0 ≤ X - log (k : ℝ) ∧
      0 ≤ log (k : ℝ) - log (b.k : ℝ) ∧
      log (k : ℝ) - log (b.k : ℝ) ≤ b.δ ∧
      0 ≤ actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ∧
      actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ≤ η / X ∧
      ∃ J : ℕ, ∃ A : Finset ℕ, 3 ≤ J ∧
        (∀ p ∈ A, p.Prime ∧ p ≤ b.Q ∧
          b.k.factorization p = J - 1 ∧
          optimalLayerCount (referencePrice X) p = J - 1) ∧
        k = b.k * ∏ p ∈ A, p ∧
        log (k : ℝ) - log (b.k : ℝ) = ∑ p ∈ A, log p ∧
        (∀ p : ℕ, k.factorization p =
          b.k.factorization p + if p ∈ A then 1 else 0) ∧
        actualDefect X k - completeFirstLayerLoss X k =
          ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p := by
  intro η hη
  classical
  obtain ⟨J, hJbig⟩ := exists_nat_gt (max (3 : ℝ) (4 / η))
  have hJ : 3 ≤ J := by
    have hh := (le_max_left (3 : ℝ) (4 / η)).trans_lt hJbig
    exact_mod_cast hh.le
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJη : 1 / (J : ℝ) < η / 2 := by
    have hh := (div_lt_iff₀ hη).mp ((le_max_right (3 : ℝ) (4 / η)).trans_lt hJbig)
    apply (div_lt_iff₀ hJ0).mpr
    nlinarith
  let τ := min (η / 8) (1 / 2)
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτ1 : τ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hτη : 2 * τ ≤ η / 2 := by
    have hh := min_le_left (η / 8) (1 / 2 : ℝ)
    change τ ≤ η / 8 at hh
    linarith
  obtain ⟨B, hB⟩ := eventually_atTop.mp (candidate_roster hη hτ hτ1 hJ hJη)
  refine ⟨max B 14, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX b hb
  have hX14 : 14 ≤ X := (le_max_right B 14).trans hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have hLambda : 0 < referencePrice X := reference_price_pos (by linarith)
  obtain ⟨S, hfull, hS⟩ := hB X ((le_max_left B 14).trans hX)
  rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  have hb' : b.spec X := ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0,
    hdlog, hds, hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  obtain ⟨A, hAS, hAd, hremain0, hremain⟩ := finite_pack S (fun p => log p)
    hd0 (hdlog.trans hfull) (fun p hp => ⟨(hS p hp).1.log_pos.le, (hS p hp).2.2.1⟩)
  have hexp (p : ℕ) (hp : p ∈ S) :
      b.k.factorization p = J - 1 ∧ optimalLayerCount (referencePrice X) p = J - 1 := by
    obtain ⟨hpp, hpX, hplog, hlow, hupp, hprev⟩ := hS p hp
    have hlo : J - 1 ≤ optimalLayerCount (referencePrice X) p := by
      rw [← strictInteger_counts hLambda]
      exact (strict_layer_iff hLambda hpp (by omega : 1 ≤ J - 1)).mpr hprev
    have hhi : ¬ J ≤ optimalLayerCount (referencePrice X) p := by
      rw [← strictInteger_counts hLambda]
      exact fun hj => hupp.not_ge ((strict_layer_iff hLambda hpp (by omega)).mp hj).le
    have hc : optimalLayerCount (referencePrice X) p = J - 1 := by omega
    have hblo := (hhigher p hpp (J - 1) (by omega)).mpr hlo
    have hbhi : ¬ J ≤ b.k.factorization p := fun hj => hhi ((hhigher p hpp J (by omega)).mp hj)
    exact ⟨by omega, hc⟩
  have hA (p : ℕ) (hp : p ∈ A) :
      p.Prime ∧ p ≤ b.Q ∧ b.k.factorization p = J - 1 := by
    have hpS := hAS hp
    refine ⟨(hS p hpS).1, ?_, (hexp p hpS).1⟩
    exact_mod_cast ((hS p hpS).2.1.le.trans hQ.1)
  let k := b.k * ∏ p ∈ A, p
  obtain ⟨hk2, hkprefix, hlogk, hkf, hcost⟩ := insert_roster (by linarith) hb' hJ A hA
  change 2 ≤ k at hk2
  change k.primeFactors = Nat.primesLE b.Q at hkprefix
  change log (k : ℝ) - log (b.k : ℝ) = _ at hlogk
  change actualDefect X k - completeFirstLayerLoss X k = _ at hcost
  have hmass0 : 0 ≤ ∑ p ∈ A, log p := sum_nonneg (fun p hp => (hA p hp).1.log_pos.le)
  have hslack : X - log (k : ℝ) = b.δ - ∑ p ∈ A, log p := by linarith
  have hR0 : 0 ≤ actualDefect X k - completeFirstLayerLoss X k := by
    rw [hcost]
    apply sum_nonneg
    intro p hp
    exact mul_nonneg (sub_nonneg.mpr (hS p (hAS hp)).2.2.2.2.1.le) (hA p hp).1.log_pos.le
  have hRupper : actualDefect X k - completeFirstLayerLoss X k ≤
      τ * referencePrice X * b.δ := by
    rw [hcost]
    calc
      _ ≤ ∑ p ∈ A, (τ * referencePrice X) * log p := by
        apply sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_right _ (hA p hp).1.log_pos.le
        have hh := (hS p (hAS hp)).2.2.2.1
        nlinarith
      _ = (τ * referencePrice X) * (∑ p ∈ A, log p) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hAd (mul_nonneg hτ.le hLambda.le)
  have hδbound : b.δ ≤ 2 * log X := hdlog.le.trans (log_shell (by linarith : 4 < X)).2.2
  have hRsmall : actualDefect X k - completeFirstLayerLoss X k ≤ η / (2 * X) := by
    calc
      _ ≤ τ * referencePrice X * b.δ := hRupper
      _ ≤ τ * referencePrice X * (2 * log X) :=
        mul_le_mul_of_nonneg_left hδbound (mul_nonneg hτ.le hLambda.le)
      _ = 2 * τ / X := by
        unfold referencePrice
        field_simp [hX0.ne', hlog.ne'] <;> ring
      _ ≤ η / (2 * X) := by
        apply (div_le_div_iff₀ hX0 (by positivity : 0 < 2 * X)).mpr
        nlinarith
  have hslackSmall : referencePrice X * (X - log (k : ℝ)) ≤ η / (2 * X) := by
    have hh : X - log (k : ℝ) ≤ (η / 2) * log X := by rw [hslack]; exact hremain.le
    calc
      _ ≤ referencePrice X * ((η / 2) * log X) := mul_le_mul_of_nonneg_left hh hLambda.le
      _ = _ := by
        unfold referencePrice
        field_simp [hX0.ne', hlog.ne'] <;> ring
  refine ⟨k, hk2, hkprefix, ?_, ?_, ?_, ?_, ?_, J, A, hJ, ?_, rfl,
    hlogk, hkf, hcost⟩
  · rw [hslack]; exact hremain0
  · rw [hlogk]; exact hmass0
  · rw [hlogk]; exact hAd
  · exact add_nonneg hR0 (mul_nonneg hLambda.le (by rw [hslack]; exact hremain0))
  · calc
      _ ≤ η / (2 * X) + η / (2 * X) := add_le_add hRsmall hslackSmall
      _ = η / X := by
        field_simp [hX0.ne']
        ring
  · intro p hp
    exact ⟨(hA p hp).1, (hA p hp).2.1, (hexp p (hAS hp)).1, (hexp p (hAS hp)).2⟩

/- Exact two-price comparison. In particular the positive repair loss is NOT
set to zero, and the price change uses X-log(k), never the old b.δ. -/
theorem two_price_compare {X μ : ℝ} {m k : ℕ}
    (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ)) (hslack : 0 ≤ X - log (k : ℝ)) :
    k ≤ m ∧ actualDefect X m - actualDefect X k ≤
      (referencePrice X - μ) * (X - log (k : ℝ)) := by
  have hkm : k ≤ m := by
    by_contra! hbad
    have hl := log_lt_log (show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega))
      (show (m : ℝ) < k by exact_mod_cast hbad)
    linarith
  have hobj : goldenResourceObjective μ k ≤ goldenResourceObjective μ m := by
    rcases lt_or_eq_of_le hkm with hlt | heq
    · exact (hrecord k (by omega) hlt).le
    · subst k; exact le_rfl
  refine ⟨hkm, ?_⟩
  unfold actualDefect goldenResourceObjective
  unfold goldenResourceObjective at hobj
  rw [hclock]
  nlinarith

private theorem repaired_comparison {η X μ : ℝ} (hη : 0 < η)
    (hX : 14 ≤ X) {m : ℕ} (hm : 2 ≤ m) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ))
    (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (b : Budget) (hb : b.spec X)
    (hrepair : ∃ k : ℕ, 2 ≤ k ∧ k.primeFactors = Nat.primesLE b.Q ∧
      0 ≤ X - log (k : ℝ) ∧
      actualDefect X k - completeFirstLayerLoss X k +
        referencePrice X * (X - log (k : ℝ)) ≤ η / X) :
    0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧
    actualDefect X m - completeFirstLayerLoss X m ≤
      6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
        |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
          (X ^ 2 * log (X / 2)) + η / X := by
  rcases hrepair with ⟨k, hk, hkprefix, hslack, hcost⟩
  rcases hb with ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩
  have hcompare := (two_price_compare hm hk hμ hrecord hclock hslack).2
  have hmprefix := (price_record_prime_structure hm hμ hrecord).2
  have hcancel := complete_first_layer_prefix_cancellation (by linarith : 4 < X)
    hmprefix hkprefix hP hQ hr hroot
  have hlogb : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
    rw [hbdef, Nat.cast_mul,
      log_mul (by exact_mod_cast (higher_core_pos (strictInteger (referencePrice X))).ne')
        (by exact_mod_cast (prefix_integer_pos b.Q).ne'), prefix_integer_log, ← hhdef]
  have hHidentity : log (higherCore m : ℝ) =
      log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ) :=
    higher_core_log (by omega : 0 < m) hmprefix
  have hmassCore : Chebyshev.theta (largestPrime m : ℝ) - Chebyshev.theta (b.Q : ℝ) =
      b.h + b.δ - log (higherCore m : ℝ) := by
    rw [hHidentity]
    rw [hlogb] at hbudget
    linarith
  have hmass : Chebyshev.theta (largestPrime m : ℝ) - Chebyshev.theta (b.Q : ℝ) =
      b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ)) := by
    simpa only [hHidentity] using hmassCore
  rw [hmass] at hcancel
  have horiented := (le_abs_self (completeFirstLayerLoss X k -
    completeFirstLayerLoss X m)).trans hcancel
  have hdrop : 0 ≤ μ * (X - log (k : ℝ)) := mul_nonneg hμ.le hslack
  exact ⟨residual_nonneg (by linarith) (by omega), by nlinarith⟩

/-- A single own-log threshold, before every literal original m and every
positive original price. The chosen Budget retains its ORIGINAL delta in the
block identity; the repaired integer's actual slack is used in comparison. -/
theorem actual_record_repaired_prefix_residual :
    ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, 1 < X0 ∧
    ∀ m : ℕ, 2 ≤ m → ∀ μ : ℝ, 0 < μ →
      (∀ a : ℕ, 0 < a → a < m →
        goldenResourceObjective μ a < goldenResourceObjective μ m) →
      X0 ≤ log (m : ℝ) →
      ∃ b : Budget, b.spec (log (m : ℝ)) ∧
        0 ≤ actualDefect (log (m : ℝ)) m - completeFirstLayerLoss (log (m : ℝ)) m ∧
        actualDefect (log (m : ℝ)) m - completeFirstLayerLoss (log (m : ℝ)) m ≤
          6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
            |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
              ((log (m : ℝ)) ^ 2 * log (log (m : ℝ) / 2)) + η / log (m : ℝ) := by
  intro η hη
  classical
  obtain ⟨T, hT1, hrepair⟩ := actual_higher_layer_budget_repair η hη
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧
    ∀ a : ℕ, 0 < a → a < v.1 →
      goldenResourceObjective v.2 a < goldenResourceObjective v.2 v.1}
  let m : S → ℕ := fun x => x.1.1
  let μ : S → ℝ := fun x => x.1.2
  let X : S → ℝ := fun x => log (m x : ℝ)
  let l : Filter S := comap X atTop
  have hX : Tendsto X l atTop := tendsto_comap
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hμ (x : S) : 0 < μ x := x.2.2.1
  have hrec (x : S) (a : ℕ) : 0 < a → a < m x →
      goldenResourceObjective (μ x) a < goldenResourceObjective (μ x) (m x) := x.2.2.2 a
  have hb := hX.eventually canonical_budget_eventually
  have hbounds := original_record_bounds m μ hm hμ hrec hX
  have hall : ∀ᶠ x in l,
      ∃ b : Budget, b.spec (X x) ∧
        0 ≤ actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x) ∧
        actualDefect (X x) (m x) - completeFirstLayerLoss (X x) (m x) ≤
          6 * max (|(largestPrime (m x) : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
            |b.h + b.δ - (log (m x : ℝ) - Chebyshev.theta (largestPrime (m x) : ℝ))| /
              ((X x) ^ 2 * log (X x / 2)) + η / X x := by
    filter_upwards [hb, hbounds, hX.eventually_ge_atTop T,
      hX.eventually_ge_atTop 14] with x hb hbounds hxT hx14
    obtain ⟨b, hb⟩ := hb
    obtain ⟨k, hk, hkp, hs, hi0, hi, hc0, hc, htel⟩ := hrepair (X x) hxT b hb
    exact ⟨b, hb, repaired_comparison hη hx14 (hm x) (hμ x) (hrec x) rfl
      hbounds.1 b hb ⟨k, hk, hkp, hs, hc⟩⟩
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn price hprice hrec hlarge
  let x : S := ⟨(n, price), hn, hprice, hrec⟩
  have hx := hB (log (n : ℝ)) ((le_max_left B 2).trans hlarge) x rfl
  simpa only [X, m] using hx

#print axioms actual_higher_layer_budget_repair
#print axioms actual_record_repaired_prefix_residual
end D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
