/- GID: D5/S3/Analytic/SeriesInequalities/CarrierDecayThreshold
   generality: I
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/CarrierDecayThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A dyadic counting bound with logarithmic decay implies the sharp power-series threshold. -/

/- Library-search audit trail (2026-09-04):
* Repository searches covered carrier/decay/counting/summability keywords, spelling variants,
  formalization receipts, module digests, generalized spectral-series results, and every remote
  `lane/math/*` delta. No existing declaration gives this counting-to-summability threshold.
* The nearest repository result, `summable_spectral_rpow`, assumes an increasing enumeration with
  linear density and only proves the strict power threshold; it does not cover arbitrary carriers
  or the logarithmic endpoint.
* Pinned-Mathlib searches found no direct counting-function theorem. This proof directly reuses
  `summable_partition`, `Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`,
  `Nat.card_le_card_of_injective`, `Summable.of_norm_bounded_eventually_nat`,
  `summable_geometric_of_lt_one`, and `Real.summable_one_div_nat_rpow`.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace D5.S3.Analytic.SeriesInequalities.CarrierDecayThreshold

open Filter

/-- The number of carrier elements strictly below `N`. -/
noncomputable def carrierCountBelow (carrier : ℕ → Prop) (N : ℕ) : ℕ :=
  Nat.card {n : ℕ // carrier n ∧ n < N}

private def dyadicShell (carrier : ℕ → Prop) (k : ℕ) : Set {n : ℕ // carrier n} :=
  {n | n.1 < 2 ^ (k + 1) ∧ Nat.log 2 n.1 = k}

private lemma existsUnique_mem_dyadicShell (carrier : ℕ → Prop) (n : {n : ℕ // carrier n}) :
    ∃! k, n ∈ dyadicShell carrier k := by
  refine ⟨Nat.log 2 n.1, ⟨Nat.lt_pow_succ_log_self (by norm_num) n.1, rfl⟩, ?_⟩
  intro k hk
  exact hk.2.symm

private lemma dyadicShell_finite (carrier : ℕ → Prop) (k : ℕ) :
    (dyadicShell carrier k).Finite := by
  refine ((Set.finite_Iio (2 ^ (k + 1))).preimage Subtype.val_injective.injOn).subset ?_
  intro n hn
  exact hn.1

private lemma dyadicShell_card_le_countBelow (carrier : ℕ → Prop) (k : ℕ) :
    Nat.card (dyadicShell carrier k) ≤ carrierCountBelow carrier (2 ^ (k + 1)) := by
  let below : Set ℕ := {n | carrier n ∧ n < 2 ^ (k + 1)}
  have hbelow : below.Finite :=
    (Set.finite_Iio (2 ^ (k + 1))).subset fun _ hn => hn.2
  letI : Fintype (dyadicShell carrier k) := (dyadicShell_finite carrier k).fintype
  letI : Fintype below := hbelow.fintype
  let inclusion : dyadicShell carrier k → below := fun n =>
    ⟨n.1.1, n.1.2, n.2.1⟩
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun n : below => n.1) hab))
  unfold carrierCountBelow
  change Nat.card (dyadicShell carrier k) ≤ Nat.card below
  exact Nat.card_le_card_of_injective inclusion hinclusion

private lemma dyadicShell_term_le (carrier : ℕ → Prop) (hzero : ¬ carrier 0)
    {q : ℝ} (hq : 0 ≤ q) (k : ℕ) (n : dyadicShell carrier k) :
    (n.1.1 : ℝ) ^ (-q) ≤ ((2 : ℝ) ^ (-q)) ^ k := by
  have hn0 : n.1.1 ≠ 0 := by
    intro hn
    apply hzero
    simpa [hn] using n.1.2
  have hpowNat : 2 ^ k ≤ n.1.1 := by
    simpa only [n.2.2] using Nat.pow_log_le_self 2 hn0
  have hpowReal : (2 : ℝ) ^ k ≤ (n.1.1 : ℝ) := by
    exact_mod_cast hpowNat
  calc
    (n.1.1 : ℝ) ^ (-q) ≤ ((2 : ℝ) ^ k) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpowReal (by linarith)
    _ = (2 : ℝ) ^ ((k : ℝ) * (-q)) :=
      (Real.rpow_natCast_mul (by positivity) k (-q)).symm
    _ = (2 : ℝ) ^ ((-q) * (k : ℝ)) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ (-q)) ^ k :=
      Real.rpow_mul_natCast (by positivity) (-q) k

private lemma dyadicShell_sum_le (carrier : ℕ → Prop) (hzero : ¬ carrier 0)
    {q : ℝ} (hq : 0 ≤ q) (k : ℕ) :
    ∑' n : dyadicShell carrier k, (n.1.1 : ℝ) ^ (-q) ≤
      (carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) * ((2 : ℝ) ^ (-q)) ^ k := by
  letI : Fintype (dyadicShell carrier k) := (dyadicShell_finite carrier k).fintype
  rw [tsum_fintype]
  calc
    ∑ n : dyadicShell carrier k, (n.1.1 : ℝ) ^ (-q) ≤
        ∑ _n : dyadicShell carrier k, ((2 : ℝ) ^ (-q)) ^ k := by
      exact Finset.sum_le_sum fun n _ => dyadicShell_term_le carrier hzero hq k n
    _ = (Nat.card (dyadicShell carrier k) : ℝ) * ((2 : ℝ) ^ (-q)) ^ k := by
      rw [Nat.card_eq_fintype_card]
      simp
    _ ≤ (carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) *
        ((2 : ℝ) ^ (-q)) ^ k := by
      gcongr
      exact_mod_cast dyadicShell_card_le_countBelow carrier k

private lemma dyadic_base_factor (delta q : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (-q)) ^ k =
      ((2 : ℝ) ^ (-delta)) ^ k * ((2 : ℝ) ^ (delta - q)) ^ k := by
  rw [← mul_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

/-- A dyadic carrier bound with logarithmic decay gives both the strict exponent threshold and
the sharp logarithmic endpoint. Fixed factors from replacing `x` by `2^(k+1)` are absorbed in
`C`. Excluding zero prevents totalized negative powers from hiding the singular term. -/
theorem carrier_decay_threshold (carrier : ℕ → Prop) (C delta beta q : ℝ)
    (hzero : ¬ carrier 0) (hC : 0 ≤ C) (hdelta : 0 ≤ delta) (hbeta : 0 ≤ beta)
    (hcount : ∀ᶠ k : ℕ in atTop,
      (carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) *
          ((2 : ℝ) ^ (-delta)) ^ k ≤ C / ((k + 1 : ℕ) : ℝ) ^ beta)
    (hthreshold : delta < q ∨ q = delta ∧ 1 < beta) :
    Summable (fun n : {n : ℕ // carrier n} => (n.1 : ℝ) ^ (-q)) := by
  have hq : 0 ≤ q := hthreshold.elim (fun h => by linarith) (fun h => h.1 ▸ hdelta)
  let shellSum : ℕ → ℝ := fun k =>
    ∑' n : dyadicShell carrier k, (n.1.1 : ℝ) ^ (-q)
  have hshell_nonneg (k : ℕ) : 0 ≤ shellSum k :=
    tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hshell_le (k : ℕ) :
      shellSum k ≤ (carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) *
        ((2 : ℝ) ^ (-q)) ^ k :=
    dyadicShell_sum_le carrier hzero hq k
  have hshell_summable : Summable shellSum := by
    rcases hthreshold with hstrict | ⟨rfl, hcritical⟩
    · let ratio : ℝ := (2 : ℝ) ^ (delta - q)
      have hratio0 : 0 ≤ ratio := Real.rpow_nonneg (by norm_num) _
      have hratio1 : ratio < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hmajorant : Summable (fun k : ℕ => C * ratio ^ k) :=
        (summable_geometric_of_lt_one hratio0 hratio1).mul_left C
      refine Summable.of_norm_bounded_eventually_nat hmajorant ?_
      filter_upwards [hcount] with k hk
      rw [Real.norm_eq_abs, abs_of_nonneg (hshell_nonneg k)]
      calc
        shellSum k ≤ (carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) *
            ((2 : ℝ) ^ (-q)) ^ k := hshell_le k
        _ = ((carrierCountBelow carrier (2 ^ (k + 1)) : ℝ) *
              ((2 : ℝ) ^ (-delta)) ^ k) * ratio ^ k := by
            rw [dyadic_base_factor delta q k]
            simp only [ratio, mul_assoc]
        _ ≤ (C / ((k + 1 : ℕ) : ℝ) ^ beta) * ratio ^ k := by
            gcongr
        _ ≤ C * ratio ^ k := by
            gcongr
            exact div_le_self hC (Real.one_le_rpow (by norm_num) hbeta)
    · have hpseries : Summable (fun k : ℕ => 1 / (k : ℝ) ^ beta) :=
        Real.summable_one_div_nat_rpow.mpr hcritical
      have hmajorant : Summable (fun k : ℕ => C / ((k + 1 : ℕ) : ℝ) ^ beta) := by
        simpa [div_eq_mul_inv, Nat.cast_add] using
          ((summable_nat_add_iff 1).mpr hpseries).mul_left C
      refine Summable.of_norm_bounded_eventually_nat hmajorant ?_
      filter_upwards [hcount] with k hk
      rw [Real.norm_eq_abs, abs_of_nonneg (hshell_nonneg k)]
      exact (hshell_le k).trans hk
  rw [summable_partition
    (s := dyadicShell carrier)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n.1) (-q))
    (existsUnique_mem_dyadicShell carrier)]
  refine ⟨?_, hshell_summable⟩
  intro k
  letI : Fintype (dyadicShell carrier k) := (dyadicShell_finite carrier k).fintype
  exact Summable.of_finite

#print axioms carrier_decay_threshold

end D5.S3.Analytic.SeriesInequalities.CarrierDecayThreshold
