/- GID: D5/S3/RenyiDivergence/OrderInfinityLimit
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Renyi divergence tends to log maximum likelihood ratio at infinite order. -/

import Mathlib
import D5.S3.RenyiDivergence.OrderLimits

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-15, pinned repository and pinned mathlib):
   * `D5/S3/RenyiDivergence/OrderLimits.lean:34` provides the frozen upper bound
     `renyi_divergence_le_log_sup_ratio`, reused below without reproving it.
   * `Mathlib/Data/Finset/Lattice/Fold.lean:551` provides `Finset.le_sup'`, and line 747
     provides `Finset.exists_mem_eq_sup'`, which attains a nonempty finite supremum.
   * `Mathlib/Topology/Order/Basic.lean:219` provides the eventual-inequality squeeze theorem
     `tendsto_of_tendsto_of_tendsto_of_le_of_le'`; lines 230--234 provide its global variant.
   * `Mathlib/Topology/Algebra/Order/Field.lean:212` provides `Filter.Tendsto.div_atTop`,
     and lines 222--224 provide its constant-numerator specialization `const_div_atTop`.
   * `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:132` and line 137 provide
     `Real.log_mul` and `Real.log_div`; `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:490`
     provides `Real.log_rpow`.
   * A repository search for a topological infinite-order Renyi limit found no prior result;
     `D5/S3/RenyiDivergence/OrderLimits.lean:26` explicitly records this missing half.
-/

namespace D5.S3.RenyiDivergence.OrderInfinityLimit

open Filter

/-- Finite Renyi divergence converges at infinite order to the logarithm of the largest
likelihood ratio. Positivity of `q` is required only on the positive support of `p`. -/
theorem renyi_divergence_tendsto_log_sup_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : ∀ i, 0 < p i → 0 < q i) :
    Filter.Tendsto (fun a : ℝ => renyiDivergence a p q) Filter.atTop
      (nhds (Real.log (Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i)))) := by
  classical
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i)
  obtain ⟨imax, _, himax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => p i / q i)
  have hM_eq : M = p imax / q imax := by
    simpa [M] using himax
  have hp_exists : ∃ i, 0 < p i := by
    have hsum_pos : 0 < ∑ i, p i := by
      rw [hp.2]
      norm_num
    rcases (Finset.sum_pos_iff_of_nonneg fun i _ => hp.1 i).mp hsum_pos with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  have hratio_le (i : ι) : p i / q i ≤ M := by
    change p i / q i ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => p j / q j)
    exact Finset.le_sup' (fun j : ι => p j / q j) (Finset.mem_univ i)
  have hM_pos : 0 < M := by
    rcases hp_exists with ⟨i, hi⟩
    exact (div_pos hi (hq i hi)).trans_le (hratio_le i)
  have hp_imax_ne : p imax ≠ 0 := by
    intro hp_zero
    have hM_zero : M = 0 := by
      simpa [hp_zero] using hM_eq
    exact hM_pos.ne' hM_zero
  have hp_imax : 0 < p imax :=
    lt_of_le_of_ne (hp.1 imax) (Ne.symm hp_imax_ne)
  have hq_imax : 0 < q imax := hq imax hp_imax
  have hlower_bound (a : ℝ) (ha : 1 < a) :
      (Real.log (q imax) + a * Real.log M) / (a - 1) ≤ renyiDivergence a p q := by
    have ha_pos : 0 < a := zero_lt_one.trans ha
    have hterm_nonneg (i : ι) :
        0 ≤ (p i) ^ a * (q i) ^ (1 - a) := by
      by_cases hp_zero : p i = 0
      · rw [hp_zero, Real.zero_rpow ha_pos.ne', zero_mul]
      · have hp_pos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hp_zero)
        exact mul_nonneg
          (Real.rpow_nonneg hp_pos.le a)
          (Real.rpow_nonneg (hq i hp_pos).le (1 - a))
    have hterm_pos :
        0 < (p imax) ^ a * (q imax) ^ (1 - a) :=
      mul_pos (Real.rpow_pos_of_pos hp_imax a)
        (Real.rpow_pos_of_pos hq_imax (1 - a))
    have hterm_le_sum :
        (p imax) ^ a * (q imax) ^ (1 - a) ≤
          ∑ i, (p i) ^ a * (q i) ^ (1 - a) :=
      Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ imax)
    have hlog_le :
        Real.log ((p imax) ^ a * (q imax) ^ (1 - a)) ≤
          Real.log (∑ i, (p i) ^ a * (q i) ^ (1 - a)) :=
      Real.log_le_log hterm_pos hterm_le_sum
    have hlog_term :
        Real.log ((p imax) ^ a * (q imax) ^ (1 - a)) =
          Real.log (q imax) + a * Real.log M := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hp_imax a).ne'
          (Real.rpow_pos_of_pos hq_imax (1 - a)).ne',
        Real.log_rpow hp_imax, Real.log_rpow hq_imax, hM_eq,
        Real.log_div hp_imax.ne' hq_imax.ne']
      ring
    rw [renyiDivergence]
    calc
      (Real.log (q imax) + a * Real.log M) / (a - 1) =
          Real.log ((p imax) ^ a * (q imax) ^ (1 - a)) / (a - 1) := by
            rw [hlog_term]
      _ ≤ Real.log (∑ i, (p i) ^ a * (q i) ^ (1 - a)) / (a - 1) :=
        div_le_div_of_nonneg_right hlog_le (sub_nonneg.mpr ha.le)
      _ = (1 / (a - 1)) *
          Real.log (∑ i, (p i) ^ a * (q i) ^ (1 - a)) := by
        ring
  have hden : Tendsto (fun a : ℝ => a - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_id : Tendsto (fun a : ℝ => a) atTop atTop))
  have hlower :
      Tendsto (fun a : ℝ => (Real.log (q imax) + a * Real.log M) / (a - 1)) atTop
        (nhds (Real.log M)) := by
    have hrearranged :
        Tendsto
          (fun a : ℝ => Real.log M + (Real.log (q imax) + Real.log M) / (a - 1))
          atTop (nhds (Real.log M)) := by
      simpa using
        tendsto_const_nhds.add (hden.const_div_atTop (Real.log (q imax) + Real.log M))
    refine hrearranged.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
    field_simp [sub_ne_zero.mpr ha.ne']
    ring
  change Tendsto (fun a : ℝ => renyiDivergence a p q) atTop (nhds (Real.log M))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
    exact hlower_bound a ha
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with a ha
    simpa [M] using renyi_divergence_le_log_sup_ratio a p q ha hp hq

#print axioms renyi_divergence_tendsto_log_sup_ratio

end D5.S3.RenyiDivergence.OrderInfinityLimit
