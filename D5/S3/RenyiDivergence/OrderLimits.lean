/- GID: D5/S3/RenyiDivergence/OrderLimits
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/OrderLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound finite Renyi divergence by its max-ratio and KL order members. -/

/- Library-search audit trail (2026-08-13):
   * Searched pinned mathlib and `D5/S3` for `Renyi`, `Rényi`, max divergence,
     variational forms, `Finset.sup'`, log monotonicity, real powers, and weighted Jensen.
   * No finite Renyi/max-divergence or variational theorem was found. Mathlib's Renyi-name hits
     are random graphs, and its measure-valued KL has no bridge to the frozen real finite sum.
   * Reused `Finset.le_sup'`, `Real.rpow_le_rpow`, `Real.log_le_log`, `Real.log_rpow`, and
     `ConcaveOn.le_map_sum`. The walked import closure is Monotone -> Basic -> Bhattacharyya ->
     Metric -> Pinsker -> {GrandmotherTheorem, ZeroSupportDPI} -> ClassicalDPI -> Mathlib.
-/

import D5.S3.RenyiDivergence.Monotone

namespace D5.S3.RenyiDivergence

open D5.S3.Divergence.ClassicalDPI

/-!
This module proves the finite, limit-free max-ratio ceiling and both standard comparisons with
KL. It does not prove a topological limit at infinity or at one, define max-divergence as a new
notion, prove a variational formula, or identify the literal totalized order-one value with KL.
That literal value is zero by definition; KL appears here only as the finite order-one member.
-/

/-- Above order one, Renyi divergence is at most the logarithm of the largest likelihood ratio.
Only positivity of `q` on the positive support of `p` is needed; normalization of nonnegative
`p` supplies a positive support point. `Nonempty ι` is needed by `Finset.sup'`. -/
theorem renyi_divergence_le_log_sup_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 1 < alpha)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : forall i, 0 < p i -> 0 < q i) :
    renyiDivergence alpha p q <=
      Real.log (Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i)) := by
  fail_if_success ((try simp); done)
  classical
  let M : Real := Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i)
  have hexists : Exists fun i => 0 < p i := by
    have hsum_pos : 0 < ∑ i, p i := by rw [hp.2]; norm_num
    rcases (Finset.sum_pos_iff_of_nonneg fun i _ => hp.1 i).mp hsum_pos with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  have hratio_nonneg (i : ι) : 0 <= p i / q i := by
    by_cases hpi : p i = 0
    · simp [hpi]
    · exact div_nonneg (hp.1 i) (hq i (lt_of_le_of_ne (hp.1 i) (Ne.symm hpi))).le
  have hratio_le (i : ι) : p i / q i <= M :=
    Finset.le_sup' (fun i => p i / q i) (Finset.mem_univ i)
  have hM_pos : 0 < M := by
    rcases hexists with ⟨i, hi⟩
    exact (div_pos hi (hq i hi)).trans_le (hratio_le i)
  have hsum_as_mean :
      (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
        ∑ i, p i * (p i / q i) ^ (alpha - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi, Real.zero_rpow (ne_of_gt (zero_lt_one.trans halpha))]
    · have hpi_pos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi)
      calc
        (p i) ^ alpha * (q i) ^ (1 - alpha) =
            ((p i) ^ (1 : Real) * (p i) ^ (alpha - 1)) *
              ((q i) ^ (alpha - 1))⁻¹ := by
          rw [← Real.rpow_add hpi_pos, ← Real.rpow_neg (hq i hpi_pos).le]
          congr 2 <;> ring
        _ = p i * ((p i) ^ (alpha - 1) / (q i) ^ (alpha - 1)) := by
          rw [Real.rpow_one, div_eq_mul_inv]
          ring
        _ = p i * (p i / q i) ^ (alpha - 1) := by
          rw [Real.div_rpow (hp.1 i) (hq i hpi_pos).le]
  have hmoment : (∑ i, p i * (p i / q i) ^ (alpha - 1)) <= M ^ (alpha - 1) := by
    calc
      (∑ i, p i * (p i / q i) ^ (alpha - 1)) <= ∑ i, p i * M ^ (alpha - 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hratio_nonneg i) (hratio_le i)
            (sub_nonneg.mpr halpha.le)) (hp.1 i)
      _ = M ^ (alpha - 1) := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hsum_pos : 0 < ∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha) := by
    rw [hsum_as_mean]
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hp.1 i)
      (Real.rpow_nonneg (hratio_nonneg i) (alpha - 1)))
    rcases hexists with ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, mul_pos hi
      (Real.rpow_pos_of_pos (div_pos hi (hq i hi)) (alpha - 1))⟩
  have hlog := Real.log_le_log hsum_pos (hsum_as_mean.trans_le hmoment)
  rw [renyiDivergence]
  calc
    (1 / (alpha - 1)) * Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
        Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) / (alpha - 1) := by ring
    _ <= Real.log (M ^ (alpha - 1)) / (alpha - 1) :=
      div_le_div_of_nonneg_right hlog (sub_nonneg.mpr halpha.le)
    _ = Real.log M := by
      rw [Real.log_rpow hM_pos]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr halpha.ne')

/-- Jensen's logarithmic moment bound, the common structural step behind both KL comparisons. -/
theorem renyi_log_moment_ge_kl {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 0 < alpha)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : forall i, 0 < p i -> 0 < q i) :
    (alpha - 1) * klDivergence p q <=
      Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) := by
  fail_if_success ((try simp); done)
  classical
  let support : Finset ι := Finset.univ.filter fun i => 0 < p i
  have hp_pos (i : ι) (hi : i ∈ support) : 0 < p i := (Finset.mem_filter.mp hi).2
  have hratio_pos (i : ι) (hi : i ∈ support) : 0 < p i / q i :=
    div_pos (hp_pos i hi) (hq i (hp_pos i hi))
  have hsum_p : ∑ i ∈ support, p i = 1 := by
    calc
      (∑ i ∈ support, p i) = ∑ i, p i := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        have hnot_pos : ¬0 < p i := fun hpi =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
        exact le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
      _ = 1 := hp.2
  have hkl_support :
      (∑ i ∈ support, p i * Real.log (p i / q i)) = klDivergence p q := by
    rw [klDivergence]
    apply Finset.sum_subset (Finset.subset_univ support)
    intro i _ hi
    have hnot_pos : ¬0 < p i := fun hpi =>
      hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
    have hpi : p i = 0 := le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
    simp [hpi]
  have hsum_as_mean :
      (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
        ∑ i, p i * (p i / q i) ^ (alpha - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi, Real.zero_rpow halpha.ne']
    · have hpi_pos : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi)
      have hqi_pos : 0 < q i := hq i hpi_pos
      calc
        (p i) ^ alpha * (q i) ^ (1 - alpha) =
            ((p i) ^ (1 : Real) * (p i) ^ (alpha - 1)) *
              ((q i) ^ (alpha - 1))⁻¹ := by
          rw [← Real.rpow_add hpi_pos, ← Real.rpow_neg hqi_pos.le]
          congr 2 <;> ring
        _ = p i * ((p i) ^ (alpha - 1) / (q i) ^ (alpha - 1)) := by
          rw [Real.rpow_one, div_eq_mul_inv]
          ring
        _ = p i * (p i / q i) ^ (alpha - 1) := by
          rw [Real.div_rpow (hp.1 i) hqi_pos.le]
  have hmoment_support :
      (∑ i ∈ support, p i * (p i / q i) ^ (alpha - 1)) =
        ∑ i, p i * (p i / q i) ^ (alpha - 1) := by
    apply Finset.sum_subset (Finset.subset_univ support)
    intro i _ hi
    have hnot_pos : ¬0 < p i := fun hpi =>
      hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
    have hpi : p i = 0 := le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
    simp [hpi]
  have hjensen := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (t := support) (w := p) (p := fun i => (p i / q i) ^ (alpha - 1))
    (fun i _ => hp.1 i) hsum_p
    (fun i hi => Real.rpow_pos_of_pos (hratio_pos i hi) (alpha - 1))
  calc
    (alpha - 1) * klDivergence p q =
        ∑ i ∈ support, p i * Real.log ((p i / q i) ^ (alpha - 1)) := by
      rw [← hkl_support, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_rpow (hratio_pos i hi)]
      ring
    _ <= Real.log (∑ i ∈ support, p i * (p i / q i) ^ (alpha - 1)) := by
      simpa only [smul_eq_mul] using hjensen
    _ = Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) := by
      rw [hmoment_support, hsum_as_mean]

/-- Below order one, Renyi divergence is at most KL divergence. -/
theorem renyi_divergence_le_kl_of_lt_one {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 0 < alpha ∧ alpha < 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : forall i, 0 < p i -> 0 < q i) :
    renyiDivergence alpha p q <= klDivergence p q := by
  fail_if_success ((try simp); done)
  have h := renyi_log_moment_ge_kl alpha p q halpha.1 hp hq
  rw [renyiDivergence]
  rw [show (1 / (alpha - 1)) * Real.log
    (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
      Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) / (alpha - 1) by ring]
  rw [div_le_iff_of_neg (sub_neg.mpr halpha.2)]
  simpa [mul_comm] using h

/-- Above order one, KL divergence is at most Renyi divergence. -/
theorem kl_le_renyi_divergence_of_one_lt {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 1 < alpha)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : forall i, 0 < p i -> 0 < q i) :
    klDivergence p q <= renyiDivergence alpha p q := by
  fail_if_success ((try simp); done)
  have h := renyi_log_moment_ge_kl alpha p q (zero_lt_one.trans halpha) hp hq
  rw [renyiDivergence]
  rw [show (1 / (alpha - 1)) * Real.log
    (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) =
      Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) / (alpha - 1) by ring]
  rw [le_div_iff₀ (sub_pos.mpr halpha)]
  simpa [mul_comm] using h

/-- The below-one comparison at order one half agrees with the frozen affinity formula. -/
theorem renyi_divergence_one_half_le_kl {ι : Type*} [Fintype ι]
    (p q : ι -> Real) (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : forall i, 0 < p i -> 0 < q i) :
    -2 * Real.log (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya p q) <=
      klDivergence p q := by
  fail_if_success ((try simp); done)
  rw [← renyi_divergence_one_half p q hp.1]
  exact renyi_divergence_le_kl_of_lt_one (1 / 2) p q (by norm_num) hp hq

#print axioms renyi_divergence_le_log_sup_ratio
#print axioms renyi_log_moment_ge_kl
#print axioms renyi_divergence_le_kl_of_lt_one
#print axioms kl_le_renyi_divergence_of_one_lt
#print axioms renyi_divergence_one_half_le_kl

end D5.S3.RenyiDivergence
