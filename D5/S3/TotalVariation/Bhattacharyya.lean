/- GID: D5/S3/TotalVariation/Bhattacharyya
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Bhattacharyya
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite Bhattacharyya affinity and prove the Bretagnolle--Huber bound. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `Hellinger`, `Bhattacharyya`, `Renyi`, `Rényi`,
     `affinity`, `Bretagnolle`, `Huber`, `sum_mul_sq_le_sq_mul_sq`,
     `sum_sq_le_sum_mul_sum_of_sq_le_mul`, `sum_sqrt_mul_sqrt_le`,
     `strictConcaveOn_log_Ioi`, `ConvexOn.map_sum_le`, and `ConcaveOn.le_map_sum`.
   * No probability-theory Hellinger affinity, Bhattacharyya coefficient, Rényi divergence,
     or Bretagnolle--Huber bound was found. The only Hellinger hits concern the unrelated
     Hellinger--Toeplitz theorem. The finite Cauchy--Schwarz and Jensen lemmas above are reused.
   * Repository grep over every Lean declaration below `D5/S3` found no existing declaration
     for these notions or bounds. The frozen `klDivergence`, total variation, and their existing
     support conventions are imported rather than redefined.
-/

import D5.S3.TotalVariation.Metric

namespace D5.S3.TotalVariation.Bhattacharyya

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker

/-- The Bhattacharyya coefficient (Hellinger affinity) of two finite real mass functions. -/
noncomputable def bhattacharyya {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i * q i)

/-- A nonnegative normalized mass function has self-affinity one. This pins both the square root
and the product normalization in the definition. -/
theorem bhattacharyya_self {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    bhattacharyya p p = 1 := by
  rw [bhattacharyya]
  calc
    (∑ i, Real.sqrt (p i * p i)) = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sqrt_mul_self (hp.1 i)
    _ = 1 := hp.2

/-- Pointwise-disjoint mass functions have zero affinity. Together with self-affinity, this rules
out a one-sided definition that ignores either input. -/
theorem bhattacharyya_eq_zero_of_mul_eq_zero {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hdisjoint : ∀ i, p i * q i = 0) :
    bhattacharyya p q = 0 := by
  rw [bhattacharyya]
  apply Finset.sum_eq_zero
  intro i _
  rw [hdisjoint i, Real.sqrt_zero]

/-- The Bhattacharyya coefficient of two nonnegative normalized mass functions is at most one. -/
theorem bhattacharyya_le_one {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    bhattacharyya p q ≤ 1 := by
  rw [bhattacharyya]
  calc
    (∑ i, Real.sqrt (p i * q i)) =
        ∑ i, Real.sqrt (p i) * Real.sqrt (q i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sqrt_mul (hp.1 i) (q i)
    _ ≤ Real.sqrt (∑ i, p i) * Real.sqrt (∑ i, q i) := by
      simpa using Real.sum_sqrt_mul_sqrt_le Finset.univ hp.1 hq.1
    _ = 1 := by rw [hp.2, hq.2]; norm_num

/-- Total variation is bounded by the complementary square of Bhattacharyya affinity. -/
theorem total_variation_sq_le_one_sub_bhattacharyya_sq
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    totalVariation p q ^ 2 ≤ 1 - bhattacharyya p q ^ 2 := by
  have habs (i : ι) :
      |p i - q i| =
        |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
    calc
      |p i - q i| =
          |Real.sqrt (p i) ^ 2 - Real.sqrt (q i) ^ 2| := by
        rw [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i)]
      _ = |(Real.sqrt (p i) - Real.sqrt (q i)) *
          (Real.sqrt (p i) + Real.sqrt (q i))| := by ring_nf
      _ = |Real.sqrt (p i) - Real.sqrt (q i)| *
          (Real.sqrt (p i) + Real.sqrt (q i)) := by
        rw [abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hminus :
      (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) =
        2 - 2 * bhattacharyya p q := by
    rw [bhattacharyya]
    calc
      (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) =
          ∑ i, (p i + q i - 2 * Real.sqrt (p i * q i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sq_abs]
        calc
          (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 =
              Real.sqrt (p i) ^ 2 + Real.sqrt (q i) ^ 2 -
                2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by ring
          _ = p i + q i - 2 * Real.sqrt (p i * q i) := by
            rw [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i),
              Real.sqrt_mul (hp.1 i) (q i)]
      _ = 2 - 2 * ∑ i, Real.sqrt (p i * q i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2,
          Finset.mul_sum]
        ring
  have hplus :
      (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) =
        2 + 2 * bhattacharyya p q := by
    rw [bhattacharyya]
    calc
      (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) =
          ∑ i, (p i + q i + 2 * Real.sqrt (p i * q i)) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 =
              Real.sqrt (p i) ^ 2 + Real.sqrt (q i) ^ 2 +
                2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by ring
          _ = p i + q i + 2 * Real.sqrt (p i * q i) := by
            rw [Real.sq_sqrt (hp.1 i), Real.sq_sqrt (hq.1 i),
              Real.sqrt_mul (hp.1 i) (q i)]
      _ = 2 + 2 * ∑ i, Real.sqrt (p i * q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hp.2, hq.2,
          Finset.mul_sum]
        ring
  have hcs :
      (∑ i, |p i - q i|) ^ 2 ≤
        (2 - 2 * bhattacharyya p q) *
          (2 + 2 * bhattacharyya p q) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : ι => |Real.sqrt (p i) - Real.sqrt (q i)|)
      (fun i : ι => Real.sqrt (p i) + Real.sqrt (q i))
    calc
      (∑ i, |p i - q i|) ^ 2 =
          (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| *
            (Real.sqrt (p i) + Real.sqrt (q i))) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact habs i
      _ ≤ (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) *
          ∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 := this
      _ = (2 - 2 * bhattacharyya p q) *
          (2 + 2 * bhattacharyya p q) := by rw [hminus, hplus]
  rw [totalVariation]
  nlinarith

/-- The exponential of negative KL divergence is bounded by squared Bhattacharyya affinity.
Only `p` is normalized: Jensen uses `p` as its weights. The reference mass `q` needs
nonnegativity and discrete absolute continuity so every ratio on the positive support of `p` is
strictly positive. -/
theorem exp_neg_kl_divergence_le_bhattacharyya_sq
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    Real.exp (-klDivergence p q) ≤ bhattacharyya p q ^ 2 := by
  classical
  let support : Finset ι := Finset.univ.filter fun i => 0 < p i
  have hp_pos (i : ι) (hi : i ∈ support) : 0 < p i := by
    exact (Finset.mem_filter.mp hi).2
  have hq_pos (i : ι) (hi : i ∈ support) : 0 < q i := by
    have hqi : q i ≠ 0 := by
      intro hzero
      have := hac i hzero
      linarith [hp_pos i hi]
    exact lt_of_le_of_ne (hq_nonneg i) (Ne.symm hqi)
  have hsum_p : ∑ i ∈ support, p i = 1 := by
    calc
      (∑ i ∈ support, p i) = ∑ i, p i := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        have hnot_pos : ¬0 < p i := by
          intro hpi
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
        exact le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
      _ = 1 := hp.2
  have hratio_pos (i : ι) (hi : i ∈ support) : 0 < q i / p i :=
    div_pos (hq_pos i hi) (hp_pos i hi)
  have hweighted_affinity (i : ι) (hi : i ∈ support) :
      p i * Real.sqrt (q i / p i) = Real.sqrt (p i * q i) := by
    calc
      p i * Real.sqrt (q i / p i) =
          p i * (Real.sqrt (q i) / Real.sqrt (p i)) := by
        rw [Real.sqrt_div (hq_nonneg i)]
      _ = Real.sqrt (p i) * Real.sqrt (q i) := by
        field_simp [(Real.sqrt_pos.2 (hp_pos i hi)).ne']
        rw [Real.sq_sqrt (hp.1 i)]
        ring
      _ = Real.sqrt (p i * q i) := by
        rw [Real.sqrt_mul (hp.1 i) (q i)]
  have haffinity :
      (∑ i ∈ support, p i * Real.sqrt (q i / p i)) = bhattacharyya p q := by
    rw [bhattacharyya]
    calc
      (∑ i ∈ support, p i * Real.sqrt (q i / p i)) =
          ∑ i ∈ support, Real.sqrt (p i * q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hweighted_affinity i hi
      _ = ∑ i, Real.sqrt (p i * q i) := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        have hnot_pos : ¬0 < p i := by
          intro hpi
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
        have hpi_zero : p i = 0 := le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
        simp [hpi_zero]
  have hlog_term (i : ι) (hi : i ∈ support) :
      p i * Real.log (Real.sqrt (q i / p i)) =
        -(p i * Real.log (p i / q i)) / 2 := by
    rw [Real.log_sqrt (hratio_pos i hi).le,
      Real.log_div (hq_pos i hi).ne' (hp_pos i hi).ne',
      Real.log_div (hp_pos i hi).ne' (hq_pos i hi).ne']
    ring
  have hlog_support :
      (∑ i ∈ support, p i * Real.log (Real.sqrt (q i / p i))) =
        -klDivergence p q / 2 := by
    calc
      (∑ i ∈ support, p i * Real.log (Real.sqrt (q i / p i))) =
          ∑ i ∈ support, (-(p i * Real.log (p i / q i)) / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hlog_term i hi
      _ = -(∑ i ∈ support, p i * Real.log (p i / q i)) / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
      _ = -(∑ i, p i * Real.log (p i / q i)) / 2 := by
        congr 2
        apply Finset.sum_subset (Finset.subset_univ support)
        intro i _ hi
        have hnot_pos : ¬0 < p i := by
          intro hpi
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩)
        have hpi_zero : p i = 0 := le_antisymm (le_of_not_gt hnot_pos) (hp.1 i)
        simp [hpi_zero]
      _ = -klDivergence p q / 2 := by rw [klDivergence]
  have hjensen :
      (∑ i ∈ support, p i * Real.log (Real.sqrt (q i / p i))) ≤
        Real.log (∑ i ∈ support, p i * Real.sqrt (q i / p i)) := by
    have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := support) (w := p) (p := fun i => Real.sqrt (q i / p i))
      (fun i _ => hp.1 i) hsum_p
      (fun i hi => Real.sqrt_pos.2 (hratio_pos i hi))
    simpa only [smul_eq_mul] using h
  rw [hlog_support, haffinity] at hjensen
  have hlinear : -klDivergence p q ≤ 2 * Real.log (bhattacharyya p q) := by
    linarith
  have hexists : ∃ i ∈ support, 0 < p i := by
    apply (Finset.sum_pos_iff_of_nonneg fun i _ => hp.1 i).mp
    rw [hsum_p]
    norm_num
  have haffinity_pos : 0 < bhattacharyya p q := by
    rw [← haffinity]
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hp.1 i) (Real.sqrt_nonneg _))
    rcases hexists with ⟨i, hi, hpi⟩
    exact ⟨i, hi, mul_pos hpi (Real.sqrt_pos.2 (hratio_pos i hi))⟩
  calc
    Real.exp (-klDivergence p q) ≤
        Real.exp (2 * Real.log (bhattacharyya p q)) :=
      Real.exp_le_exp.mpr hlinear
    _ = Real.exp (Real.log (bhattacharyya p q)) *
        Real.exp (Real.log (bhattacharyya p q)) := by
      rw [show 2 * Real.log (bhattacharyya p q) =
        Real.log (bhattacharyya p q) + Real.log (bhattacharyya p q) by ring,
        Real.exp_add]
    _ = bhattacharyya p q ^ 2 := by
      rw [Real.exp_log haffinity_pos]
      ring

/-- The Bretagnolle--Huber bound. Unlike Pinsker's square-root bound, its right side remains
strictly below one for every finite KL divergence. -/
theorem bretagnolle_huber {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    totalVariation p q ≤ Real.sqrt (1 - Real.exp (-klDivergence p q)) := by
  have hA := total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  have hB := exp_neg_kl_divergence_le_bhattacharyya_sq p q hp hq.1 hac
  have hsq :
      totalVariation p q ^ 2 ≤ 1 - Real.exp (-klDivergence p q) :=
    hA.trans (sub_le_sub_left hB 1)
  have hkl : 0 ≤ klDivergence p q :=
    D5.S3.Divergence.GrandmotherTheorem.kl_divergence_nonneg p q hp hq hac
  have hexp_le_one : Real.exp (-klDivergence p q) ≤ 1 := by
    calc
      Real.exp (-klDivergence p q) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr hkl)
      _ = 1 := Real.exp_zero
  exact (Real.le_sqrt
    (D5.S3.TotalVariation.Metric.total_variation_nonneg p q)
    (sub_nonneg.mpr hexp_le_one)).2 hsq

/-- The Bretagnolle--Huber bound is strict for a point mass against the uniform distribution on
two points. -/
theorem bretagnolle_huber_strict_witness :
    totalVariation
        (fun b : Bool => if b then (1 : ℝ) else 0)
        (fun _ : Bool => (1 / 2 : ℝ)) <
      Real.sqrt
        (1 - Real.exp (-klDivergence
          (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun _ : Bool => (1 / 2 : ℝ)))) := by
  have htv :
      totalVariation
          (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun _ : Bool => (1 / 2 : ℝ)) = 1 / 2 := by
    norm_num [totalVariation, Fintype.sum_bool]
  have hkl :
      klDivergence
          (fun b : Bool => if b then (1 : ℝ) else 0)
          (fun _ : Bool => (1 / 2 : ℝ)) = Real.log 2 := by
    norm_num [klDivergence, Fintype.sum_bool]
  rw [htv, hkl, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show 1 - (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by norm_num)

end D5.S3.TotalVariation.Bhattacharyya
