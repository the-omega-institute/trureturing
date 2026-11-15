/- GID: D5/S3/Analytic/Probability/NoncompactQuantile
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NoncompactQuantile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrable quantile-bin means preserve order and have uniform absolute tails. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
The quantile-bin arguments extend the existing port from danlyng/Econlib
revision d7bd9477476cade1c6695c8891746048ceddc52f to integrable laws.
-/
import D5.S3.Analytic.Probability.ConditionalMeanApproximation
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Equal quantile-bin means for arbitrary integrable real probability laws. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open Econlib.Probability

noncomputable section

namespace Econlib.Probability.NoncompactQuantile

open private bin_endpoints volume_real_bin bins_pairwise_disjoint_Ioc
  from D5.S3.Analytic.Probability.ConditionalMeanAtoms
open private integrable_quantile_Ioo integrable_quantile_Ioc
  integral_quantile_Ioo_split upperIntegratedQuantile_le_stopLoss_add
  upperIntegratedQuantile_eq_stopLoss_add
  from D5.S3.Analytic.Probability.CompactConvexOrder

private lemma integrable_bin {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    IntegrableOn (Measure.quantile μ.toMeasure)
      (Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
  obtain ⟨h0, h1, _⟩ := bin_endpoints hn k
  exact (integrable_quantile_Ioc hμ (le_refl (0 : ℝ))).mono_set
    (fun _ hu => ⟨lt_of_le_of_lt h0 hu.1, hu.2.trans h1⟩)

private lemma integral_finite_law (p : DiscreteLaw) (f : ℝ → ℝ) :
    ∫ x, f x ∂p.toProbDist.toMeasure = ∑ k, p.weight k * f (p.atom k) := by
  rw [DiscreteLaw.toProbDist_toMeasure,
    integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (p.weight_nonneg _)]

private lemma bin_tail_le {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n)
    (k : Fin n) {R : ℝ} (hR : 0 ≤ R) :
    (1 / (n : ℝ)) * (if R < |DiscreteLaw.condMeanAtom μ n hn k|
      then |DiscreteLaw.condMeanAtom μ n hn k| else 0) ≤
      2 * ∫ u in Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        {u : ℝ | R / 2 < |Measure.quantile μ.toMeasure u|}.indicator
          (fun u => |Measure.quantile μ.toMeasure u|) u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hint := integrable_bin hμ hn k
  let q := Measure.quantile μ.toMeasure
  let s := Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)
  let T := {u : ℝ | R / 2 < |q u|}.indicator (fun u => |q u|)
  have hT : IntegrableOn T s := hint.abs.indicator₀ (by
    simpa only [Real.norm_eq_abs] using
      aestronglyMeasurable_const.nullMeasurableSet_lt hint.aestronglyMeasurable.norm)
  have hTnonneg : 0 ≤ ∫ u in s, T u := integral_nonneg fun _ =>
    indicator_nonneg (fun u _ => abs_nonneg (q u)) _
  by_cases ha : R < |DiscreteLaw.condMeanAtom μ n hn k|
  · rw [ite_eq_left ha]
    have hconst : IntegrableOn (fun _ : ℝ => R / 2) s :=
      integrableOn_const (by dsimp [s]; rw [Real.volume_Ioc]; finiteness)
    have hsplit : (∫ u in s, |q u|) ≤ (1 / (n : ℝ)) * (R / 2) + ∫ u in s, T u := by
      calc
        _ ≤ ∫ u in s, R / 2 + T u := by
          apply integral_mono_ae hint.abs (hconst.add hT)
          filter_upwards with u
          change |q u| ≤ R / 2 + T u
          by_cases hu : R / 2 < |q u|
          · simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hu]; linarith
          · simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hu, add_zero]; exact le_of_not_gt hu
        _ = _ := by rw [integral_add hconst hT, setIntegral_const, show volume.real s = 1 / (n : ℝ) from volume_real_bin hn k,
          smul_eq_mul]
    have habs : (1 / (n : ℝ)) * |DiscreteLaw.condMeanAtom μ n hn k| ≤ ∫ u in s, |q u| := by
      rw [DiscreteLaw.condMeanAtom, abs_mul, abs_of_pos hnR]
      have hc : (1 / (n : ℝ)) * ((n : ℝ) * |∫ u in s, q u|) = |∫ u in s, q u| := by
        field_simp
      rw [hc]
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := q) (μ := volume.restrict s))
    have hpos : 0 < 1 / (n : ℝ) := by positivity
    have hlarge := mul_lt_mul_of_pos_left ha hpos
    dsimp [T, s, q] at *
    linarith
  · rw [ite_eq_right ha, mul_zero]
    exact mul_nonneg (by norm_num) hTnonneg

/-- Conditional means on equal quantile bins have genuine absolute first-moment tails,
uniformly controlled by the original law. -/
theorem absolute_tail_le {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) (n : ℕ) (hn : 0 < n)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in {x : ℝ | R < |x|}, |x|
      ∂(DiscreteLaw.condMeanAtomize μ n hn).toProbDist.toMeasure) ≤
      2 * ∫ x in {x : ℝ | R / 2 < |x|}, |x| ∂μ.toMeasure := by
  let f : ℝ → ℝ := {x : ℝ | R / 2 < |x|}.indicator (fun x => |x|)
  have hf : Integrable f μ.toMeasure := hμ.abs.indicator (measurableSet_lt measurable_const
    continuous_abs.measurable)
  have hq : IntegrableOn (fun u => f (Measure.quantile μ.toMeasure u)) (Ioo (0 : ℝ) 1) := by
    have hh := integrable_map_measure (by
      rw [Measure.map_quantile_volume_Ioo]; exact hf.aestronglyMeasurable)
      (Measure.aemeasurable_quantile_restrict_Ioo (μ := μ.toMeasure))
    rw [Measure.map_quantile_volume_Ioo] at hh
    exact hh.mp hf
  rw [← integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable),
    integral_finite_law]
  change (∑ k : Fin n, (1 / (n : ℝ)) *
    {x : ℝ | R < |x|}.indicator (fun x => |x|) (DiscreteLaw.condMeanAtom μ n hn k)) ≤ _
  calc
    _ ≤ ∑ k : Fin n, 2 * ∫ u in Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        f (Measure.quantile μ.toMeasure u) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [f, Set.indicator_apply, Set.mem_ofPred_eq] using bin_tail_le hμ hn k hR
    _ = 2 * ∫ u in Ioo (0 : ℝ) 1, f (Measure.quantile μ.toMeasure u) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [← integral_Ico_eq_integral_Ioc]
      rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico)
        (Measure.bins_pairwise_disjoint n)]
      · rw [Measure.iUnion_bins_eq_Ico n hn, integral_Ico_eq_integral_Ioo]
      · intro k
        rw [integrableOn_Ico_iff_integrableOn_Ioo]
        exact hq.mono_set fun u hu =>
          ⟨lt_of_le_of_lt (bin_endpoints hn k).1 hu.1,
            lt_of_lt_of_le hu.2 (bin_endpoints hn k).2.1⟩
    _ = _ := by
      rw [← Measure.integral_eq_integral_quantile f hf.aestronglyMeasurable]
      dsimp only [f]
      rw [integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]

open DiscreteLaw
open private binIndex binIndex_lt bin_of_binIndex_bounds condStepFun
  aestronglyMeasurable_condStepFun abs_condStepFun_le integral_condStepFun_Ioo
  integral_toProbDist_condMeanAtomize
  from D5.S3.Analytic.Probability.ConditionalMeanApproximation

private lemma atom_monotone {μ : ProbDist ℝ}
    (h : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n) :
    Monotone (fun k : Fin n => condMeanAtom μ n hn k) := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  intro i j hij
  by_cases heq : i = j
  · rw [heq]
  have hlt : i < j := lt_of_le_of_ne hij heq
  have hij_lt : (i : ℕ) < (j : ℕ) := hlt
  have hij_succ_le : (i : ℕ) + 1 ≤ (j : ℕ) := hij_lt
  have h_ij_R : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij_succ_le
  have h_i_succ_lt : (i : ℕ) + 1 < n := lt_of_le_of_lt hij_succ_le j.isLt
  set r : ℝ := ((i : ℝ) + 1) / n with hr_def
  have hr_pos : 0 < r := by
    change 0 < ((i : ℝ) + 1) / n
    apply div_pos _ hn_pos_R
    have hknn : (0 : ℝ) ≤ i := by exact_mod_cast (Nat.zero_le (i : ℕ))
    linarith
  have hr_lt_1 : r < 1 := by
    change ((i : ℝ) + 1) / n < 1
    rw [div_lt_one hn_pos_R]
    exact_mod_cast h_i_succ_lt
  have hr_mem : r ∈ Ioo (0 : ℝ) 1 := ⟨hr_pos, hr_lt_1⟩
  set s : ℝ := (j : ℝ) / n with hs_def
  have hs_pos : 0 < s := by
    change 0 < (j : ℝ) / n
    apply div_pos _ hn_pos_R
    have : 0 < (j : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hij_lt
    exact_mod_cast this
  have hs_lt_1 : s < 1 := by
    change (j : ℝ) / n < 1
    rw [div_lt_one hn_pos_R]
    exact_mod_cast j.isLt
  have hs_mem : s ∈ Ioo (0 : ℝ) 1 := ⟨hs_pos, hs_lt_1⟩
  have hrs : r ≤ s := by
    change ((i : ℝ) + 1) / n ≤ (j : ℝ) / n
    apply div_le_div_of_nonneg_right h_ij_R hn_pos_R.le
  have hq_rs : MeasureTheory.Measure.quantile μ.toMeasure r ≤
      MeasureTheory.Measure.quantile μ.toMeasure s :=
    MeasureTheory.Measure.monotoneOn_quantile hr_mem hs_mem hrs
  obtain ⟨h0_i, h1_i, hlt_i⟩ := bin_endpoints hn i
  obtain ⟨h0_j, h1_j, hlt_j⟩ := bin_endpoints hn j
  have h_bin_i_ae_le :
      ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc ((i : ℝ) / n) r)),
        MeasureTheory.Measure.quantile μ.toMeasure u ≤
          MeasureTheory.Measure.quantile μ.toMeasure r := by
    have h_ae_ne : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ r :=
      MeasureTheory.Measure.ae_ne _ r
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h_ae_ne] with u hu_ne hu_bin
    have hu_pos : 0 < u := lt_of_le_of_lt h0_i hu_bin.1
    have hu_lt_r : u < r := lt_of_le_of_ne hu_bin.2 hu_ne
    have hu_lt_1 : u < 1 := lt_trans hu_lt_r hr_lt_1
    exact MeasureTheory.Measure.monotoneOn_quantile
      ⟨hu_pos, hu_lt_1⟩ hr_mem hu_lt_r.le
  have h_int_i := integrable_bin h hn i
  have hbin_i_finite :
      (MeasureTheory.volume : Measure ℝ)
          (Set.Ioc ((i : ℝ) / n) r) ≠ ⊤ := by
    change (MeasureTheory.volume : Measure ℝ)
      (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) ≠ ⊤
    rw [Real.volume_Ioc]; simp
  have h_int_const_r :
      MeasureTheory.IntegrableOn (fun _ : ℝ =>
        MeasureTheory.Measure.quantile μ.toMeasure r)
        (Set.Ioc ((i : ℝ) / n) r) :=
    MeasureTheory.integrableOn_const (hs := hbin_i_finite)
  have h_int_le :
      ∫ u in Set.Ioc ((i : ℝ) / n) r,
          MeasureTheory.Measure.quantile μ.toMeasure u ≤
      ∫ _ in Set.Ioc ((i : ℝ) / n) r,
          MeasureTheory.Measure.quantile μ.toMeasure r := by
    apply MeasureTheory.integral_mono_ae h_int_i h_int_const_r
    exact h_bin_i_ae_le
  have h_const_i : ∫ _ in Set.Ioc ((i : ℝ) / n) r,
          MeasureTheory.Measure.quantile μ.toMeasure r =
      (1 / n) * MeasureTheory.Measure.quantile μ.toMeasure r := by
    rw [MeasureTheory.setIntegral_const]
    rw [volume_real_bin hn i, smul_eq_mul]
  have h_atom_i_le :
      condMeanAtom μ n hn i ≤ MeasureTheory.Measure.quantile μ.toMeasure r := by
    change (n : ℝ) * ∫ u in Set.Ioc ((i : ℝ) / n) r,
        MeasureTheory.Measure.quantile μ.toMeasure u ≤ _
    have hstep : (n : ℝ) * ∫ u in Set.Ioc ((i : ℝ) / n) r,
        MeasureTheory.Measure.quantile μ.toMeasure u ≤
      (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure r) := by
      calc _ ≤ (n : ℝ) * ∫ _ in Set.Ioc ((i : ℝ) / n) r,
                    MeasureTheory.Measure.quantile μ.toMeasure r :=
            mul_le_mul_of_nonneg_left h_int_le hn_pos_R.le
        _ = (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure r) := by rw [h_const_i]
    have hsimp : (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure r) =
        MeasureTheory.Measure.quantile μ.toMeasure r := by field_simp
    linarith
  have h_bin_j_ae_le :
      ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc s (((j : ℝ) + 1) / n))),
        MeasureTheory.Measure.quantile μ.toMeasure s ≤
          MeasureTheory.Measure.quantile μ.toMeasure u := by
    have h_ae_ne : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ 1 :=
      MeasureTheory.Measure.ae_ne _ 1
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h_ae_ne] with u hu_ne hu_bin
    have hu_pos : 0 < u := lt_trans hs_pos hu_bin.1
    have hu_le1 : u ≤ 1 := hu_bin.2.trans h1_j
    have hu_lt1 : u < 1 := lt_of_le_of_ne hu_le1 hu_ne
    exact MeasureTheory.Measure.monotoneOn_quantile
      hs_mem ⟨hu_pos, hu_lt1⟩ hu_bin.1.le
  have h_int_j := integrable_bin h hn j
  have hbin_j_finite :
      (MeasureTheory.volume : Measure ℝ)
          (Set.Ioc s (((j : ℝ) + 1) / n)) ≠ ⊤ := by
    change (MeasureTheory.volume : Measure ℝ)
      (Set.Ioc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) ≠ ⊤
    rw [Real.volume_Ioc]; simp
  have h_int_const_s :
      MeasureTheory.IntegrableOn (fun _ : ℝ =>
        MeasureTheory.Measure.quantile μ.toMeasure s)
        (Set.Ioc s (((j : ℝ) + 1) / n)) :=
    MeasureTheory.integrableOn_const (hs := hbin_j_finite)
  have h_int_ge :
      ∫ _ in Set.Ioc s (((j : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure s ≤
      ∫ u in Set.Ioc s (((j : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure u := by
    apply MeasureTheory.integral_mono_ae h_int_const_s h_int_j
    exact h_bin_j_ae_le
  have h_const_j : ∫ _ in Set.Ioc s (((j : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure s =
      (1 / n) * MeasureTheory.Measure.quantile μ.toMeasure s := by
    rw [MeasureTheory.setIntegral_const, volume_real_bin hn j, smul_eq_mul]
  have h_atom_j_ge :
      MeasureTheory.Measure.quantile μ.toMeasure s ≤ condMeanAtom μ n hn j := by
    change _ ≤ (n : ℝ) * ∫ u in Set.Ioc s (((j : ℝ) + 1) / n),
      MeasureTheory.Measure.quantile μ.toMeasure u
    have hstep : (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure s) ≤
        (n : ℝ) * ∫ u in Set.Ioc s (((j : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure u := by
      calc (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure s)
          = (n : ℝ) * ∫ _ in Set.Ioc s (((j : ℝ) + 1) / n),
                MeasureTheory.Measure.quantile μ.toMeasure s := by rw [h_const_j]
        _ ≤ _ := mul_le_mul_of_nonneg_left h_int_ge hn_pos_R.le
    have hsimp : (n : ℝ) * (1 / n * MeasureTheory.Measure.quantile μ.toMeasure s) =
        MeasureTheory.Measure.quantile μ.toMeasure s := by field_simp
    linarith
  exact h_atom_i_le.trans (hq_rs.trans h_atom_j_ge)

private lemma prefix_eq {μ : ProbDist ℝ}
    (h : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n) (K : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val),
        condMeanAtom μ n hn i) =
      (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  have h_atom : ∀ i : Fin n, condMeanAtom μ n hn i =
      (n : ℝ) * ∫ u in Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := fun _ => rfl
  simp_rw [h_atom]
  rw [← Finset.mul_sum]
  congr 1
  have h_union :
      (⋃ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val),
        Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) = Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n) := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · rintro ⟨i, hi_le, hu_lo, hu_hi⟩
      obtain ⟨h0, _, _⟩ := bin_endpoints hn i
      refine ⟨lt_of_le_of_lt h0 hu_lo, ?_⟩
      have : ((i : ℝ) + 1) / n ≤ ((K.val + 1 : ℝ) / n) := by
        apply div_le_div_of_nonneg_right _ hn_pos_R.le
        have hi_le' : (i : ℝ) ≤ K.val := by exact_mod_cast hi_le
        linarith
      linarith
    · rintro ⟨hu_lo, hu_hi⟩
      set y : ℝ := (n : ℝ) * u with hy_def
      have hy_pos : 0 < y := mul_pos hn_pos_R hu_lo
      have hy_le_Kplus1 : y ≤ (K.val + 1 : ℝ) := by
        rw [hy_def]
        calc (n : ℝ) * u ≤ (n : ℝ) * ((K.val + 1 : ℝ) / n) :=
              mul_le_mul_of_nonneg_left hu_hi hn_pos_R.le
          _ = (K.val + 1 : ℝ) := by field_simp
      set m : ℕ := ⌈y⌉₊ with hm_def
      have hm_pos : 1 ≤ m := by rw [hm_def, Nat.one_le_ceil_iff]; exact hy_pos
      have hm_le : m ≤ K.val + 1 := by
        rw [hm_def, Nat.ceil_le]; exact_mod_cast hy_le_Kplus1
      have h_i_val : m - 1 < n := by
        have hK_lt : K.val + 1 ≤ n := K.isLt
        omega
      refine ⟨⟨m - 1, h_i_val⟩, ?_, ?_, ?_⟩
      · change m - 1 ≤ K.val
        omega
      · change ((⟨m - 1, h_i_val⟩ : Fin n) : ℝ) / n < u
        have h_cast : (((⟨m - 1, h_i_val⟩ : Fin n) : ℕ) : ℝ) = (m : ℝ) - 1 := by
          change ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1
          rw [Nat.cast_pred (by omega : 0 < m)]
        rw [h_cast, div_lt_iff₀ hn_pos_R]
        have h_ceil_lt : (m : ℝ) - 1 < y := by
          rw [hm_def]
          have := Nat.ceil_lt_add_one hy_pos.le
          linarith
        linarith [mul_comm u (n : ℝ)]
      · change u ≤ (((⟨m - 1, h_i_val⟩ : Fin n) : ℝ) + 1) / n
        have h_cast : (((⟨m - 1, h_i_val⟩ : Fin n) : ℕ) : ℝ) + 1 = (m : ℝ) := by
          change ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ)
          rw [Nat.cast_pred (by omega : 0 < m)]; ring
        rw [h_cast, le_div_iff₀ hn_pos_R]
        have : y ≤ m := Nat.le_ceil _
        linarith [mul_comm u (n : ℝ)]
  have h_disj :
      (↑(Finset.univ.filter (fun i : Fin n => i.val ≤ K.val)) : Set (Fin n)).Pairwise
        (Function.onFun Disjoint
          (fun k : Fin n => Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) :=
    (bins_pairwise_disjoint_Ioc hn).mono (Set.subset_univ _)
  have h_meas : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val),
      MeasurableSet (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :=
    fun i _ => measurableSet_Ioc
  have h_int : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val),
      MeasureTheory.IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
        (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := fun i _ =>
    integrable_bin h hn i
  rw [← h_union,
    MeasureTheory.integral_biUnion_finset
      (t := Finset.univ.filter (fun i : Fin n => i.val ≤ K.val))
      h_meas h_disj h_int]

private lemma tendsto_condMeanAtom_of_continuousWithinAt
    {μ : ProbDist ℝ} (h : Integrable (fun x : ℝ => x) μ.toMeasure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
      (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => if h : binIndex (n + 1) t < (n + 1) then
        DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨binIndex (n + 1) t, h⟩
      else DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩)
      atTop (𝓝 (MeasureTheory.Measure.quantile μ.toMeasure t)) := by
  have h_idx_lt : ∀ᶠ n in atTop, binIndex (n + 1) t < n + 1 := by
    filter_upwards with n
    exact binIndex_lt (Nat.succ_le_succ (Nat.zero_le n)) ht
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at h_qcts
  obtain ⟨δ, hδ_pos, hδ⟩ := h_qcts (ε / 2) hε2
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  obtain ⟨N1, hN1⟩ := exists_nat_gt (1 / t)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / (1 - t))
  have ht_pos : 0 < t := ht.1
  have ht_sub_pos : 0 < 1 - t := by linarith [ht.2]
  set N := max (max (max N0 N1) N2) 1 with hN_def
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn_succ_ge_1 : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
  have h_np1_R_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hN0_le_n : (N0 : ℝ) ≤ (n : ℝ) := by
    have : N0 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans (le_max_left _ _)
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact_mod_cast le_trans this hn
  have h_small_inv : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
    have h1 : 1 / δ < (n + 1 : ℕ) := by
      calc 1 / δ < (N0 : ℝ) := hN0
        _ ≤ (n : ℝ) := hN0_le_n
        _ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    rw [div_lt_iff₀ hδ_pos] at h1
    linarith
  have hN1_le_n : (N1 : ℝ) ≤ (n : ℝ) := by
    have hN1_le : N1 ≤ N := by
      calc N1 ≤ max N0 N1 := le_max_right _ _
        _ ≤ max (max N0 N1) N2 := le_max_left _ _
        _ ≤ max (max (max N0 N1) N2) 1 := le_max_left _ _
    exact_mod_cast le_trans hN1_le hn
  have hN2_le_n : (N2 : ℝ) ≤ (n : ℝ) := by
    have hN2_le : N2 ≤ N := by
      calc N2 ≤ max (max N0 N1) N2 := le_max_right _ _
        _ ≤ max (max (max N0 N1) N2) 1 := le_max_left _ _
    exact_mod_cast le_trans hN2_le hn
  obtain ⟨hL_le, hR_lt, _⟩ := bin_of_binIndex_bounds hn_succ_ge_1 ht
  set k_nat : ℕ := binIndex (n + 1) t with hk_def
  have hk_lt : k_nat < n + 1 := binIndex_lt hn_succ_ge_1 ht
  have hN1_gt : (1 : ℝ) / t < (N1 : ℝ) := hN1
  have hN2_gt : (1 : ℝ) / (1 - t) < (N2 : ℝ) := hN2
  have h_one_div_np1_lt_t : 1 / ((n + 1 : ℕ) : ℝ) < t := by
    have : 1 / t < (n : ℝ) := lt_of_lt_of_le hN1_gt hN1_le_n
    have h_np1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : 1 / t < ((n + 1 : ℕ) : ℝ) := lt_trans this h_np1
    rw [div_lt_iff₀ ht_pos] at this
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    linarith
  have h_one_div_np1_lt_sub : 1 / ((n + 1 : ℕ) : ℝ) < 1 - t := by
    have : 1 / (1 - t) < (n : ℝ) := lt_of_lt_of_le hN2_gt hN2_le_n
    have h_np1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : 1 / (1 - t) < ((n + 1 : ℕ) : ℝ) := lt_trans this h_np1
    rw [div_lt_iff₀ ht_sub_pos] at this
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    linarith
  have h_left_ge : t - 1 / ((n + 1 : ℕ) : ℝ) ≤ (k_nat : ℝ) / (n + 1 : ℕ) := by
    have h_np1_t : ((n + 1 : ℕ) : ℝ) * t < (k_nat : ℝ) + 1 := by
      rw [lt_div_iff₀ h_np1_R_pos] at hR_lt; linarith
    have h_t_lt : t < ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ h_np1_R_pos]; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [add_div]
    linarith
  have h_right_le : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := by
    have hk_le_nt : (k_nat : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * t := by
      rw [div_le_iff₀ h_np1_R_pos] at hL_le; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by rw [add_div]
    rw [this]
    have hk_le_t : (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ t := hL_le
    linarith
  have h_L_pos : 0 < (k_nat : ℝ) / (n + 1 : ℕ) := by
    have : t - 1 / ((n + 1 : ℕ) : ℝ) > 0 := by linarith
    linarith
  have h_R_lt_1 : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) < 1 := by
    have : t + 1 / ((n + 1 : ℕ) : ℝ) < 1 := by linarith
    linarith
  rw [dite_eq_left hk_lt]
  unfold DiscreteLaw.condMeanAtom
  set bin : Set ℝ := Set.Ioc ((k_nat : ℝ) / (n + 1 : ℕ))
    (((k_nat : ℝ) + 1) / (n + 1 : ℕ)) with hbin_def
  have h_bin_subset_Ioo : bin ⊆ Ioo (0 : ℝ) 1 := by
    rw [hbin_def]
    intro u hu
    refine ⟨lt_of_lt_of_le h_L_pos hu.1.le, lt_of_le_of_lt hu.2 h_R_lt_1⟩
  have h_width_eq : (((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) - (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ))
      = 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [show ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) - (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) =
      ((k_nat : ℝ) + 1 - k_nat) / ((n + 1 : ℕ) : ℝ) from (sub_div _ _ _).symm]
    congr 1; ring
  have hbin_vol_real : (MeasureTheory.volume : Measure ℝ).real bin = 1 / (n + 1 : ℕ) := by
    rw [hbin_def, Real.volume_real_Ioc_of_le]
    · exact h_width_eq
    · have : (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ h_np1_R_pos.le; linarith
      exact this
  have hbin_vol : (MeasureTheory.volume : Measure ℝ) bin ≠ ⊤ := by
    rw [hbin_def, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hbin_meas : MeasurableSet bin := by
    rw [hbin_def]; exact measurableSet_Ioc
  have h_int_quantile : IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      bin := by
    rw [hbin_def]
    exact integrable_bin h (Nat.succ_pos n) ⟨k_nat, hk_lt⟩
  have h_int_const : IntegrableOn (fun _ : ℝ => MeasureTheory.Measure.quantile μ.toMeasure t)
      bin volume := integrableOn_const hbin_vol
  have h_bin_ae_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict bin),
      |MeasureTheory.Measure.quantile μ.toMeasure u
        - MeasureTheory.Measure.quantile μ.toMeasure t| < ε / 2 := by
    rw [MeasureTheory.ae_restrict_iff' hbin_meas]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_Ioo : u ∈ Ioo (0 : ℝ) 1 := h_bin_subset_Ioo hu
    rw [hbin_def] at hu
    have hu_dist : dist u t < δ := by
      rw [Real.dist_eq]
      rcases le_or_gt u t with hle | hgt
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        have : u > t - 1 / ((n + 1 : ℕ) : ℝ) := lt_of_le_of_lt h_left_ge hu.1
        linarith
      · rw [abs_of_pos (sub_pos.mpr hgt)]
        have : u ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := le_trans hu.2 h_right_le
        linarith
    have h_diff : dist (MeasureTheory.Measure.quantile μ.toMeasure u)
        (MeasureTheory.Measure.quantile μ.toMeasure t) < ε / 2 :=
      hδ hu_Ioo hu_dist
    rw [Real.dist_eq] at h_diff
    exact h_diff
  have h_diff_int :
      (∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u)
      - (MeasureTheory.Measure.quantile μ.toMeasure t) * (1 / ((n + 1 : ℕ) : ℝ))
      = ∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t) := by
    rw [integral_sub h_int_quantile h_int_const]
    rw [MeasureTheory.setIntegral_const]
    rw [hbin_vol_real, smul_eq_mul]
    ring
  have h_int_diff_abs :
      ‖∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t)‖
        ≤ (ε / 2) * (1 / ((n + 1 : ℕ) : ℝ)) := by
    have h_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict bin),
        ‖MeasureTheory.Measure.quantile μ.toMeasure u
            - MeasureTheory.Measure.quantile μ.toMeasure t‖ ≤ ε / 2 := by
      filter_upwards [h_bin_ae_bound] with u hu
      rw [Real.norm_eq_abs]
      linarith
    have h_fin : (MeasureTheory.volume : Measure ℝ) bin < ⊤ := by
      rw [hbin_def, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae (C := ε / 2) (s := bin)
      (f := fun u => MeasureTheory.Measure.quantile μ.toMeasure u
        - MeasureTheory.Measure.quantile μ.toMeasure t) h_fin h_bound
    rw [hbin_vol_real] at this
    linarith [this]
  rw [Real.dist_eq]
  have h_cancel : ((n + 1 : ℕ) : ℝ) *
      ((MeasureTheory.Measure.quantile μ.toMeasure t) * (1 / ((n + 1 : ℕ) : ℝ))) =
      MeasureTheory.Measure.quantile μ.toMeasure t := by
    field_simp
  have h_lhs_eq :
      ((n + 1 : ℕ) : ℝ) * (∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u)
      - MeasureTheory.Measure.quantile μ.toMeasure t =
      ((n + 1 : ℕ) : ℝ) *
        ∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t) := by
    rw [← h_diff_int, mul_sub]
    rw [show ((n + 1 : ℕ) : ℝ) *
        (MeasureTheory.Measure.quantile μ.toMeasure t * (1 / ((n + 1 : ℕ) : ℝ))) =
        MeasureTheory.Measure.quantile μ.toMeasure t from h_cancel]
  rw [h_lhs_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  have h_step : ((n + 1 : ℕ) : ℝ) * |∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t|
      ≤ ε / 2 := by
    calc ((n + 1 : ℕ) : ℝ) * |∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u
            - MeasureTheory.Measure.quantile μ.toMeasure t|
        ≤ ((n + 1 : ℕ) : ℝ) * ((ε / 2) * (1 / ((n + 1 : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := h_int_diff_abs
          rw [Real.norm_eq_abs] at this
          exact this
      _ = ε / 2 := by field_simp
  linarith
private lemma tendsto_condStepFun_of_continuousWithinAt
    {μ : ProbDist ℝ} (h : Integrable (fun x : ℝ => x) μ.toMeasure)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
      (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
      (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t))) := by
  have h_atom := tendsto_condMeanAtom_of_continuousWithinAt h ht h_qcts
  have h_cts := (hφ.tendsto _).comp h_atom
  convert h_cts using 1
  funext n
  unfold condStepFun
  simp only [Function.comp_apply]
  split_ifs with h1 <;> rfl
private lemma condStepFun_tendsto_ae
    {μ : ProbDist ℝ} (h : Integrable (fun x : ℝ => x) μ.toMeasure)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∀ᵐ t ∂((MeasureTheory.volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
        (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t))) := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  have h_small :
      {t | t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt
          (MeasureTheory.Measure.quantile μ.toMeasure) (Ioo (0 : ℝ) 1) t}.Countable :=
    MeasureTheory.Measure.countable_not_continuousWithinAt_quantile
      (μ := μ.toMeasure)
  have h_null : (MeasureTheory.volume : Measure ℝ) {t : ℝ |
      t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt
        (MeasureTheory.Measure.quantile μ.toMeasure) (Ioo (0 : ℝ) 1) t} = 0 :=
    h_small.measure_zero _
  rw [ae_iff]
  apply measure_mono_null _ h_null
  intro t ht
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
  obtain ⟨h_t_in, h_no_conv⟩ := ht
  refine ⟨h_t_in, ?_⟩
  intro h_cts
  exact h_no_conv (tendsto_condStepFun_of_continuousWithinAt h hφ h_t_in h_cts)
private theorem means_tendsto {μ : ProbDist ℝ} (h : Integrable (fun x : ℝ => x) μ.toMeasure) :
    Filter.Tendsto (fun n : ℕ =>
      ((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        : MeasureTheory.ProbabilityMeasure ℝ))
      Filter.atTop (nhds μ) := by
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φBC
  set φ : ℝ → ℝ := fun x => φBC x with hφ_def
  have hφ_cts : Continuous φ := φBC.continuous
  set M : ℝ := ‖φBC‖ with hM_def
  have hM : ∀ x, |φ x| ≤ M := fun x => by
    rw [hM_def]
    have := φBC.norm_coe_le_norm x
    simpa [Real.norm_eq_abs] using this
  have h_lhs_eq : (fun n : ℕ => ∫ x, φBC x
      ∂((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure))
      = fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, condStepFun μ φ (n + 1) (Nat.succ_pos n) t := by
    funext n
    rw [integral_condStepFun_Ioo hφ_cts (Nat.succ_pos n)]
    rw [integral_toProbDist_condMeanAtomize hφ_cts (Nat.succ_pos n)]
  rw [h_lhs_eq]
  have h_rhs : ∫ x, φBC x ∂μ.toMeasure
      = ∫ t in Ioo (0 : ℝ) 1, φ (MeasureTheory.Measure.quantile μ.toMeasure t) :=
    MeasureTheory.Measure.integral_eq_integral_quantile φ hφ_cts.aestronglyMeasurable
  change Filter.Tendsto _ Filter.atTop (nhds (∫ x, φBC x ∂μ.toMeasure))
  rw [h_rhs]
  set F : ℕ → ℝ → ℝ := fun n => condStepFun μ φ (n + 1) (Nat.succ_pos n) with hF_def
  change Filter.Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, F n t) Filter.atTop
    (nhds (∫ t in Ioo (0 : ℝ) 1, φ (MeasureTheory.Measure.quantile μ.toMeasure t)))
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ => M) ?_ ?_ ?_ ?_
  · intro n
    exact aestronglyMeasurable_condStepFun hφ_cts (Nat.succ_pos n)
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs]
      exact abs_condStepFun_le hM (Nat.succ_pos n) t)
  · exact condStepFun_tendsto_ae h hφ_cts

private lemma lower_integral_le {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ u in Ioc 0 t, Measure.quantile ν.toMeasure u) ≤
      ∫ u in Ioc 0 t, Measure.quantile μ.toMeasure u := by
  have hupper : (∫ u in Ioc t 1, Measure.quantile μ.toMeasure u) ≤
      ∫ u in Ioc t 1, Measure.quantile ν.toMeasure u := by
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · subst t; simp
    · have h1 := upperIntegratedQuantile_le_stopLoss_add hμ ⟨ht.1.le, ht.2⟩
        (Measure.quantile ν.toMeasure t)
      have h2 := hstop (Measure.quantile ν.toMeasure t)
      have h3 := upperIntegratedQuantile_eq_stopLoss_add hν ⟨ht.1, hlt⟩
      linarith
  have hμsplit := integral_quantile_Ioo_split hμ ht.1 ht.2
  have hνsplit := integral_quantile_Ioo_split hν ht.1 ht.2
  have hμmean : μ.expect id = ∫ u in Ioo (0 : ℝ) 1, Measure.quantile μ.toMeasure u :=
    Measure.integral_eq_integral_quantile (fun x : ℝ => x) aestronglyMeasurable_id
  have hνmean : ν.expect id = ∫ u in Ioo (0 : ℝ) 1, Measure.quantile ν.toMeasure u :=
    Measure.integral_eq_integral_quantile (fun x : ℝ => x) aestronglyMeasurable_id
  linarith

private theorem means_order {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z) (n : ℕ) (hn : 0 < n) :
    DiscreteLaw.ConvexOrder
      (DiscreteLaw.condMeanAtomize μ n hn)
      (DiscreteLaw.condMeanAtomize ν n hn) := by
  intro φ hφ
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  simp only [condMeanAtomize, uniform]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hn_inv_nonneg : (0 : ℝ) ≤ 1 / n := by positivity
  apply mul_le_mul_of_nonneg_left _ hn_inv_nonneg
  set x : Fin n → ℝ := fun k => condMeanAtom μ n hn k with hx_def
  set y : Fin n → ℝ := fun k => condMeanAtom ν n hn k with hy_def
  have hx_mono : Monotone x := atom_monotone hμ hn
  have hy_mono : Monotone y := atom_monotone hν hn
  have hμ_int : Integrable (fun t : ℝ => t) μ.toMeasure :=
    hμ
  have hν_int : Integrable (fun t : ℝ => t) ν.toMeasure :=
    hν
  have hμ_mean : (condMeanAtomize μ n hn).mean = μ.expect id :=
    condMeanAtomize_mean_eq hμ_int n hn
  have hν_mean : (condMeanAtomize ν n hn).mean = ν.expect id :=
    condMeanAtomize_mean_eq hν_int n hn
  have h_sum_x : ∑ i, x i = (n : ℝ) * μ.expect id := by
    have h_mean_eq : (condMeanAtomize μ n hn).mean = (∑ i, x i) / n := by
      simpa only [hx_def, condMeanAtomize] using
        DiscreteLaw.uniform_mean hn (fun k => condMeanAtom μ n hn k)
    rw [hμ_mean] at h_mean_eq
    field_simp at h_mean_eq
    linarith
  have h_sum_y : ∑ i, y i = (n : ℝ) * ν.expect id := by
    have h_mean_eq : (condMeanAtomize ν n hn).mean = (∑ i, y i) / n := by
      simpa only [hy_def, condMeanAtomize] using
        DiscreteLaw.uniform_mean hn (fun k => condMeanAtom ν n hn k)
    rw [hν_mean] at h_mean_eq
    field_simp at h_mean_eq
    linarith
  have hsum : ∑ i, x i = ∑ i, y i := by
    rw [h_sum_x, h_sum_y, hmean]
  have hpart : ∀ K : Fin n,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) := by
    intro K
    have h_partial_μ :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u := by
      simpa [hx_def] using prefix_eq hμ hn K
    have h_partial_ν :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u := by
      simpa [hy_def] using prefix_eq hν hn K
    rw [h_partial_μ, h_partial_ν]
    have ht_pos : (0 : ℝ) < ((K.val + 1 : ℝ) / n) := by
      apply div_pos _ hn_pos_R
      have : (0 : ℕ) < K.val + 1 := Nat.succ_pos _
      exact_mod_cast this
    have ht_le_1 : ((K.val + 1 : ℝ) / n) ≤ 1 := by
      rw [div_le_one hn_pos_R]
      have hKlt : K.val + 1 ≤ n := K.isLt
      exact_mod_cast hKlt
    have h_ineq :
        (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u) ≤
          (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u) :=
      lower_integral_le hμ hν hmean hstop ⟨ht_pos, ht_le_1⟩
    exact mul_le_mul_of_nonneg_left h_ineq hn_pos_R.le
  exact sum_convex_le_of_partial_sum_ge x y hx_mono hy_mono hsum hpart hφ

private lemma uniform_absolute_tails {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ,
      (∫ x in {x : ℝ | R < |x|}, |x|
        ∂(condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure) < ε := by
  have htend : Tendsto (fun m : ℕ => ∫ x,
      {x : ℝ | (m : ℝ) < |x|}.indicator (fun x => |x|) x ∂μ.toMeasure)
      atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence
      (F := fun m : ℕ => {x : ℝ | (m : ℝ) < |x|}.indicator (fun x => |x|))
      (f := fun _ : ℝ => (0 : ℝ)) (bound := fun x : ℝ => |x|)
      (fun m => (hμ.abs.indicator (measurableSet_lt measurable_const
        continuous_abs.measurable)).aestronglyMeasurable) hμ.abs
      (fun m => ae_of_all _ fun x => by
        by_cases hx : (m : ℝ) < |x| <;>
          simp [Set.indicator_apply, hx, Real.norm_eq_abs, abs_nonneg])
      (ae_of_all _ fun x => ?_)
    · simpa using hh
    · obtain ⟨N, hN⟩ := exists_nat_gt |x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with m hm
      have hx : ¬(m : ℝ) < |x| := by
        have : (N : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      simp [hx]
  intro ε hε
  have hsmall := htend.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨2 * ((N + 1 : ℕ) : ℝ), by positivity, fun n => ?_⟩
  have hb := absolute_tail_le hμ (n + 1) (Nat.succ_pos n)
    (R := 2 * ((N + 1 : ℕ) : ℝ)) (by positivity)
  have he := hN (N + 1) (by omega)
  rw [integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)] at he
  have hr : 2 * ((N + 1 : ℕ) : ℝ) / 2 = ((N + 1 : ℕ) : ℝ) := by ring
  rw [hr] at hb
  linarith

private lemma tail_map (ρ : Measure (ℝ × ℝ)) (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) (R : ℝ) :
    (∫ p in {p : ℝ × ℝ | R < |g p|}, |g p| ∂ρ) =
      ∫ x in {x : ℝ | R < |x|}, |x| ∂Measure.map g ρ := by
  let f : ℝ → ℝ := {x : ℝ | R < |x|}.indicator (fun x => |x|)
  have hf : Measurable f := continuous_abs.measurable.indicator
    (measurableSet_lt measurable_const continuous_abs.measurable)
  rw [← integral_indicator (s := {p : ℝ × ℝ | R < |g p|})
      (f := fun p => |g p|) (measurableSet_lt measurable_const
        (continuous_abs.measurable.comp hg)),
    ← integral_indicator (s := {x : ℝ | R < |x|}) (f := fun x => |x|)
      (measurableSet_lt measurable_const continuous_abs.measurable)]
  exact (integral_map hg.aemeasurable hf.aestronglyMeasurable).symm

/-- Equal-resolution quantile-bin laws admit actual finite martingale joints,
converge to the original integrable marginals, and have uniform joint coordinate tails. -/
theorem exists_martingale_approximations {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z) :
    ∃ π : ℕ → ProbDist (ℝ × ℝ),
      (∀ n, IsMartingaleCoupling
        (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist (π n)) ∧
      Tendsto (fun n => (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist)
        atTop (𝓝 μ) ∧
      Tendsto (fun n => (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist)
        atTop (𝓝 ν) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n,
        (∫ p in {p : ℝ × ℝ | R < |p.1|}, |p.1| ∂(π n).toMeasure) +
        (∫ p in {p : ℝ × ℝ | R < |p.2|}, |p.2| ∂(π n).toMeasure) < ε) := by
  have hex : ∀ n : ℕ, ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling
      (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
      (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist π := by
    intro n
    exact DiscreteLaw.exists_martingaleCoupling_uniform _ _ (Nat.succ_pos n) rfl
      (fun _ => rfl) (fun _ => rfl) (means_order hμ hν hmean hstop _ (Nat.succ_pos n))
  choose π hπ using hex
  refine ⟨π, hπ, means_tendsto hμ, means_tendsto hν, ?_⟩
  intro ε hε
  obtain ⟨Rμ, hRμ, hbμ⟩ := uniform_absolute_tails hμ (ε / 2) (by linarith)
  obtain ⟨Rν, hRν, hbν⟩ := uniform_absolute_tails hν (ε / 2) (by linarith)
  refine ⟨max Rμ Rν, lt_max_of_lt_left hRμ, fun n => ?_⟩
  rw [tail_map _ _ measurable_fst, tail_map _ _ measurable_snd]
  change (∫ x in {x : ℝ | max Rμ Rν < |x|}, |x|
    ∂(π n).toMeasure.fst) + (∫ x in {x : ℝ | max Rμ Rν < |x|}, |x|
    ∂(π n).toMeasure.snd) < ε
  rw [(hπ n).fst_measure, (hπ n).snd_measure]
  have hsubμ : {x : ℝ | max Rμ Rν < |x|} ⊆ {x : ℝ | Rμ < |x|} :=
    fun x hx => show Rμ < |x| from lt_of_le_of_lt (le_max_left Rμ Rν) hx
  have hsubν : {x : ℝ | max Rμ Rν < |x|} ⊆ {x : ℝ | Rν < |x|} :=
    fun x hx => show Rν < |x| from lt_of_le_of_lt (le_max_right Rμ Rν) hx
  have hμint : Integrable (fun x : ℝ => |x|)
      (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure := by
    rw [DiscreteLaw.toProbDist_toMeasure]
    exact integrable_finsetSum_measure.mpr fun i _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hνint : Integrable (fun x : ℝ => |x|)
      (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure := by
    rw [DiscreteLaw.toProbDist_toMeasure]
    exact integrable_finsetSum_measure.mpr fun i _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hu := setIntegral_mono_set hμint.integrableOn (ae_of_all _ fun x => abs_nonneg x)
    (ae_of_all _ hsubμ)
  have hv := setIntegral_mono_set hνint.integrableOn (ae_of_all _ fun x => abs_nonneg x)
    (ae_of_all _ hsubν)
  linarith [hbμ n, hbν n]

/-- Continuous bounded displacement tests determine all measurable bounded displacement tests
when both coordinates are integrable. -/
theorem tested_measurable_of_continuous {π : ProbDist (ℝ × ℝ)}
    (hint_fst : Integrable (fun p : ℝ × ℝ => p.1) π.toMeasure)
    (hint_snd : Integrable (fun p : ℝ × ℝ => p.2) π.toMeasure)
    (hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0) :
    ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0 := by
  have h_diff_int : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π.toMeasure :=
    hint_snd.sub hint_fst
  have h_abs_int : Integrable (fun p : ℝ × ℝ => |p.2 - p.1|) π.toMeasure := h_diff_int.abs
  let posW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (p.2 - p.1)
  let negW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (-(p.2 - p.1))
  have hposW_meas : Measurable posW :=
    (measurable_snd.sub measurable_fst).real_toNNReal
  have hnegW_meas : Measurable negW :=
    ((measurable_snd.sub measurable_fst).neg).real_toNNReal
  have h_pos_coe : ∀ p : ℝ × ℝ, ((posW p : ℝ)) = max (p.2 - p.1) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_neg_coe : ∀ p : ℝ × ℝ, ((negW p : ℝ)) = max (-(p.2 - p.1)) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_decomp : ∀ p : ℝ × ℝ, (posW p : ℝ) - (negW p : ℝ) = p.2 - p.1 := by
    intro p; rw [h_pos_coe, h_neg_coe]; exact max_zero_sub_eq_self _
  have h_pos_le_abs : ∀ p : ℝ × ℝ, (posW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_pos_coe]; exact max_le (le_abs_self _) (abs_nonneg _)
  have h_neg_le_abs : ∀ p : ℝ × ℝ, (negW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_neg_coe]; exact max_le (neg_le_abs _) (abs_nonneg _)
  have hposW_int : Integrable (fun p => (posW p : ℝ)) π.toMeasure := by
    refine h_abs_int.mono' ?_ ?_
    · exact (hposW_meas.coe_nnreal_real).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((posW p).coe_nonneg)]; exact h_pos_le_abs p)
  have hnegW_int : Integrable (fun p => (negW p : ℝ)) π.toMeasure := by
    refine h_abs_int.mono' ?_ ?_
    · exact (hnegW_meas.coe_nnreal_real).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((negW p).coe_nonneg)]; exact h_neg_le_abs p)
  let posE : ℝ × ℝ → ENNReal := fun p => (posW p : ENNReal)
  let negE : ℝ × ℝ → ENNReal := fun p => (negW p : ENNReal)
  have hposE_meas : Measurable posE := hposW_meas.coe_nnreal_ennreal
  have hnegE_meas : Measurable negE := hnegW_meas.coe_nnreal_ennreal
  have hposE_lint_ne : ∫⁻ p, posE p ∂π.toMeasure ≠ ⊤ := by
    have : ∫⁻ p, posE p ∂π.toMeasure = ENNReal.ofReal (∫ p, (posW p : ℝ) ∂π.toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hposW_int
        (Filter.Eventually.of_forall (fun p => (posW p).coe_nonneg))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change (posW p : ENNReal) = ENNReal.ofReal ((posW p : ℝ))
      rw [ENNReal.ofReal_coe_nnreal]
    rw [this]; exact ENNReal.ofReal_ne_top
  have hnegE_lint_ne : ∫⁻ p, negE p ∂π.toMeasure ≠ ⊤ := by
    have : ∫⁻ p, negE p ∂π.toMeasure = ENNReal.ofReal (∫ p, (negW p : ℝ) ∂π.toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hnegW_int
        (Filter.Eventually.of_forall (fun p => (negW p).coe_nonneg))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change (negW p : ENNReal) = ENNReal.ofReal ((negW p : ℝ))
      rw [ENNReal.ofReal_coe_nnreal]
    rw [this]; exact ENNReal.ofReal_ne_top
  haveI h_pos_fin : IsFiniteMeasure (π.toMeasure.withDensity posE) :=
    isFiniteMeasure_withDensity hposE_lint_ne
  haveI h_neg_fin : IsFiniteMeasure (π.toMeasure.withDensity negE) :=
    isFiniteMeasure_withDensity hnegE_lint_ne
  let μ_pos : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity posE).map Prod.fst
  let μ_neg : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity negE).map Prod.fst
  haveI : IsFiniteMeasure μ_pos := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure μ_neg := Measure.isFiniteMeasure_map _ _
  have int_pos : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_pos),
      ∫ x, g x ∂μ_pos = ∫ p, (posW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity posE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    rw [integral_withDensity_eq_integral_smul hposW_meas]
    simp only [smul_eq_mul, NNReal.smul_def]
  have int_neg : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_neg),
      ∫ x, g x ∂μ_neg = ∫ p, (negW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity negE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    rw [integral_withDensity_eq_integral_smul hnegW_meas]
    simp only [smul_eq_mul, NNReal.smul_def]
  have int_weighted_pos : ∀ (φ : ℝ → ℝ), Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      Integrable (fun p => (posW p : ℝ) * φ p.1) π.toMeasure := by
    intro φ hφ_meas hφ_bdd
    obtain ⟨M, hM⟩ := hφ_bdd
    have h1 : Integrable (fun p => φ p.1 * (posW p : ℝ)) π.toMeasure :=
      hposW_int.bdd_mul ((hφ_meas.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hM _))
    exact h1.congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have int_weighted_neg : ∀ (φ : ℝ → ℝ), Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      Integrable (fun p => (negW p : ℝ) * φ p.1) π.toMeasure := by
    intro φ hφ_meas hφ_bdd
    obtain ⟨M, hM⟩ := hφ_bdd
    have h1 : Integrable (fun p => φ p.1 * (negW p : ℝ)) π.toMeasure :=
      hnegW_int.bdd_mul ((hφ_meas.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hM _))
    exact h1.congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have h_sub_gen : ∀ (g : ℝ → ℝ), Measurable g → (∃ M, ∀ x, |g x| ≤ M) →
      ∫ p, (posW p : ℝ) * g p.1 ∂π.toMeasure -
        ∫ p, (negW p : ℝ) * g p.1 ∂π.toMeasure =
        ∫ p, (p.2 - p.1) * g p.1 ∂π.toMeasure := by
    intro g hg_meas hg_bdd
    have h_cong : (fun p => (posW p : ℝ) * g p.1 - (negW p : ℝ) * g p.1) =
        fun p => (p.2 - p.1) * g p.1 := by
      funext p; rw [← sub_mul, h_decomp]
    rw [← MeasureTheory.integral_sub (int_weighted_pos g hg_meas hg_bdd)
      (int_weighted_neg g hg_meas hg_bdd), ← h_cong]
  have hμ_eq : μ_pos = μ_neg := by
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
    have hf_cts : Continuous (f : ℝ → ℝ) := f.continuous
    have hf_bdd : ∃ M, ∀ x, |(f : ℝ → ℝ) x| ≤ M :=
      ⟨‖f‖, fun x => (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm x⟩
    have hf_meas : Measurable (f : ℝ → ℝ) := hf_cts.measurable
    have hf_aesm : AEStronglyMeasurable (f : ℝ → ℝ) μ_pos :=
      hf_cts.aestronglyMeasurable
    have hf_aesm' : AEStronglyMeasurable (f : ℝ → ℝ) μ_neg :=
      hf_cts.aestronglyMeasurable
    rw [int_pos (f : ℝ → ℝ) hf_aesm, int_neg (f : ℝ → ℝ) hf_aesm']
    have h_sub := h_sub_gen (f : ℝ → ℝ) hf_meas hf_bdd
    have h_ct := hcts (f : ℝ → ℝ) hf_cts hf_bdd
    linarith
  intro φ hφ_meas hφ_bdd
  obtain ⟨M, hM⟩ := hφ_bdd
  have hφ_aesm_pos : AEStronglyMeasurable φ μ_pos := hφ_meas.aestronglyMeasurable
  have hφ_aesm_neg : AEStronglyMeasurable φ μ_neg := hφ_meas.aestronglyMeasurable
  have heq : ∫ x, φ x ∂μ_pos = ∫ x, φ x ∂μ_neg := by rw [hμ_eq]
  rw [int_pos φ hφ_aesm_pos, int_neg φ hφ_aesm_neg] at heq
  have h_sub := h_sub_gen φ hφ_meas ⟨M, hM⟩
  linarith
end Econlib.Probability.NoncompactQuantile
