/- GID: D5/S3/Analytic/Probability/ConditionalMeanAtoms
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/ConditionalMeanAtoms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ConditionalMeanAtoms for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Probability.CompactConvexOrder
import D5.S3.Analytic.Probability.CompactQuantile
import D5.S3.Analytic.Probability.FiniteMartingaleCoupling
import Mathlib.MeasureTheory.Function.Floor


open MeasureTheory Set Filter Topology

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace Econlib.Probability
namespace DiscreteLaw

/-- The `k`-th conditional-mean atom of `μ`: The average of `quantile μ` over the bin
`(k/n, (k+1)/n]`. -/
noncomputable def condMeanAtom (μ : ProbDist ℝ) (n : ℕ) (_hn : 0 < n) (k : Fin n) : ℝ :=
  (n : ℝ) * ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
    MeasureTheory.Measure.quantile μ.toMeasure u

/-- Uniform discrete law with atoms at conditional means of each equal bin. -/
noncomputable def condMeanAtomize (μ : ProbDist ℝ) (n : ℕ) (hn : 0 < n) : DiscreteLaw :=
  DiscreteLaw.uniform n hn (fun k => DiscreteLaw.condMeanAtom μ n hn k)

end DiscreteLaw
end Econlib.Probability

end
end

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace Econlib.Probability
namespace DiscreteLaw

/-- The bin endpoints `k/n, (k+1)/n` sit in `[0, 1]` with `(k+1)/n ≤ 1`. -/
private lemma bin_endpoints {n : ℕ} (hn : 0 < n) (k : Fin n) :
    0 ≤ ((k : ℝ) / n) ∧ ((k : ℝ) + 1) / n ≤ 1 ∧ ((k : ℝ) / n) < ((k : ℝ) + 1) / n := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · apply div_nonneg
    · exact_mod_cast (Nat.zero_le (k : ℕ))
    · exact hn_pos_R.le
  · rw [div_le_one hn_pos_R]
    have := k.isLt
    have : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
    exact this
  · apply div_lt_div_of_pos_right _ hn_pos_R
    linarith

/-- Volume (as a real) of the `k`-th bin equals `1/n`. -/
private lemma volume_real_bin {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (MeasureTheory.volume : Measure ℝ).real
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) = 1 / n := by
  obtain ⟨_, _, hlt⟩ := bin_endpoints hn k
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  rw [Real.volume_real_Ioc_of_le hlt.le]
  field_simp
  ring

/-- The `Ioc` bins `Ioc (k/n) ((k+1)/n)` are pairwise disjoint across all indices. -/
private lemma bins_pairwise_disjoint_Ioc {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n)).Pairwise
      (Function.onFun Disjoint
        (fun k : Fin n => Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  intro i _ j _ hij
  change Disjoint (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n))
    (Set.Ioc ((j : ℝ) / n) (((j : ℝ) + 1) / n))
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h_le : ((i : ℝ) + 1) / n ≤ (j : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hn_pos_R.le
      have : (i : ℕ) + 1 ≤ (j : ℕ) := hlt
      exact_mod_cast this
    refine Set.disjoint_iff.mpr fun t ht => ?_
    simp only [Set.mem_inter_iff, Set.mem_Ioc] at ht
    linarith [ht.1.2, ht.2.1]
  · have h_le : ((j : ℝ) + 1) / n ≤ (i : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hn_pos_R.le
      have : (j : ℕ) + 1 ≤ (i : ℕ) := hgt
      exact_mod_cast this
    refine Set.disjoint_iff.mpr fun t ht => ?_
    simp only [Set.mem_inter_iff, Set.mem_Ioc] at ht
    linarith [ht.2.2, ht.1.1]

/-- A `μ`-quantile at `u ∈ (0, 1)` lies in any closed interval supporting `μ`. -/
private lemma quantile_mem_Icc_of_supportsOn_Icc {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    MeasureTheory.Measure.quantile μ.toMeasure u ∈ Icc a b := by
  obtain ⟨hu_pos, hu_lt⟩ := hu
  have hμ_Icc : μ.toMeasure (Icc a b) = 1 := h
  set S : Set ℝ := { x : ℝ | u ≤ (μ.toMeasure (Iic x)).toReal } with hS_def
  have hS_ne : S.Nonempty := MeasureTheory.Measure.Quantile.set_nonempty hu_lt
  have hb_in_S : b ∈ S := by
    rw [hS_def]
    simp only [Set.mem_setOf_eq]
    have hIcc_sub : Icc a b ⊆ Iic b := fun x hx => hx.2
    have hmono : μ.toMeasure (Icc a b) ≤ μ.toMeasure (Iic b) := measure_mono hIcc_sub
    have hmeas1 : μ.toMeasure (Iic b) = 1 := by
      have hge : (1 : ENNReal) ≤ μ.toMeasure (Iic b) := by rw [← hμ_Icc]; exact hmono
      have hle : μ.toMeasure (Iic b) ≤ 1 := by
        have : μ.toMeasure (Iic b) ≤ μ.toMeasure Set.univ := measure_mono (Set.subset_univ _)
        simpa using this
      exact le_antisymm hle hge
    rw [hmeas1]
    simp only [ENNReal.toReal_one]
    exact hu_lt.le
  have h_lower : ∀ x ∈ S, a ≤ x := by
    intro x hx
    by_contra hxa
    push Not at hxa
    have h_sub_compl : Iic x ⊆ (Icc a b)ᶜ := by
      intro y hy
      simp only [Set.mem_Iic] at hy
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
      intro _
      linarith
    have h_compl_zero : μ.toMeasure (Icc a b)ᶜ = 0 :=
      (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mpr hμ_Icc
    have h_Iic_zero : μ.toMeasure (Iic x) = 0 := by
      have : μ.toMeasure (Iic x) ≤ μ.toMeasure (Icc a b)ᶜ := measure_mono h_sub_compl
      rw [h_compl_zero] at this
      exact le_antisymm this bot_le
    rw [hS_def] at hx
    simp only [Set.mem_setOf_eq, h_Iic_zero, ENNReal.toReal_zero] at hx
    linarith
  have hS_bddBelow : BddBelow S := ⟨a, h_lower⟩
  refine ⟨?_, ?_⟩
  · exact le_csInf hS_ne h_lower
  · exact csInf_le hS_bddBelow hb_in_S

/-- On the `k`-th bin `Ioc (k/n) ((k+1)/n)`, the quantile lies a.e. in `Icc a b` whenever `μ` is
supported on `Icc a b`. -/
private lemma quantile_mem_Icc_ae_on_bin {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    ∀ᵐ u ∂(MeasureTheory.volume.restrict
        (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))),
      MeasureTheory.Measure.quantile μ.toMeasure u ∈ Icc a b := by
  obtain ⟨h0, h1, _⟩ := bin_endpoints hn k
  -- On the bin, `u ∈ (k/n, (k+1)/n] ⊆ (0, 1]`. The only point not in `Ioo 0 1` is `u = 1`,
  -- which has Lebesgue measure zero (`volume` has no atoms).
  have h_ae : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ 1 :=
    MeasureTheory.Measure.ae_ne _ 1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h_ae] with u hu hu_bin
  have hu_pos : 0 < u := lt_of_le_of_lt h0 hu_bin.1
  have hu_le_1 : u ≤ 1 := hu_bin.2.trans h1
  have hu_lt : u < 1 := lt_of_le_of_ne hu_le_1 hu
  exact quantile_mem_Icc_of_supportsOn_Icc h ⟨hu_pos, hu_lt⟩

/-- The quantile function of `μ` is a.e.-measurable on each bin, with no support assumption. -/
private lemma aemeasurable_quantile_bin (μ : ProbDist ℝ) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    AEMeasurable (MeasureTheory.Measure.quantile μ.toMeasure)
      ((MeasureTheory.volume : Measure ℝ).restrict
        (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) := by
  obtain ⟨h0, h1, _⟩ := bin_endpoints hn k
  have h_bin_sub_Ioo : Set.Ioo ((k : ℝ) / n) (((k : ℝ) + 1) / n) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    refine ⟨lt_of_le_of_lt h0 hu.1, lt_of_lt_of_le hu.2 h1⟩
  have hmono_bin : MonotoneOn (MeasureTheory.Measure.quantile μ.toMeasure)
      (Set.Ioo ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :=
    MeasureTheory.Measure.monotoneOn_quantile.mono h_bin_sub_Ioo
  have hmeas_Ioo :
      AEMeasurable (MeasureTheory.Measure.quantile μ.toMeasure)
        ((MeasureTheory.volume : Measure ℝ).restrict
          (Set.Ioo ((k : ℝ) / n) (((k : ℝ) + 1) / n))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmono_bin
  -- transfer Ioo → Ioc since they differ by the null left endpoint
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := (k : ℝ) / n) (b := ((k : ℝ) + 1) / n))]
  exact hmeas_Ioo

/-- The quantile function is integrable on each bin, given a bounded support. -/
lemma integrableOn_quantile_bin {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
  have hae := quantile_mem_Icc_ae_on_bin h hn k
  have h_ae_abs :
      ∀ᵐ u ∂(MeasureTheory.volume.restrict
          (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))),
        ‖MeasureTheory.Measure.quantile μ.toMeasure u‖ ≤ max |a| |b| := by
    filter_upwards [hae] with u hu
    rw [Real.norm_eq_abs]
    obtain ⟨hl, hr⟩ := hu
    rcases le_or_gt 0 (MeasureTheory.Measure.quantile μ.toMeasure u) with hnn | hneg
    · rw [abs_of_nonneg hnn]
      exact le_max_of_le_right (hr.trans (le_abs_self b))
    · rw [abs_of_neg hneg]
      have hneg' : -MeasureTheory.Measure.quantile μ.toMeasure u ≤ -a := by linarith
      exact le_max_of_le_left (hneg'.trans (neg_le_abs _))
  have hmeas_Ioc := aemeasurable_quantile_bin μ hn k
  have hbin_finite :
      (MeasureTheory.volume : Measure ℝ)
          (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; simp
  refine MeasureTheory.Integrable.mono (g := fun _ : ℝ => max |a| |b|)
    (MeasureTheory.integrableOn_const (hs := hbin_finite)) hmeas_Ioc.aestronglyMeasurable ?_
  filter_upwards [h_ae_abs] with u hu
  have h_norm_max : ‖(max |a| |b| : ℝ)‖ = max |a| |b| := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
  rw [h_norm_max]
  exact hu

/-- If `μ` is supported on `Icc a b`, then each conditional-mean atom lies in `Icc a b`. -/
lemma condMeanAtom_mem_Icc {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) (n : ℕ) (hn : 0 < n) (k : Fin n) :
    condMeanAtom μ n hn k ∈ Icc a b := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  have hae := quantile_mem_Icc_ae_on_bin h hn k
  have hint := integrableOn_quantile_bin h hn k
  have hbin_finite :
      (MeasureTheory.volume : Measure ℝ)
          (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; simp
  have h_int_a : IntegrableOn (fun _ : ℝ => a)
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :=
    MeasureTheory.integrableOn_const (hs := hbin_finite)
  have h_int_b : IntegrableOn (fun _ : ℝ => b)
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :=
    MeasureTheory.integrableOn_const (hs := hbin_finite)
  -- Lower bound on the integral.
  have h_le_a :
      a * (1 / n) ≤ ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := by
    have h1' : ∫ _ in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n), (a : ℝ) ≤
        ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure u := by
      apply MeasureTheory.integral_mono_ae h_int_a hint
      filter_upwards [hae] with u hu using hu.1
    have h_const : ∫ _ in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n), (a : ℝ) = a * (1 / n) := by
      rw [MeasureTheory.setIntegral_const, volume_real_bin hn k, smul_eq_mul]
      ring
    linarith [h_const ▸ h1']
  -- Upper bound on the integral.
  have h_le_b :
      ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u ≤ b * (1 / n) := by
    have h1' : ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          MeasureTheory.Measure.quantile μ.toMeasure u ≤
        ∫ _ in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n), (b : ℝ) := by
      apply MeasureTheory.integral_mono_ae hint h_int_b
      filter_upwards [hae] with u hu using hu.2
    have h_const : ∫ _ in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n), (b : ℝ) = b * (1 / n) := by
      rw [MeasureTheory.setIntegral_const, volume_real_bin hn k, smul_eq_mul]
      ring
    linarith [h_const ▸ h1']
  unfold condMeanAtom
  refine ⟨?_, ?_⟩
  · have hmul : (n : ℝ) * (a * (1 / n)) ≤
        (n : ℝ) * ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u :=
      mul_le_mul_of_nonneg_left h_le_a hn_pos_R.le
    have hsimp : (n : ℝ) * (a * (1 / n)) = a := by field_simp
    linarith
  · have hmul : (n : ℝ) * ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u ≤
        (n : ℝ) * (b * (1 / n)) :=
      mul_le_mul_of_nonneg_left h_le_b hn_pos_R.le
    have hsimp : (n : ℝ) * (b * (1 / n)) = b := by field_simp
    linarith

/-- Conditional-mean atoms are monotone non-decreasing in the bin index. Requires boundedness of
`μ`'s support for integrability on each bin. -/
lemma condMeanAtom_monotone {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) {n : ℕ} (hn : 0 < n) :
    Monotone (fun k : Fin n => condMeanAtom μ n hn k) := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  intro i j hij
  by_cases heq : i = j
  · rw [heq]
  have hlt : i < j := lt_of_le_of_ne hij heq
  -- Key facts: i.val + 1 ≤ j.val, so (i+1)/n ≤ j/n.
  -- Also j < n so j/n < 1, and i+1 ≤ j < n so (i+1)/n < 1.
  have hij_lt : (i : ℕ) < (j : ℕ) := hlt
  have hij_succ_le : (i : ℕ) + 1 ≤ (j : ℕ) := hij_lt
  have h_ij_R : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij_succ_le
  -- i+1 < n.
  have h_i_succ_lt : (i : ℕ) + 1 < n := lt_of_le_of_lt hij_succ_le j.isLt
  -- Set r = (i+1)/n.
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
  -- Set s = j/n.
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
  -- q_μ is monotone on Ioo, so q_μ(r) ≤ q_μ(s).
  have hq_rs : MeasureTheory.Measure.quantile μ.toMeasure r ≤
      MeasureTheory.Measure.quantile μ.toMeasure s :=
    MeasureTheory.Measure.monotoneOn_quantile hr_mem hs_mem hrs
  -- `condMeanAtom μ n hn i ≤ q_μ(r)`: the integral of `q_μ` on `bin_i` is `≤ q_μ(r) · (1/n)` by
  -- monotonicity, since every `u` in `bin_i` satisfies `0 < u < r ≤ 1`.
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
  have h_int_i := integrableOn_quantile_bin h hn i
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
  -- `q_μ(s) ≤ condMeanAtom μ n hn j` by the symmetric argument at the left endpoint.
  have h_bin_j_ae_le :
      ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc s (((j : ℝ) + 1) / n))),
        MeasureTheory.Measure.quantile μ.toMeasure s ≤
          MeasureTheory.Measure.quantile μ.toMeasure u := by
    have h_ae_ne : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ 1 :=
      MeasureTheory.Measure.ae_ne _ 1
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h_ae_ne] with u hu_ne hu_bin
    -- u ∈ Ioc s ((j+1)/n). So u > s and u ≤ (j+1)/n ≤ 1.
    have hu_pos : 0 < u := lt_trans hs_pos hu_bin.1
    have hu_le1 : u ≤ 1 := hu_bin.2.trans h1_j
    have hu_lt1 : u < 1 := lt_of_le_of_ne hu_le1 hu_ne
    exact MeasureTheory.Measure.monotoneOn_quantile
      hs_mem ⟨hu_pos, hu_lt1⟩ hu_bin.1.le
  have h_int_j := integrableOn_quantile_bin h hn j
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
  -- Chain: f i ≤ q_μ(r) ≤ q_μ(s) ≤ f j.
  exact h_atom_i_le.trans (hq_rs.trans h_atom_j_ge)

/-- The mean of `condMeanAtomize μ n` equals the mean of `μ`, whenever `id` is integrable against
`μ` (e.g., `μ` supported on a bounded interval). -/
lemma condMeanAtomize_mean_eq {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) (n : ℕ) (hn : 0 < n) :
    (condMeanAtomize μ n hn).mean = μ.expect id := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  rw [condMeanAtomize, DiscreteLaw.uniform_mean]
  have h_atom : ∀ k : Fin n, condMeanAtom μ n hn k =
      (n : ℝ) * ∫ u in Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := fun _ => rfl
  simp_rw [h_atom]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hn_ne]
  -- Express μ.expect id as ∫_{Ioo 0 1} q_μ via integral_eq_integral_quantile.
  have h_expect_eq : μ.expect id =
      ∫ u in Set.Ioo (0 : ℝ) 1, MeasureTheory.Measure.quantile μ.toMeasure u := by
    unfold ProbDist.expect
    have : ∫ x, (id x : ℝ) ∂μ.toMeasure =
        ∫ u in Set.Ioo (0 : ℝ) 1, (id : ℝ → ℝ) (MeasureTheory.Measure.quantile μ.toMeasure u) :=
      MeasureTheory.Measure.integral_eq_integral_quantile (id : ℝ → ℝ)
        (measurable_id).aestronglyMeasurable
    simpa using this
  rw [h_expect_eq]
  -- Integrability of quantile on Ioo 0 1, transported from Integrable id μ.
  have h_map_eq : MeasureTheory.Measure.map (MeasureTheory.Measure.quantile μ.toMeasure)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) = μ.toMeasure :=
    MeasureTheory.Measure.map_quantile_volume_Ioo
  have h_aemeas : AEMeasurable (MeasureTheory.Measure.quantile μ.toMeasure)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) :=
    MeasureTheory.Measure.aemeasurable_quantile_restrict_Ioo
  have h_int_quantile : MeasureTheory.IntegrableOn
      (MeasureTheory.Measure.quantile μ.toMeasure) (Set.Ioo (0 : ℝ) 1) := by
    rw [MeasureTheory.IntegrableOn]
    have h_iff := MeasureTheory.integrable_map_measure (g := (id : ℝ → ℝ))
      (f := MeasureTheory.Measure.quantile μ.toMeasure)
      (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))
      (by rw [h_map_eq]; exact measurable_id.aestronglyMeasurable)
      h_aemeas
    rw [h_map_eq] at h_iff
    exact h_iff.mp hμ
  -- Union identity for `Ioc` bins: `⋃_k Ioc (k/n) ((k+1)/n) = Ioc 0 1`.
  have h_union_Ioc :
      ⋃ k : Fin n, Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n) = Set.Ioc (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨k, hu_lo, hu_hi⟩
      obtain ⟨h0, h1, _⟩ := bin_endpoints hn k
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_lt h0 hu_lo
      · exact hu_hi.trans h1
    · rintro ⟨hu_lo, hu_hi⟩
      -- Take k = ⌈n·u⌉ - 1.
      set y : ℝ := (n : ℝ) * u with hy_def
      have hy_pos : 0 < y := mul_pos hn_pos_R hu_lo
      have hy_le : y ≤ n := by
        rw [hy_def]
        calc (n : ℝ) * u ≤ (n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hu_hi hn_pos_R.le
          _ = n := mul_one _
      set m : ℕ := ⌈y⌉₊ with hm_def
      have hm_pos : 1 ≤ m := by
        rw [hm_def, Nat.one_le_ceil_iff]; exact hy_pos
      have hm_le_n : m ≤ n := by
        rw [hm_def, Nat.ceil_le]; exact_mod_cast hy_le
      have h_i_val : m - 1 < n := by omega
      refine ⟨⟨m - 1, h_i_val⟩, ?_, ?_⟩
      · -- (m-1)/n < u ⟺ m-1 < y.
        change (((m - 1 : ℕ) : ℝ)) / n < u
        have h_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_pred (by omega : 0 < m)]
        rw [h_cast, div_lt_iff₀ hn_pos_R]
        have h_ceil_lt : (m : ℝ) - 1 < y := by
          rw [hm_def]
          have := Nat.ceil_lt_add_one hy_pos.le
          linarith
        linarith [mul_comm u (n : ℝ)]
      · change u ≤ (((m - 1 : ℕ) : ℝ) + 1) / n
        have h_cast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
          rw [Nat.cast_pred (by omega : 0 < m)]; ring
        rw [h_cast, le_div_iff₀ hn_pos_R]
        have : y ≤ m := Nat.le_ceil _
        linarith [mul_comm u (n : ℝ)]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← h_union_Ioc]
  have h_disj :
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise
        (Function.onFun Disjoint
          (fun k : Fin n => Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) :=
    (bins_pairwise_disjoint_Ioc hn).mono (Set.subset_univ _)
  have h_meas : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      MeasurableSet (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :=
    fun i _ => measurableSet_Ioc
  have h_int_Ioc : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      MeasureTheory.IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
        (Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    intro i _
    -- The whole quantile is IntegrableOn Ioo 0 1, hence IntegrableOn on a subset.
    -- But bin_i might not be contained in Ioo 0 1 strictly (its right endpoint could be 1).
    -- Use IntegrableOn.mono and Ioc ⊆ Ioc 0 1 = (Ioo 0 1) a.e.
    -- Actually simpler: apply aemeasurable_quantile_bin to get AEMeasurability on the bin.
    -- And bound using IntegrableOn of constant? No, we don't have a bound.
    -- Use: IntegrableOn q (Ioo 0 1) → IntegrableOn q (Ioo 0 1 ∪ {0, 1}) → IntegrableOn q (Icc 0 1)
    -- → IntegrableOn q on any subset of Icc 0 1 (finite measure).
    have h_Icc01 : MeasureTheory.IntegrableOn
        (MeasureTheory.Measure.quantile μ.toMeasure) (Set.Icc (0 : ℝ) 1) := by
      rw [MeasureTheory.IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1))]
      exact h_int_quantile
    -- bin_i ⊆ Icc 0 1.
    have h_sub : Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro u hu
      obtain ⟨h0, h1, _⟩ := bin_endpoints hn i
      refine ⟨(le_of_lt (lt_of_le_of_lt h0 hu.1)), hu.2.trans h1⟩
    exact h_Icc01.mono_set h_sub
  -- Apply integral_biUnion_finset.
  rw [show (⋃ k : Fin n, Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))
      = ⋃ k ∈ (Finset.univ : Finset (Fin n)), Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n) by
      simp]
  rw [← MeasureTheory.integral_biUnion_finset (t := Finset.univ) h_meas h_disj h_int_Ioc]

/-- Partial sum of conditional-mean atoms up to index `K` equals `n · ∫_{(0, (K+1)/n]} q_μ`. This
requires boundedness of `μ`'s support so that the quantile is integrable on each bin. -/
lemma condMeanAtomize_partial_sum_eq {a b : ℝ} {μ : ProbDist ℝ}
    (h : μ.supportsOn (Icc a b)) {n : ℕ} (hn : 0 < n) (K : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val),
        condMeanAtom μ n hn i) =
      (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := by
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  -- Each atom is n · ∫_{bin_i} q.
  have h_atom : ∀ i : Fin n, condMeanAtom μ n hn i =
      (n : ℝ) * ∫ u in Set.Ioc ((i : ℝ) / n) (((i : ℝ) + 1) / n),
        MeasureTheory.Measure.quantile μ.toMeasure u := fun _ => rfl
  simp_rw [h_atom]
  rw [← Finset.mul_sum]
  congr 1
  -- Goal: ∑ i ∈ filter ..., ∫_{bin_i} q = ∫_{Ioc 0 ((K+1)/n)} q.
  -- Union identity: ⋃ i ∈ filter, Ioc (i/n) ((i+1)/n) = Ioc 0 ((K+1)/n).
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
  -- Disjointness.
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
    integrableOn_quantile_bin h hn i
  rw [← h_union,
    MeasureTheory.integral_biUnion_finset
      (t := Finset.univ.filter (fun i : Fin n => i.val ≤ K.val))
      h_meas h_disj h_int]

end DiscreteLaw
end Econlib.Probability

end
end
