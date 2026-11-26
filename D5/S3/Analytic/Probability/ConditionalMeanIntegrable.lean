/- GID: D5/S3/Analytic/Probability/ConditionalMeanIntegrable
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/ConditionalMeanIntegrable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrable quantile-bin means and convex order for real laws. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Probability.ConditionalMeanApproximation

/-! Finite laws formed by averaging integrable real quantiles over equally spaced bins. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

noncomputable section

namespace Econlib.Probability

/-- Stop-loss comparison orders the upper integrated quantiles of integrable real laws. -/
theorem upperIntegratedQuantile_le_of_stopLoss_le {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ u in Ioc t 1, Measure.quantile μ.toMeasure u) ≤
      ∫ u in Ioc t 1, Measure.quantile ν.toMeasure u := by
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · subst t
    simp
  · have hbound := Measure.upperIntegratedQuantile_le_stopLoss_add hμ ⟨ht.1.le, ht.2⟩
      (Measure.quantile ν.toMeasure t)
    have hcompare := hstop (Measure.quantile ν.toMeasure t)
    have heq := Measure.upperIntegratedQuantile_eq_stopLoss_add hν ⟨ht.1, hlt⟩
    linarith

/-- An upper integrated-quantile inequality reverses on the complementary lower interval
when the two integrable laws have equal means. -/
theorem lowerIntegratedQuantile_ge_of_upper_le {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (hupper : (∫ u in Ioc t 1, Measure.quantile μ.toMeasure u) ≤
      ∫ u in Ioc t 1, Measure.quantile ν.toMeasure u) :
    (∫ u in Ioc 0 t, Measure.quantile ν.toMeasure u) ≤
      ∫ u in Ioc 0 t, Measure.quantile μ.toMeasure u := by
  have hμsplit := Measure.integral_quantile_Ioo_split hμ ht.1 ht.2
  have hνsplit := Measure.integral_quantile_Ioo_split hν ht.1 ht.2
  have hμmean : μ.expect id = ∫ u in Ioo (0 : ℝ) 1, Measure.quantile μ.toMeasure u :=
    Measure.integral_eq_integral_quantile (fun x : ℝ => x) aestronglyMeasurable_id
  have hνmean : ν.expect id = ∫ u in Ioo (0 : ℝ) 1, Measure.quantile ν.toMeasure u :=
    Measure.integral_eq_integral_quantile (fun x : ℝ => x) aestronglyMeasurable_id
  linarith

namespace DiscreteLaw

open MeasureTheory.Measure (integrable_quantile_Ioc)

lemma integrableOn_quantile_bin_of_integrable {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n) (k : Fin n) :
    IntegrableOn (Measure.quantile μ.toMeasure)
      (Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
  obtain ⟨h0, h1, _⟩ := bin_endpoints hn k
  exact (integrable_quantile_Ioc hμ (le_refl (0 : ℝ))).mono_set
    (fun _ hu => ⟨lt_of_le_of_lt h0 hu.1, hu.2.trans h1⟩)

lemma condMeanAtom_monotone_of_integrable_bins {μ : ProbDist ℝ} {n : ℕ} (hn : 0 < n)
    (hBin : ∀ k : Fin n, MeasureTheory.IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) :
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
  have h_int_i := hBin i
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
  have h_int_j := hBin j
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

lemma condMeanAtomize_partial_sum_eq_of_integrable_bins {μ : ProbDist ℝ} {n : ℕ} (hn : 0 < n)
    (hBin : ∀ k : Fin n, MeasureTheory.IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      (Set.Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) (K : Fin n) :
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
    hBin i
  rw [← h_union,
    MeasureTheory.integral_biUnion_finset
      (t := Finset.univ.filter (fun i : Fin n => i.val ≤ K.val))
      h_meas h_disj h_int]

private lemma tendsto_condMeanAtom_of_continuousWithinAt_of_integrable_bins
    {μ : ProbDist ℝ}
    (hBin : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n),
      IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
        (Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
      (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => if h : binIndex (n + 1) t < (n + 1) then
        DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨binIndex (n + 1) t, h⟩
      else DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩)
      atTop (𝓝 (MeasureTheory.Measure.quantile μ.toMeasure t)) := by
  -- Eventually binIndex (n+1) t < n+1, so the conditional branch taken is the first.
  have h_idx_lt : ∀ᶠ n in atTop, binIndex (n + 1) t < n + 1 := by
    filter_upwards with n
    exact binIndex_lt (Nat.succ_le_succ (Nat.zero_le n)) ht
  -- Reduce to showing `condMeanAtom μ (n+1) _ ⟨binIndex (n+1) t, _⟩ → quantile μ t`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- Use continuity of `quantile` within `Ioo 0 1` at `t`.
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at h_qcts
  obtain ⟨δ, hδ_pos, hδ⟩ := h_qcts (ε / 2) hε2
  -- Eventually 1/(n+1) < δ and bin is inside Ioo 0 1.
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  -- Choose N large enough that 1/(N+1) < δ and bin fits in Ioo 0 1.
  -- The bin containing `t` has width 1/(n+1) and contains `t`, so its endpoints are within
  -- 1/(n+1) of t. Need 1/(n+1) < δ AND the left endpoint > 0 AND the right endpoint < 1.
  obtain ⟨N1, hN1⟩ := exists_nat_gt (1 / t)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / (1 - t))
  have ht_pos : 0 < t := ht.1
  have ht_sub_pos : 0 < 1 - t := by linarith [ht.2]
  set N := max (max (max N0 N1) N2) 1 with hN_def
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn_succ_ge_1 : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
  -- 1/(n+1) < δ.
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
  -- Analogous: bin's left endpoint > 0.
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
  -- Bin endpoints.
  obtain ⟨hL_le, hR_lt, _⟩ := bin_of_binIndex_bounds hn_succ_ge_1 ht
  set k_nat : ℕ := binIndex (n + 1) t with hk_def
  have hk_lt : k_nat < n + 1 := binIndex_lt hn_succ_ge_1 ht
  -- `k_nat/(n+1) ≤ t < (k_nat+1)/(n+1)`, width `1/(n+1)`. We bound `|condMeanAtom - q_μ(t)|` by the
  -- bin-average of `|q_μ(u) - q_μ(t)|`, using `u ∈ Ioo 0 1` a.e. on the bin and continuity of
  -- `q_μ`.
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
  -- Now: t - 1/(n+1) > 0 and t + 1/(n+1) < 1.
  -- Bounds on bin endpoints.
  -- Left endpoint: k_nat/(n+1) ≥ t - 1/(n+1) (since t < (k_nat+1)/(n+1) implies
  -- (n+1) t < k_nat + 1 implies k_nat > (n+1)t - 1 implies k_nat / (n+1) > t - 1/(n+1)).
  have h_left_ge : t - 1 / ((n + 1 : ℕ) : ℝ) ≤ (k_nat : ℝ) / (n + 1 : ℕ) := by
    have h_np1_t : ((n + 1 : ℕ) : ℝ) * t < (k_nat : ℝ) + 1 := by
      rw [lt_div_iff₀ h_np1_R_pos] at hR_lt; linarith
    have h_t_lt : t < ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ h_np1_R_pos]; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [add_div]
    linarith
  -- Right endpoint: (k_nat+1)/(n+1) ≤ t + 1/(n+1).
  have h_right_le : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := by
    have hk_le_nt : (k_nat : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * t := by
      rw [div_le_iff₀ h_np1_R_pos] at hL_le; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by rw [add_div]
    rw [this]
    have hk_le_t : (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ t := hL_le
    linarith
  -- So bin ⊆ Ioo 0 1 (using h_left_ge: left endpoint ≥ t - 1/(n+1) > 0; h_right_le: right
  -- endpoint ≤ t + 1/(n+1) < 1).
  have h_L_pos : 0 < (k_nat : ℝ) / (n + 1 : ℕ) := by
    have : t - 1 / ((n + 1 : ℕ) : ℝ) > 0 := by linarith
    linarith
  have h_R_lt_1 : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) < 1 := by
    have : t + 1 / ((n + 1 : ℕ) : ℝ) < 1 := by linarith
    linarith
  -- Now evaluate the dif.
  rw [dif_pos hk_lt]
  -- Goal: dist (condMeanAtom μ (n+1) _ ⟨k_nat, hk_lt⟩) (quantile μ t) < ε.
  -- Unfold condMeanAtom: (n+1) · ∫_{Ioc (k_nat/(n+1)) ((k_nat+1)/(n+1))} quantile μ u du.
  unfold DiscreteLaw.condMeanAtom
  -- Express quantile μ t = (n+1) · ∫_{bin} quantile μ t du (constant * volume 1/(n+1)).
  set bin : Set ℝ := Set.Ioc ((k_nat : ℝ) / (n + 1 : ℕ))
    (((k_nat : ℝ) + 1) / (n + 1 : ℕ)) with hbin_def
  have h_bin_subset_Ioo : bin ⊆ Ioo (0 : ℝ) 1 := by
    rw [hbin_def]
    intro u hu
    refine ⟨lt_of_lt_of_le h_L_pos hu.1.le, lt_of_le_of_lt hu.2 h_R_lt_1⟩
  -- Volume of bin is 1/(n+1).
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
  -- Integrability of quantile on bin (using bounded support).
  have h_int_quantile : IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      bin := by
    rw [hbin_def]
    exact hBin (n + 1) (Nat.succ_pos n) ⟨k_nat, hk_lt⟩
  have h_int_const : IntegrableOn (fun _ : ℝ => MeasureTheory.Measure.quantile μ.toMeasure t)
      bin volume := integrableOn_const hbin_vol
  -- Integrand bound on bin: for u ∈ bin, |quantile μ u - quantile μ t| < ε.
  -- First, u ∈ Ioo 0 1 (above). Second, |u - t| ≤ 1/(n+1) < δ.
  have h_bin_ae_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict bin),
      |MeasureTheory.Measure.quantile μ.toMeasure u
        - MeasureTheory.Measure.quantile μ.toMeasure t| < ε / 2 := by
    rw [MeasureTheory.ae_restrict_iff' hbin_meas]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_Ioo : u ∈ Ioo (0 : ℝ) 1 := h_bin_subset_Ioo hu
    -- |u - t| < δ.
    rw [hbin_def] at hu
    have hu_dist : dist u t < δ := by
      rw [Real.dist_eq]
      rcases le_or_gt u t with hle | hgt
      · -- u ≤ t: |u - t| = t - u. u > k_nat/(n+1) ≥ t - 1/(n+1), so t - u < 1/(n+1) < δ.
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        have : u > t - 1 / ((n + 1 : ℕ) : ℝ) := lt_of_le_of_lt h_left_ge hu.1
        linarith
      · -- u > t: |u - t| = u - t. u ≤ (k_nat+1)/(n+1) ≤ t + 1/(n+1), so u - t ≤ 1/(n+1) < δ.
        rw [abs_of_pos (sub_pos.mpr hgt)]
        have : u ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := le_trans hu.2 h_right_le
        linarith
    have h_diff : dist (MeasureTheory.Measure.quantile μ.toMeasure u)
        (MeasureTheory.Measure.quantile μ.toMeasure t) < ε / 2 :=
      hδ hu_Ioo hu_dist
    rw [Real.dist_eq] at h_diff
    exact h_diff
  -- Integrate pointwise bound.
  -- We write:
  --   condMeanAtom - q(t) = (n+1) * ∫_{bin} q(u) - q(t) du = (n+1) * (∫_{bin} q u du - q(t)/(n+1))
  -- and |above| ≤ (n+1) * ∫_{bin} |q(u) - q(t)| du ≤ (n+1) * ε * (1/(n+1)) = ε.
  -- In practice, use ∫_{bin} q(u) - q(t) du = ∫_{bin} q(u) du - q(t) * vol(bin).
  have h_diff_int :
      (∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u)
      - (MeasureTheory.Measure.quantile μ.toMeasure t) * (1 / ((n + 1 : ℕ) : ℝ))
      = ∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t) := by
    rw [integral_sub h_int_quantile h_int_const]
    rw [MeasureTheory.setIntegral_const]
    rw [hbin_vol_real, smul_eq_mul]
    ring
  -- Bound ∫|diff| ≤ ε * vol(bin).
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
  -- Combine.
  rw [Real.dist_eq]
  -- Rewrite LHS as (n+1) * (∫ q(u) - q(t)/(n+1)) = (n+1) * ∫ (q(u) - q(t)).
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

/-- At a continuity point `t ∈ Ioo 0 1` of `quantile μ` (within `Ioo 0 1`),
`condStepFun μ φ (n+1) _ t → φ(quantile μ t)`. -/

private lemma tendsto_condStepFun_of_atom_tendsto
    {μ : ProbDist ℝ}
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    {t : ℝ}
    (h_atom : Tendsto (fun n : ℕ => if h : binIndex (n + 1) t < (n + 1) then
        DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨binIndex (n + 1) t, h⟩
      else DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩)
      atTop (𝓝 (MeasureTheory.Measure.quantile μ.toMeasure t))) :
    Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
      (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t))) := by
  have h_cts := (hφ.tendsto _).comp h_atom
  -- condStepFun is the if-dif around the atom; h_atom already matches this shape.
  convert h_cts using 1
  funext n
  unfold condStepFun
  simp only [Function.comp_apply]
  split_ifs with h1 <;> rfl

private lemma condStepFun_tendsto_ae_of_pointwise
    {μ : ProbDist ℝ}
    {φ : ℝ → ℝ}
    (hPointwise : ∀ t ∈ Ioo (0 : ℝ) 1,
      ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
        (Ioo (0 : ℝ) 1) t →
      Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
        (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t)))) :
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
  simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
  obtain ⟨h_t_in, h_no_conv⟩ := ht
  refine ⟨h_t_in, ?_⟩
  intro h_cts
  exact h_no_conv (hPointwise t h_t_in h_cts)

private lemma condMeanAtomize_tendsto_of_ae {μ : ProbDist ℝ}
    (hAe : ∀ {φ : ℝ → ℝ}, Continuous φ →
      ∀ᵐ t ∂((MeasureTheory.volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
        Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
          (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t)))) :
    Filter.Tendsto (fun n : ℕ =>
      ((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        : MeasureTheory.ProbabilityMeasure ℝ))
      Filter.atTop (nhds μ) := by
  -- Use weak convergence characterization: it suffices to test against BC functions.
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φBC
  set φ : ℝ → ℝ := fun x => φBC x with hφ_def
  have hφ_cts : Continuous φ := φBC.continuous
  set M : ℝ := ‖φBC‖ with hM_def
  have hM : ∀ x, |φ x| ≤ M := fun x => by
    rw [hM_def]
    have := φBC.norm_coe_le_norm x
    simpa [Real.norm_eq_abs] using this
  -- The LHS equals `(1/(n+1)) * ∑_k φ(condMeanAtom μ (n+1) _ k) = ∫_{Ioo 0 1} condStepFun`.
  have h_lhs_eq : (fun n : ℕ => ∫ x, φBC x
      ∂((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure))
      = fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, condStepFun μ φ (n + 1) (Nat.succ_pos n) t := by
    funext n
    rw [integral_condStepFun_Ioo hφ_cts (Nat.succ_pos n)]
    rw [integral_toProbDist_condMeanAtomize hφ_cts (Nat.succ_pos n)]
  rw [h_lhs_eq]
  -- The RHS equals `∫_{Ioo 0 1} φ ∘ quantile μ`.
  have h_rhs : ∫ x, φBC x ∂μ.toMeasure
      = ∫ t in Ioo (0 : ℝ) 1, φ (MeasureTheory.Measure.quantile μ.toMeasure t) :=
    MeasureTheory.Measure.integral_eq_integral_quantile φ hφ_cts.aestronglyMeasurable
  change Filter.Tendsto _ Filter.atTop (nhds (∫ x, φBC x ∂μ.toMeasure))
  rw [h_rhs]
  -- Conclude by dominated convergence.
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
  · exact hAe hφ_cts

/-- Conditional-mean atomizations converge weakly when the quantile is integrable on every bin. -/
theorem condMeanAtomize_tendsto_of_integrable_bins {μ : ProbDist ℝ}
    (hBin : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n),
      IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
        (Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n))) :
    Filter.Tendsto (fun n : ℕ =>
      ((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        : MeasureTheory.ProbabilityMeasure ℝ))
      Filter.atTop (nhds μ) :=
  condMeanAtomize_tendsto_of_ae fun hφ =>
    condStepFun_tendsto_ae_of_pointwise fun _ ht hcts =>
      tendsto_condStepFun_of_atom_tendsto hφ (tendsto_condMeanAtom_of_continuousWithinAt_of_integrable_bins hBin ht hcts)

/-- Ordered lower quantile integrals and equal means give convex order of the uniform
finite laws formed from integrable quantile bins. -/
theorem condMeanAtomize_convexOrder_of_lowerIntegratedQuantile {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id) (n : ℕ) (hn : 0 < n)
    (hlower : ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) 1 →
      (∫ u in Ioc 0 t, Measure.quantile ν.toMeasure u) ≤
        ∫ u in Ioc 0 t, Measure.quantile μ.toMeasure u) :
    DiscreteLaw.ConvexOrder (condMeanAtomize μ n hn) (condMeanAtomize ν n hn) := by
  intro φ hφ
  have hμBin := integrableOn_quantile_bin_of_integrable hμ hn
  have hνBin := integrableOn_quantile_bin_of_integrable hν hn
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  -- Reduce weighted sum to unweighted sum by factoring out the uniform weight 1/n.
  simp only [condMeanAtomize, uniform]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Use monotonicity of scaling by 1/n ≥ 0.
  have hn_inv_nonneg : (0 : ℝ) ≤ 1 / n := by positivity
  apply mul_le_mul_of_nonneg_left _ hn_inv_nonneg
  -- Reduce `∑ φ(condMeanAtom μ) ≤ ∑ φ(condMeanAtom ν)` to `sum_convex_le_of_partial_sum_ge`, whose
  -- hypotheses are monotone atoms, equal total sums, and a partial-sum comparison.
  set x : Fin n → ℝ := fun k => condMeanAtom μ n hn k with hx_def
  set y : Fin n → ℝ := fun k => condMeanAtom ν n hn k with hy_def
  have hx_mono : Monotone x := condMeanAtom_monotone_of_integrable_bins hn hμBin
  have hy_mono : Monotone y := condMeanAtom_monotone_of_integrable_bins hn hνBin
  -- Equal total sums: ∑ x = n · μ.expect id = n · ν.expect id = ∑ y.
  have hμ_mean : (condMeanAtomize μ n hn).mean = μ.expect id :=
    condMeanAtomize_mean_eq hμ n hn
  have hν_mean : (condMeanAtomize ν n hn).mean = ν.expect id :=
    condMeanAtomize_mean_eq hν n hn
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
  -- Partial-sum comparison: `∑_{i ≤ K} y i ≤ ∑_{i ≤ K} x i`.
  have hpart : ∀ K : Fin n,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) := by
    intro K
    have h_partial_μ :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u := by
      simpa [hx_def] using condMeanAtomize_partial_sum_eq_of_integrable_bins hn hμBin K
    have h_partial_ν :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u := by
      simpa [hy_def] using condMeanAtomize_partial_sum_eq_of_integrable_bins hn hνBin K
    rw [h_partial_μ, h_partial_ν]
    -- Bound t = (K.val + 1)/n in (0, 1].
    have ht_pos : (0 : ℝ) < ((K.val + 1 : ℝ) / n) := by
      apply div_pos _ hn_pos_R
      have : (0 : ℕ) < K.val + 1 := Nat.succ_pos _
      exact_mod_cast this
    have ht_le_1 : ((K.val + 1 : ℝ) / n) ≤ 1 := by
      rw [div_le_one hn_pos_R]
      have hKlt : K.val + 1 ≤ n := K.isLt
      exact_mod_cast hKlt
    -- The lower integrated quantile of `ν` is dominated by that of `μ` under the convex order.
    have h_ineq :
        (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u) ≤
          (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u) :=
      hlower ⟨ht_pos, ht_le_1⟩
    exact mul_le_mul_of_nonneg_left h_ineq hn_pos_R.le
  exact sum_convex_le_of_partial_sum_ge x y hx_mono hy_mono hsum hpart hφ

end DiscreteLaw
end Econlib.Probability
