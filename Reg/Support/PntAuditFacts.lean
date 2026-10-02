import D5.S3.Weil.PrimeNumberTheorem.MediumPNT

namespace Reg.Support.PntAuditFacts

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff

noncomputable section

theorem normalized_smooth_kernel_Ici :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have hBump : ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc 1 (3 / 2)) 1 ≤ Ψ ∧
      Ψ ≤ Set.indicator (Set.Ioo (1 / 2) 2) 1 ∧
      (Function.support Ψ = Set.Ioo (1 / 2) 2) := by
    have hUrysohn := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
      (modelWithCornersSelf ℝ ℝ)
      (s := Set.Iic (1 / 2 : ℝ) ∪ Set.Ici 2)
      (t := Set.Icc 1 (3 / 2 : ℝ))
      (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
      (by
        simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
          Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
          and_imp, imp_false, not_le, Set.mem_Ici]
        constructor <;> intros <;> linarith)
    obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := hUrysohn
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
    use Ψ
    simp only [range_subset_iff, mem_Icc] at hΨrange
    refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
    · apply HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (1 / 2 : ℝ) 2) isCompact_Icc
      simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
      bound
    · apply Set.indicator_le'
      · intro x hx
        rw [hΨ1 x |>.mp, Pi.one_apply]
        simpa using hx
      · exact fun x _ ↦ (hΨrange x).1
    · intro x
      apply Set.le_indicator_apply
      · exact fun _ ↦ (hΨrange x).2
      · intro hx
        rw [← hΨ0 x |>.mp]
        simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
    · ext x
      simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := hBump
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · have hSupportId : Function.support (fun a : ℝ => a) = {0}ᶜ := by
        ext x
        simp
      simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, hSupportId]
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

theorem normalized_smooth_kernel :
    ∃ ν : ℝ → ℝ, ContDiff ℝ 1 ν ∧ (∀ x > 0, 0 ≤ ν x) ∧
      ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ioi 0, ν x / x = 1 := by
  obtain ⟨ν, hd, hn, hs, hm⟩ := normalized_smooth_kernel_Ici
  refine ⟨ν, hd.of_le (by simp), fun x _ => hn x, hs, ?_⟩
  rwa [← integral_Ici_eq_integral_Ioi]

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem smooth1_zero (ε x : ℝ) : Smooth1 (fun _ => 0) ε x = 0 := by
  simp [Smooth1, MellinConvolution, DeltaSpike]

theorem smooth1_distinct_values :
    ∃ ν : ℝ → ℝ, Smooth1 ν (1 / 4) (1 / 4) = 1 ∧
      Smooth1 ν (1 / 4) 5 = 0 := by
  obtain ⟨ν, _hd, _hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨c, _hc, hceq, below⟩ := Smooth1Properties_below hs hm
  obtain ⟨d, _hd, hdeq, above⟩ := Smooth1Properties_above hs
  have hc : c ≤ 1 := by rw [hceq]; exact log_two_le_one
  have hd : d ≤ 2 := by rw [hdeq]; linarith [log_two_le_one]
  refine ⟨ν, below (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by linarith),
    above (1 / 4) 5 (by constructor <;> norm_num) (by linarith)⟩

end
end Reg.Support.PntAuditFacts
