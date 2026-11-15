/- GID: D5/S3/Entropy/KolmogorovSinai/HistoryEnvelope
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/HistoryEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound stationary partition entropy rate by each finite-history conditional entropy. -/

import D5.S3.Entropy.KolmogorovSinai.GeneratorConditioning
import D5.S3.Entropy.ConditionalEntropy
import Mathlib.Analysis.SpecificLimits.Basic

/-! A stationary finite partition has nonincreasing finite-history conditional increments. -/

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α ι : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Fintype ι]
  {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

private noncomputable def historyIncrement (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n : ℕ) : ℝ :=
  condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT P n))
    (P.pullback (hT.iterate n)).cells

private theorem history_increment_antitone (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) : Antitone (historyIncrement hT P) := by
  apply antitone_nat_of_succ_le
  intro n
  have hle := comap_iterate_generatedSigmaAlgebra_ksJoin_le hT P 1 n
  rw [Nat.add_comm 1 n] at hle
  have hb := condEntropy_mono_of_le hle
    (generatedSigmaAlgebra_le (ksJoin hT P (n + 1)))
    (P.pullback (hT.iterate (n + 1)))
  have heq : (P.pullback (hT.iterate (n + 1))).cells =
      fun i => (T^[1]) ⁻¹' (P.pullback (hT.iterate n)).cells i := by
    funext i
    simp only [MeasurePartition.pullback_cells, ← Set.preimage_comp,
      ← Function.iterate_add]
  unfold historyIncrement
  refine hb.trans_eq ?_
  rw [heq]
  exact condEntropy_comap_pullback (generatedSigmaAlgebra_le (ksJoin hT P n))
    hT 1 (P.pullback (hT.iterate n))

private theorem history_increment_chain (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropySeq hT P (n + 1) = ksEntropySeq hT P n + historyIncrement hT P n := by
  let Q := P.pullback (hT.iterate n)
  have hcell : ∀ x : (Fin n → ι) × ι,
      (ksJoin hT P (n + 1)).cells ((Equiv.prodCongr (Equiv.refl _) 
        (Equiv.funUnique (Fin 1) ι).symm).trans (Fin.appendEquiv n 1) x) =
        joinCells (ksJoin hT P n).cells Q.cells x := by
    intro x
    change ksJoinCells P.cells T (n + 1)
      (Fin.append x.1 ((Equiv.funUnique (Fin 1) ι).symm x.2)) = _
    rw [ksJoinCells_append]
    congr 1
    change (T^[n]) ⁻¹' ksJoinCells P.cells T 1
      ((Equiv.funUnique (Fin 1) ι).symm x.2) = (T^[n]) ⁻¹' P.cells x.2
    congr 1
    ext z
    simp [ksJoinCells, Equiv.funUnique_symm_apply]
  have hj : ksEntropySeq hT P (n + 1) =
      entropy μ (joinCells (ksJoin hT P n).cells Q.cells) := by
    rw [ksEntropySeq, ← entropy_reindex μ
      ((Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique (Fin 1) ι).symm).trans
        (Fin.appendEquiv n 1))]
    congr 1
    exact funext hcell
  rw [hj, entropy_join_eq_add_condEntropyGivenPartition,
    condEntropyGivenPartition_eq_condEntropy_generated _ _ Q.measurable]
  rfl

private theorem history_linear_bound (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) (n m : ℕ) :
    ksEntropySeq hT P (n + m) ≤
      ksEntropySeq hT P n + (m : ℝ) * historyIncrement hT P n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by omega, history_increment_chain]
    have hc := history_increment_antitone hT P (Nat.le_add_right n m)
    push_cast
    nlinarith

/-- Every actual finite history bounds the stationary partition entropy rate, in nats. -/
theorem ksEntropyPartition_le_history_conditionalEntropy
    (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) (n : ℕ) :
    ksEntropyPartition hT P ≤
      D5.S3.Entropy.ConditionalEntropy.conditionalEntropy
        (fun x : (Fin n → ι) × ι =>
          μ.real ((ksJoin hT P n).cells x.1 ∩ (T^[n]) ⁻¹' P.cells x.2)) := by
  have hshift : Tendsto (fun m : ℕ => n + m) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hl := (tendsto_ksEntropySeq hT P).comp hshift
  have hr := ((tendsto_const_div_atTop_nhds_zero_nat
    (ksEntropySeq hT P n - (n : ℝ) * historyIncrement hT P n)).comp hshift).add_const
      (historyIncrement hT P n)
  have hbound : ksEntropyPartition hT P ≤ historyIncrement hT P n := by
    apply le_of_tendsto_of_tendsto hl (by simpa using hr)
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hpos : (0 : ℝ) < (n + m : ℕ) := by exact_mod_cast (show 0 < n + m by omega)
    have h := history_linear_bound hT P n m
    have heq : (ksEntropySeq hT P n + (m : ℝ) * historyIncrement hT P n) /
        (n + m : ℕ) =
        (ksEntropySeq hT P n - (n : ℝ) * historyIncrement hT P n) / (n + m : ℕ) +
          historyIncrement hT P n := by
      push_cast
      field_simp
      <;> ring
    simpa only [Function.comp_apply, Nat.cast_add] using
      (div_le_div_of_nonneg_right h hpos.le).trans_eq heq
  have hbridge := condEntropyGivenPartition_eq_condEntropy_generated
    (ksJoin hT P n) (P.pullback (hT.iterate n)).cells
    (P.pullback (hT.iterate n)).measurable
  rw [historyIncrement, ← hbridge] at hbound
  have hmass : ∀ a : Fin n → ι,
      D5.S3.Divergence.ChainRule.marginal
        (fun x : (Fin n → ι) × ι =>
          μ.real ((ksJoin hT P n).cells x.1 ∩ (T^[n]) ⁻¹' P.cells x.2)) a =
            μ.real ((ksJoin hT P n).cells a) := by
    intro a
    have hm := (P.pullback (hT.iterate n)).measure_eq_sum_inter
      ((ksJoin hT P n).measurable a)
    have hr := congrArg ENNReal.toReal hm
    simpa only [ENNReal.toReal_sum (fun i _ => measure_ne_top μ _),
      D5.S3.Divergence.ChainRule.marginal, MeasurePartition.pullback_cells,
      measureReal_def] using hr.symm
  convert hbound using 1
  simp only [D5.S3.Entropy.ConditionalEntropy.conditionalEntropy,
    D5.S3.Entropy.MaxEntropy.shannonEntropy, D5.S3.Divergence.ChainRule.conditional]
  simp_rw [hmass]
  rfl

end D5.S3.Entropy.KolmogorovSinai
