/- GID: D5/S3/Entropy/KolmogorovSinai/FairEquilibrium
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/FairEquilibrium
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov-Sinai fairequilibrium for the full-shift equilibrium proof. -/

/- Copyright (c) 2026 Marcel Morgenstern. Licensed under Apache-2.0.
   Selected source port of marcmorningstar/lean4-ergodic-theory,
   revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f.
   Attribution, source mapping and full license: Library/Entropy/morgenstern2026ks.md.
   Adaptation: current Lean APIs, subject namespaces and live-dependency pruning.
   Retire each ported declaration when an equivalent declaration exists in this
   repository's pinned mathlib revision, replacing consumers by direct imports. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.KolmogorovSinai.Bernoulli
import D5.S3.Entropy.LopesOliveiraFullTail

namespace D5.S3.Entropy.FairBernoulli
open MeasureTheory Filter Topology Set D5.S3.Entropy.KolmogorovSinai D5.S3.Entropy.BernoulliShift
noncomputable section
private abbrev X := ℕ → Bool
local instance : MetricSpace X := PiNat.metricSpace (E := fun _ => Bool)
private def fairSymbol : Measure Bool := (2 : ENNReal)⁻¹ • Measure.dirac false +
  (2 : ENNReal)⁻¹ • Measure.dirac true
@[instance] private theorem fairSymbol_probability : IsProbabilityMeasure fairSymbol := by
  constructor
  simp only [fairSymbol, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  simpa only [one_div] using ENNReal.add_halves 1
private lemma fairSymbol_mass (b : Bool) : fairSymbol {b} = (2 : ENNReal)⁻¹ := by
  cases b <;> simp [fairSymbol]
private def rawFair : Measure X := bern fairSymbol
@[instance] private theorem rawFair_probability : IsProbabilityMeasure rawFair :=
  inferInstanceAs (IsProbabilityMeasure (bern fairSymbol))
private lemma rawFairInvariant : MeasurePreserving shiftMap rawFair rawFair :=
  measurePreserving_shiftMap_bern fairSymbol
private lemma ks_eq_coord (rho : Measure X) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shiftMap rho rho) :
    ksEntropy hT = ((ksEntropyPartition hT (coordPartition rho) : ℝ) : EReal) := by
  have hgen : IsGenerating rho shiftMap (coordPartitionFin rho) := by
    unfold IsGenerating
    rw [generatedSigmaAlgebra_coordPartitionFin_eq]
    exact coordPartition_isGenerating hT
  rw [ksEntropy_eq_ksEntropyPartition_of_generating hT (coordPartitionFin rho) hgen,
    ksEntropyPartition_coordPartitionFin_eq hT]
private lemma rawKsLe (rho : Measure X) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shiftMap rho rho) : ksEntropy hT ≤ (Real.log 2 : ℝ) := by
  rw [ks_eq_coord rho hT, EReal.coe_le_coe_iff]
  have hu := entropy_le_log_card_partition (coordPartition rho)
  have hl := ksEntropyPartition_le_entropy hT (coordPartition rho)
  simpa using hl.trans hu
private lemma rawFairKs : ksEntropy rawFairInvariant = (Real.log 2 : ℝ) := by
  rw [ks_eq_coord rawFair rawFairInvariant]
  have he := ksEntropyPartition_coordPartition_bern_eq fairSymbol
  have hh : Hnu fairSymbol = Real.log 2 := by
    simp [Hnu, fairSymbol_mass, Real.negMulLog]
  exact congrArg (fun r : ℝ => (r : EReal)) (he.trans hh)
private lemma full_word_uniform (rho : Measure X) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shiftMap rho rho) (hmax : ksEntropy hT = (Real.log 2 : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    (fun f => (rho ((ksJoin hT (coordPartition rho) n).cells f)).toReal) =
      (fun _ : Fin n → Bool => (Fintype.card (Fin n → Bool) : ℝ)⁻¹) := by
  have hk : ksEntropyPartition hT (coordPartition rho) = Real.log 2 := by
    apply EReal.coe_injective
    rw [← ks_eq_coord rho hT, hmax]
  have hl := ksEntropyPartition_le_ksEntropySeq_div hT (coordPartition rho) hn
  rw [hk] at hl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcard : Real.log (Fintype.card (Fin n → Bool)) = (n : ℝ) * Real.log 2 := by
    simp [Fintype.card_fun, Real.log_pow]
  have hu := entropy_le_log_card_partition (ksJoin hT (coordPartition rho) n)
  have heq : entropy rho (ksJoin hT (coordPartition rho) n).cells =
      Real.log (Fintype.card (Fin n → Bool)) := by
    apply le_antisymm hu
    rw [hcard]
    rw [le_div_iff₀ hnpos] at hl
    simpa only [ksEntropySeq, mul_comm] using hl
  exact (_root_.D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform _
    ⟨fun _ => ENNReal.toReal_nonneg,
      (ksJoin hT (coordPartition rho) n).sum_toReal_measure_eq_one⟩).mp heq
private lemma prefix_system : IsPiSystem {s : Set X | ∃ x n, s = PiNat.cylinder x n} := by
  rintro _ ⟨x, n, rfl⟩ _ ⟨y, m, rfl⟩ ⟨z, hz⟩
  have hx := PiNat.mem_cylinder_iff_eq.mp hz.1
  have hy := PiNat.mem_cylinder_iff_eq.mp hz.2
  rw [← hx, ← hy]
  rcases le_total n m with h | h
  · exact ⟨z, m, Set.inter_eq_right.mpr (PiNat.cylinder_anti z h)⟩
  · exact ⟨z, n, Set.inter_eq_left.mpr (PiNat.cylinder_anti z h)⟩
private lemma rawMaxUnique (rho : Measure X) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shiftMap rho rho) (hmax : ksEntropy hT = (Real.log 2 : ℝ)) :
    rho = rawFair := by
  apply MeasureTheory.ext_of_generate_finite {s : Set X | ∃ x n, s = PiNat.cylinder x n}
  · exact (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace X) = borel X).trans
      (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).borel_eq_generateFrom
  · exact prefix_system
  · rintro s ⟨x, n, rfl⟩
    by_cases hn : n = 0
    · subst n
      simp
    have hu := congrFun (full_word_uniform rho hT hmax n (by omega)) (fun k => x k)
    have hc (eta : Measure X) :
        ksJoinCells (coordPartition eta).cells shiftMap n (fun k => x k) =
          PiNat.cylinder x n := by
      change ksJoinCells (coordPartition (bern fairSymbol)).cells shiftMap n
        (fun k => x k) = PiNat.cylinder x n
      rw [ksJoinCells_coordPartition_eq fairSymbol]
      ext y
      simp only [Set.mem_setOf_eq, PiNat.mem_cylinder_iff]
      constructor
      · intro h i hi
        exact h ⟨i, hi⟩
      · intro h k
        exact h k k.2
    simp only [ksJoin_cells, hc rho] at hu
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [hu]
    have hfair := bern_ksJoinCells_eq fairSymbol n (fun k => x k)
    rw [hc (bern fairSymbol)] at hfair
    change _ = (bern fairSymbol (PiNat.cylinder x n)).toReal
    rw [hfair]
    simp [fairSymbol_mass, Fintype.card_fun, ENNReal.toReal_pow, inv_pow]
  · simp
end
end D5.S3.Entropy.FairBernoulli

namespace D5.S3.Entropy.FairBernoulli
open MeasureTheory D5.S3.Entropy.KolmogorovSinai
noncomputable section
private lemma ks_factor_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {T : A → A} {S : B → B} {f : A → B}
    (hT : MeasurePreserving T mu mu) (hS : MeasurePreserving S nu nu)
    (hf : MeasurePreserving f mu nu) (hsemi : f ∘ T = S ∘ f) :
    ksEntropy hS ≤ ksEntropy hT := by
  apply iSup_le
  intro n
  apply iSup_le
  intro P
  rw [← factor_relative_eq hT hS hf hsemi P]
  exact le_ksEntropy hT (P.pulledBack hf)
private lemma ks_conjugate {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {T : A → A} {S : B → B} (e : A ≃ᵐ B)
    (hT : MeasurePreserving T mu mu) (hS : MeasurePreserving S nu nu)
    (hf : MeasurePreserving e mu nu) (hsemi : e ∘ T = S ∘ e) :
    ksEntropy hS = ksEntropy hT := by
  apply le_antisymm (ks_factor_le hT hS hf hsemi)
  have hi : MeasurePreserving e.symm nu mu := by
    refine ⟨e.symm.measurable, ?_⟩
    rw [← hf.map_eq, e.map_symm_map]
  apply ks_factor_le hS hT hi
  funext y
  apply e.injective
  simpa using congrFun hsemi (e.symm y) |>.symm
end
end D5.S3.Entropy.FairBernoulli

namespace D5.S3.Entropy.SourceEquilibrium
open MeasureTheory D5.S3.Entropy.KolmogorovSinai
open D5.S3.Entropy.LopesOliveiraFullTail
noncomputable section
private lemma shift_m : Measurable shift :=
  Measurable.of_eval fun i => measurable_pi_apply (⟨i.val + 1, by omega⟩ : ℕ+)
private lemma semi : coordinateEquiv ∘ D5.S3.Entropy.BernoulliShift.shiftMap =
    shift ∘ coordinateEquiv := by
  funext x
  apply coordinateEquiv.symm.injective
  rfl
private lemma semi_inv : coordinateEquiv.symm ∘ shift =
    D5.S3.Entropy.BernoulliShift.shiftMap ∘ coordinateEquiv.symm := rfl
def fair : Measure Omega := Measure.map coordinateEquiv D5.S3.Entropy.FairBernoulli.rawFair
@[instance] private theorem fair_probability : IsProbabilityMeasure fair :=
  (Measure.isProbabilityMeasure_map_iff coordinateEquiv.measurable.aemeasurable).mpr inferInstance
lemma fair_invariant : MeasurePreserving shift fair fair := by
  refine ⟨shift_m, ?_⟩
  unfold fair
  rw [Measure.map_map shift_m coordinateEquiv.measurable, ← semi,
    ← Measure.map_map coordinateEquiv.measurable D5.S3.Entropy.FairBernoulli.rawFairInvariant.measurable,
    D5.S3.Entropy.FairBernoulli.rawFairInvariant.map_eq]
private lemma raw_invariant (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shift rho rho) :
    MeasurePreserving D5.S3.Entropy.BernoulliShift.shiftMap
      (Measure.map coordinateEquiv.symm rho) (Measure.map coordinateEquiv.symm rho) := by
  refine ⟨D5.S3.Entropy.BernoulliShift.measurable_shiftMap, ?_⟩
  rw [Measure.map_map D5.S3.Entropy.BernoulliShift.measurable_shiftMap
    coordinateEquiv.symm.measurable, ← semi_inv,
    ← Measure.map_map coordinateEquiv.symm.measurable shift_m, hT.map_eq]
lemma ks_le (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shift rho rho) : ksEntropy hT ≤ (Real.log 2 : ℝ) := by
  letI : IsProbabilityMeasure (Measure.map coordinateEquiv.symm rho) :=
    (Measure.isProbabilityMeasure_map_iff coordinateEquiv.symm.measurable.aemeasurable).mpr inferInstance
  rw [← D5.S3.Entropy.FairBernoulli.ks_conjugate coordinateEquiv.symm hT (raw_invariant rho hT)
    ⟨coordinateEquiv.symm.measurable, rfl⟩ semi_inv]
  exact D5.S3.Entropy.FairBernoulli.rawKsLe _ _
lemma fair_ks : ksEntropy fair_invariant = (Real.log 2 : ℝ) := by
  rw [D5.S3.Entropy.FairBernoulli.ks_conjugate coordinateEquiv D5.S3.Entropy.FairBernoulli.rawFairInvariant fair_invariant
    ⟨coordinateEquiv.measurable, rfl⟩ semi]
  exact D5.S3.Entropy.FairBernoulli.rawFairKs
lemma max_unique (rho : Measure Omega) [IsProbabilityMeasure rho]
    (hT : MeasurePreserving shift rho rho) (hm : ksEntropy hT = (Real.log 2 : ℝ)) :
    rho = fair := by
  letI : IsProbabilityMeasure (Measure.map coordinateEquiv.symm rho) :=
    (Measure.isProbabilityMeasure_map_iff coordinateEquiv.symm.measurable.aemeasurable).mpr inferInstance
  have hr := D5.S3.Entropy.FairBernoulli.ks_conjugate coordinateEquiv.symm hT (raw_invariant rho hT)
    ⟨coordinateEquiv.symm.measurable, rfl⟩ semi_inv
  have he := D5.S3.Entropy.FairBernoulli.rawMaxUnique _ (raw_invariant rho hT) (hr.trans hm)
  apply_fun Measure.map coordinateEquiv at he
  simpa [fair] using he
end
end D5.S3.Entropy.SourceEquilibrium

