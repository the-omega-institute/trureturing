/- GID: D5/S3/Geometry/ProbabilityTransport/CostCoupling
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/CostCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General cost Kantorovich Rubinstein transport -/
import D5.S3.Analytic.Convexity.FiniteStrongDuality
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Sequences

/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/brooks-suppliers/lean-pool-LICENSE.txt.
Authors: Joseph K. Miller
Selected optimal-transport declarations from LeanPool/Vlasov/OT/Coupling.lean
and LeanPool/Vlasov/OT/Wasserstein.lean, lean-pool commit
edbe5bd56f476cc2965564676b66199f281ab714.
The complete supplier NOTICE is retained verbatim in the owning
CostCoupling.scribe.cs. Modified: native imports and namespace, native simple
approximation with the original sigma-algebra, native finite strong duality,
and explicit finite attainment with a single c-transform potential.
-/

noncomputable section
open MeasureTheory ProbabilityTheory ENNReal Filter Topology
open scoped ProbabilityTheory
namespace CostTransport

def IsCoupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π : Measure (α × β)) (μ : Measure α) (ν : Measure β) : Prop :=
  Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν

noncomputable def wassersteinCostCoupling
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨅ (π : Measure (α × α)) (_ : IsCoupling π μ ν),
    ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π

noncomputable def wassersteinCost {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨆ (f : α → ℝ) (_ : ∀ x y, |f x - f y| ≤ c x y),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)

private lemma wassersteinCost_comm {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) :
    wassersteinCost c μ ν = wassersteinCost c ν μ := by
  unfold wassersteinCost
  have hneg : ∀ (f : α → ℝ), (∀ x y, |f x - f y| ≤ c x y) →
      ∀ x y, |(-f) x - (-f) y| ≤ c x y := by
    intro f hf x y
    simp only [Pi.neg_apply]
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact hf x y
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring

private lemma wassersteinCost_triangle {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν τ : Measure α) :
    wassersteinCost c μ τ ≤ wassersteinCost c μ ν + wassersteinCost c ν τ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hsplit : ∫ x, f x ∂μ - ∫ x, f x ∂τ =
      (∫ x, f x ∂μ - ∫ x, f x ∂ν) + (∫ x, f x ∂ν - ∫ x, f x ∂τ) := by ring
  rw [hsplit]
  calc ENNReal.ofReal _
      ≤ ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
          + ENNReal.ofReal (∫ x, f x ∂ν - ∫ x, f x ∂τ) :=
        ENNReal.ofReal_add_le
    _ ≤ (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂μ - ∫ x, g x ∂ν))
        + (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂ν - ∫ x, g x ∂τ)) := by
        gcongr
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

theorem wassersteinCostCoupling_comm
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (hc_symm : ∀ x y, c x y = c y x)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) :
    wassersteinCostCoupling c μ ν = wassersteinCostCoupling c ν μ := by
  have key : ∀ (a b : Measure α),
      wassersteinCostCoupling c a b ≤ wassersteinCostCoupling c b a := by
    intro a b
    unfold wassersteinCostCoupling
    refine le_iInf fun π => le_iInf fun hπ => ?_
    have hswap : IsCoupling (Measure.map Prod.swap π) a b := by
      refine ⟨?_, ?_⟩
      · rw [Measure.map_map measurable_fst measurable_swap]; exact hπ.2
      · rw [Measure.map_map measurable_snd measurable_swap]; exact hπ.1
    refine iInf_le_of_le (Measure.map Prod.swap π) (iInf_le_of_le hswap (le_of_eq ?_))
    calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map Prod.swap π)
        = ∫⁻ z, ENNReal.ofReal (c (Prod.swap z).1 (Prod.swap z).2) ∂π :=
          lintegral_map (ENNReal.measurable_ofReal.comp hc_meas) measurable_swap
      _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π := by
          refine lintegral_congr fun z => ?_
          simp only [Prod.fst_swap, Prod.snd_swap]
          exact congrArg ENNReal.ofReal (hc_symm z.2 z.1)
  exact le_antisymm (key μ ν) (key ν μ)

theorem exists_coupling_glue
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ]
    (π₁ : Measure (α × α)) (h₁ : IsCoupling π₁ μ ρ)
    (π₂ : Measure (α × α)) (h₂ : IsCoupling π₂ ρ ν) :
    ∃ π₃ : Measure (α × α), IsCoupling π₃ μ ν ∧
      ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃
        ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hπ₁ : IsProbabilityMeasure π₁ := by
    constructor
    have h : π₁ Set.univ = μ Set.univ := by
      rw [← h₁.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  have hπ₂ : IsProbabilityMeasure π₂ := by
    constructor
    have h : π₂ Set.univ = ρ Set.univ := by
      rw [← h₂.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [h, measure_univ]
  set κ₂ : Kernel α α := π₂.condKernel with hκ₂
  have : IsMarkovKernel κ₂ := by rw [hκ₂]; infer_instance
  set κ₂' : Kernel (α × α) α := κ₂.comap Prod.snd measurable_snd with hκ₂'
  set glued : Measure ((α × α) × α) := π₁ ⊗ₘ κ₂' with hglued
  set proj : (α × α) × α → α × α := fun w => (w.1.1, w.2) with hproj
  have hproj_meas : Measurable proj :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hg : Measurable (fun z : α × α => ENNReal.ofReal (c z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hc_meas
  have hdisint : π₂.fst ⊗ₘ κ₂ = π₂ := by
    rw [hκ₂]; exact Measure.disintegrate π₂ π₂.condKernel
  have hρπ₂ : ρ ⊗ₘ κ₂ = π₂ := by rw [show ρ = π₂.fst from h₂.1.symm]; exact hdisint
  refine ⟨glued.map proj, ⟨?_, ?_⟩, ?_⟩
  · -- fst marginal = μ
    rw [Measure.map_map measurable_fst hproj_meas]
    have hcomp : (Prod.fst ∘ proj) = (Prod.fst ∘ Prod.fst : (α × α) × α → α) := rfl
    rw [hcomp, ← Measure.map_map measurable_fst measurable_fst,
      show Measure.map Prod.fst glued = π₁ from Measure.fst_compProd π₁ κ₂']
    exact h₁.1
  · -- snd marginal = ν
    rw [Measure.map_map measurable_snd hproj_meas]
    have hcomp : (Prod.snd ∘ proj) = (Prod.snd : (α × α) × α → α) := rfl
    rw [hcomp, show Measure.map Prod.snd glued = κ₂' ∘ₘ π₁ from Measure.snd_compProd π₁ κ₂']
    have hLHS : κ₂' ∘ₘ π₁ = Measure.bind π₁ (fun p => κ₂ p.2) :=
      Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Kernel.comap_apply κ₂ measurable_snd p)
    have hbindmap : κ₂ ∘ₘ (Measure.map Prod.snd π₁) = Measure.bind π₁ (fun p => κ₂ p.2) := by
      rw [show Measure.map Prod.snd π₁ = Measure.bind π₁ (fun p => Measure.dirac p.2) from
            (Measure.bind_dirac_eq_map π₁ measurable_snd).symm,
        show (κ₂ ∘ₘ Measure.bind π₁ (fun p => Measure.dirac p.2))
            = Measure.bind (Measure.bind π₁ (fun p => Measure.dirac p.2)) κ₂ from rfl,
        Measure.bind_bind
          (by fun_prop : Measurable (fun p : α × α => Measure.dirac p.2)).aemeasurable
          κ₂.aemeasurable]
      exact Measure.bind_congr_right
        (Filter.Eventually.of_forall fun p => Measure.dirac_bind κ₂.measurable p.2)
    have hRHS : ν = Measure.bind π₁ (fun p => κ₂ p.2) := by
      calc ν = π₂.snd := h₂.2.symm
        _ = (π₂.fst ⊗ₘ κ₂).snd := by rw [hdisint]
        _ = κ₂ ∘ₘ π₂.fst := Measure.snd_compProd π₂.fst κ₂
        _ = κ₂ ∘ₘ ρ := by rw [show π₂.fst = ρ from h₂.1]
        _ = κ₂ ∘ₘ (Measure.map Prod.snd π₁) := by
            rw [show ρ = Measure.map Prod.snd π₁ from h₁.2.symm]
        _ = Measure.bind π₁ (fun p => κ₂ p.2) := hbindmap
    rw [hLHS, hRHS]
  · -- cost bound: lintegral_compProd (Tonelli) + ground-cost triangle + Markov.
    have hF : Measurable (fun w : (α × α) × α => ENNReal.ofReal (c w.1.1 w.2)) :=
      hg.comp hproj_meas
    have hLcost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(glued.map proj)
        = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
      rw [hglued]
      calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂((π₁ ⊗ₘ κ₂').map proj)
          = ∫⁻ w, ENNReal.ofReal (c w.1.1 w.2) ∂(π₁ ⊗ₘ κ₂') := by
            rw [lintegral_map hg hproj_meas]
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂' p) ∂π₁ := Measure.lintegral_compProd hF
        _ = ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁ := by
            simp only [hκ₂', Kernel.comap_apply]
    have hkey2 : ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
        = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by
      have hF_meas : Measurable (fun y : α => ∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) :=
        Measurable.lintegral_kernel_prod_right' hg
      calc ∫⁻ p, (∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁
          = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂(Measure.map Prod.snd π₁) :=
            (lintegral_map hF_meas measurable_snd).symm
        _ = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (c y z) ∂(κ₂ y)) ∂ρ := by rw [h₁.2]
        _ = ∫⁻ w, ENNReal.ofReal (c w.1 w.2) ∂(ρ ⊗ₘ κ₂) := (Measure.lintegral_compProd hg).symm
        _ = ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂ := by rw [hρπ₂]
    rw [hLcost]
    have hbound : ∫⁻ p, ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2) ∂π₁
        ≤ ∫⁻ p, (ENNReal.ofReal (c p.1 p.2)
            + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2)) ∂π₁ := by
      refine lintegral_mono fun p => ?_
      calc ∫⁻ z, ENNReal.ofReal (c p.1 z) ∂(κ₂ p.2)
          ≤ ∫⁻ z, (ENNReal.ofReal (c p.1 p.2) + ENNReal.ofReal (c p.2 z)) ∂(κ₂ p.2) := by
            refine lintegral_mono fun z => ?_
            exact (ENNReal.ofReal_le_ofReal (hc_triangle p.1 p.2 z)).trans ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (c p.1 p.2) + ∫⁻ z, ENNReal.ofReal (c p.2 z) ∂(κ₂ p.2) := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    refine hbound.trans (le_of_eq ?_)
    rw [lintegral_add_left hg, hkey2]

theorem wassersteinCostCoupling_triangle
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] :
    wassersteinCostCoupling c μ ν
      ≤ wassersteinCostCoupling c μ ρ + wassersteinCostCoupling c ρ ν := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hAB => ?_
  have hAfin : wassersteinCostCoupling c μ ρ < ⊤ := (ENNReal.add_lt_top.mp hAB).1
  have hBfin : wassersteinCostCoupling c ρ ν < ⊤ := (ENNReal.add_lt_top.mp hAB).2
  have hδ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num)
  obtain ⟨π₁, h₁, hc₁⟩ : ∃ π₁, IsCoupling π₁ μ ρ ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁) < wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCostCoupling c μ ρ < wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hAfin.ne hδ.ne'
    unfold wassersteinCostCoupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₂, h₂, hc₂⟩ : ∃ π₂, IsCoupling π₂ ρ ν ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) < wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2 := by
    have hlt : wassersteinCostCoupling c ρ ν < wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2 :=
      ENNReal.lt_add_right hBfin.ne hδ.ne'
    unfold wassersteinCostCoupling at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨π, hπ⟩ := hlt
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hcost⟩ := hπ
    exact ⟨π, h, hcost⟩
  obtain ⟨π₃, h₃, hcost⟩ :=
    exists_coupling_glue c hc_triangle hc_meas μ ν ρ π₁ h₁ π₂ h₂
  calc wassersteinCostCoupling c μ ν
      ≤ ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₃ :=
        iInf_le_of_le π₃ (iInf_le_of_le h₃ le_rfl)
    _ ≤ (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₁)
          + (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π₂) := hcost
    _ ≤ (wassersteinCostCoupling c μ ρ + (ε : ℝ≥0∞) / 2)
          + (wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) / 2) := add_le_add hc₁.le hc₂.le
    _ = wassersteinCostCoupling c μ ρ + wassersteinCostCoupling c ρ ν + (ε : ℝ≥0∞) := by
        rw [add_add_add_comm, ENNReal.add_halves]

theorem wassersteinCostCoupling_map_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α)
    (T : α → α) (hT : Measurable T) :
    wassersteinCostCoupling c μ (Measure.map T μ)
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  have hg : Measurable (fun x : α => (x, T x)) := measurable_id.prodMk hT
  have hγ : IsCoupling (Measure.map (fun x => (x, T x)) μ) μ (Measure.map T μ) := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst hg]
      rw [show (Prod.fst ∘ fun x : α => (x, T x)) = id from rfl, Measure.map_id]
    · rw [Measure.map_map measurable_snd hg]; rfl
  unfold wassersteinCostCoupling
  refine iInf_le_of_le (Measure.map (fun x => (x, T x)) μ) (iInf_le_of_le hγ (le_of_eq ?_))
  calc ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(Measure.map (fun x => (x, T x)) μ)
      = ∫⁻ x, ENNReal.ofReal (c (x, T x).1 (x, T x).2) ∂μ :=
        lintegral_map (ENNReal.measurable_ofReal.comp hc_cont.measurable) hg
    _ = ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := rfl

private theorem wassersteinCost_dual_singleMap_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ : Measure α) [IsProbabilityMeasure μ] (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (T : α → α) (hT : Measurable T) :
    wassersteinCost c (Measure.map T μ) μ ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  by_cases hItop : (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ) = ⊤
  · rw [hItop]; exact le_top
  have hf_cont : Continuous f := by
    rw [Metric.continuous_iff]
    intro a ε hε
    have hca : Continuous (fun x => c x a) :=
      hc_cont.comp (continuous_id.prodMk continuous_const)
    have hca0 : Filter.Tendsto (fun x => c x a) (nhds a) (nhds 0) := by
      have h := hca.tendsto a
      rwa [hc_self a] at h
    obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhds_nhds.1 hca0 ε hε
    refine ⟨δ, hδ0, fun x hx => ?_⟩
    have hcxa : dist (c x a) 0 < ε := hδ hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hc_nonneg x a)] at hcxa
    calc dist (f x) (f a) = |f x - f a| := Real.dist_eq _ _
      _ ≤ c x a := hf x a
      _ < ε := hcxa
  have hf_meas : Measurable f := hf_cont.measurable
  have hf_int_mu : Integrable f μ := by
    have hbound : ∀ x, |f x| ≤ |f x₀| + c x x₀ := fun x => by
      calc |f x|
          = |(f x - f x₀) + f x₀| := by ring_nf
        _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
        _ ≤ c x x₀ + |f x₀| := by have := hf x x₀; linarith
        _ = |f x₀| + c x x₀ := by ring
    refine ((integrable_const |f x₀|).add hμ_cm).mono hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x₀)) (hc_nonneg x x₀))]
    exact hbound x
  have hcT_meas : Measurable (fun x => c x (T x)) :=
    hc_cont.measurable.comp (measurable_id.prodMk hT)
  have hcT_int : Integrable (fun x => c x (T x)) μ := by
    refine ⟨hcT_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have henorm : ∀ x, ‖c x (T x)‖ₑ = ENNReal.ofReal (c x (T x)) := fun x => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc_nonneg x (T x))]
    simp_rw [henorm]
    exact lt_top_iff_ne_top.mpr hItop
  have hfT_int : Integrable (fun x => f (T x)) μ := by
    have hbound2 : ∀ x, |f (T x)| ≤ |f x| + c x (T x) := fun x => by
      have h1 := hf (T x) x
      rw [hc_symm (T x) x] at h1
      calc |f (T x)|
          = |(f (T x) - f x) + f x| := by ring_nf
        _ ≤ |f (T x) - f x| + |f x| := abs_add_le _ _
        _ ≤ c x (T x) + |f x| := by linarith
        _ = |f x| + c x (T x) := by ring
    refine (hf_int_mu.abs.add hcT_int).mono (hf_meas.comp hT).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (abs_nonneg (f x)) (hc_nonneg x (T x)))]
    exact hbound2 x
  have hcov : (∫ x, f x ∂(Measure.map T μ)) = ∫ x, f (T x) ∂μ :=
    integral_map hT.aemeasurable hf_cont.aestronglyMeasurable
  rw [hcov, ← integral_sub hfT_int hf_int_mu]
  have hmono : (∫ x, (f (T x) - f x) ∂μ) ≤ ∫ x, c x (T x) ∂μ := by
    refine integral_mono_ae (hfT_int.sub hf_int_mu) hcT_int
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 := hf (T x) x
    rw [hc_symm (T x) x] at h1
    calc f (T x) - f x ≤ |f (T x) - f x| := le_abs_self _
      _ ≤ c x (T x) := h1
  refine (ENNReal.ofReal_le_ofReal hmono).trans (le_of_eq ?_)
  exact ofReal_integral_eq_lintegral_ofReal hcT_int
    (Filter.Eventually.of_forall fun x => hc_nonneg x (T x))

theorem wassersteinCost_dual_le_add_map
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ) (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν
        + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
        + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by
  have htri1 := wassersteinCost_triangle c (Measure.map T μ) μ (Measure.map S ν)
  have htri2 := wassersteinCost_triangle c μ ν (Measure.map S ν)
  have hT_bound : wassersteinCost c (Measure.map T μ) μ
      ≤ ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ :=
    wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont μ x₀ hμ_cm T hT
  have hS_bound : wassersteinCost c ν (Measure.map S ν)
      ≤ ∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν := by
    rw [wassersteinCost_comm c ν (Measure.map S ν)]
    exact wassersteinCost_dual_singleMap_le c hc_nonneg hc_self hc_symm hc_cont ν x₀ hν_cm S hS
  calc wassersteinCost c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) μ + wassersteinCost c μ (Measure.map S ν) := htri1
    _ ≤ wassersteinCost c (Measure.map T μ) μ
          + (wassersteinCost c μ ν + wassersteinCost c ν (Measure.map S ν)) :=
        add_le_add le_rfl htri2
    _ ≤ (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (wassersteinCost c μ ν + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν)) :=
        add_le_add hT_bound (add_le_add le_rfl hS_bound)
    _ = wassersteinCost c μ ν
          + (∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ)
          + (∫⁻ y, ENNReal.ofReal (c y (S y)) ∂ν) := by abel


private structure CostCopy (α : Type*) where
  val : α

theorem exists_finiteRange_map_cost_le
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_self : ∀ x, c x x = 0) (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ : Measure α) (x₀ : α) (hμ_cm : Integrable (fun y => c y x₀) μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : α → α, Measurable T ∧ (Set.range T).Finite ∧
      ∫⁻ x, ENNReal.ofReal (c x (T x)) ∂μ ≤ ENNReal.ofReal ε := by
  let : MeasurableSpace (CostCopy α) := MeasurableSpace.map CostCopy.mk inferInstance
  have hUp : Measurable (CostCopy.mk : α → CostCopy α) := fun _ => id
  have hDown : Measurable (CostCopy.val : CostCopy α → α) := fun _ => id
  let : PseudoMetricSpace (CostCopy α) :=
    { dist := fun x y => c x.val y.val
      dist_self := fun x => hc_self x.val
      dist_comm := fun x y => hc_symm x.val y.val
      dist_triangle := fun x y z => hc_triangle x.val y.val z.val }
  have hup : LipschitzWith 1 (CostCopy.mk : α → CostCopy α) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change c x y ≤ (1 : ℝ) * dist x y
    simpa only [NNReal.coe_one, one_mul] using hc_le_dist x y
  let : OpensMeasurableSpace (CostCopy α) := by
    apply (opensMeasurableSpace_iff_forall_measurableSet).2
    intro s hs
    exact (hs.preimage hup.continuous).measurableSet
  let : TopologicalSpace.SeparableSpace (CostCopy α) :=
    Function.Surjective.denseRange (fun x => ⟨x.val, rfl⟩) |>.separableSpace hup.continuous
  let F : ℕ → SimpleFunc α (CostCopy α) :=
    SimpleFunc.approxOn CostCopy.mk hUp Set.univ (CostCopy.mk x₀) (Set.mem_univ _)
  let T : ℕ → α → α := fun n x => (F n x).val
  have hT (n : ℕ) : Measurable (T n) := hDown.comp (F n).measurable
  have hfin (n : ℕ) : (Set.range (T n)).Finite :=
    (F n).finite_range.image CostCopy.val |>.subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩)
  have hid (n : ℕ) (x : α) :
      ENNReal.ofReal (c x (T n x)) = edist (F n x) (CostCopy.mk x) := by
    rw [edist_dist]
    change ENNReal.ofReal (c x (T n x)) = ENNReal.ofReal (c (T n x) x)
    exact congrArg ENNReal.ofReal (hc_symm _ _)
  have hbound (n : ℕ) (x : α) :
      ENNReal.ofReal (c x (T n x)) ≤ ENNReal.ofReal (c x x₀) := by
    rw [hid, edist_dist]
    change ENNReal.ofReal (c (T n x) x) ≤ ENNReal.ofReal (c x x₀)
    have h : edist (F n x) (CostCopy.mk x : CostCopy α) ≤
        edist (CostCopy.mk x₀ : CostCopy α) (CostCopy.mk x) :=
      SimpleFunc.edist_approxOn_le hUp (Set.mem_univ (CostCopy.mk x₀)) x n
    simp only [edist_dist] at h
    change ENNReal.ofReal (c (T n x) x) ≤ ENNReal.ofReal (c x₀ x) at h
    rwa [hc_symm x₀ x] at h
  have hlim (x : α) : Tendsto (fun n => ENNReal.ofReal (c x (T n x))) atTop (𝓝 0) := by
    simp_rw [hid]
    apply tendsto_iff_edist_tendsto_0.mp
    exact SimpleFunc.tendsto_approxOn hUp (Set.mem_univ (CostCopy.mk x₀)) (by simp)
  have hint : ∫⁻ x, ENNReal.ofReal (c x x₀) ∂μ ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hμ_cm.aestronglyMeasurable
      (ae_of_all μ (fun x => hc_nonneg x x₀))).2 hμ_cm
  have hconv : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (c x (T n x)) ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (c x x₀))
      (fun n => ENNReal.measurable_ofReal.comp (hc_cont.measurable.comp (measurable_id.prodMk (hT n))))
      (fun n => ae_of_all μ (hbound n)) hint (ae_of_all μ hlim)
    simpa only [lintegral_zero, Function.comp_apply, id_eq] using h
  have he := (ENNReal.tendsto_nhds_zero.mp hconv) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp he
  exact ⟨T n, hT n, hfin n, hn n le_rfl⟩

end CostTransport

open D5.S3.Analytic.Convexity.FarkasAlternative
open D5.S3.Analytic.Convexity.ExtendedFarkas
open D5.S3.Analytic.Convexity.FiniteStrongDuality
open scoped Matrix
namespace FiniteTransportInterface
noncomputable section
universe u v

private lemma e_ne_bot (x : ℝ) : toE x ≠ (⊥ : Extend ℝ) := WithBot.coe_ne_bot
private lemma e_ne_top (x : ℝ) : toE x ≠ (⊤ : Extend ℝ) := by
  intro h
  exact WithTop.coe_ne_top (WithBot.coe_eq_coe.mp h)
private lemma e_le (x y : ℝ) : toE x ≤ toE y ↔ x ≤ y :=
  (WithBot.coe_strictMono.comp WithTop.coe_strictMono).le_iff_le
private lemma e_inj (x y : ℝ) : toE x = toE y ↔ x = y :=
  (WithBot.coe_strictMono.comp WithTop.coe_strictMono).injective.eq_iff
private lemma e_dot {K : Type*} [Fintype K] (c : K → ℝ) (x : K → NNeg ℝ) :
    (fun k => toE (c k)) ᵥ⬝ x = toE (∑ k, c k * (x k).val) := by
  change (∑ k, toE ((x k).val * c k)) = _
  calc
    (∑ k, toE ((x k).val * c k)) = ∑ k, toE (c k * (x k).val) := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg toE (mul_comm _ _)
    _ = toE (∑ k, c k * (x k).val) :=
      (map_sum (RatAddHom (F := ℝ)) (fun k => c k * (x k).val) Finset.univ).symm

private def realLP {I J : Type*} (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) :
    ValidELP I J ℝ where
  A i j := toE (A i j)
  b i := toE (b i)
  c j := toE (c j)
  hAi := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_bot _ h
  hAj := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_bot _ h
  hbA := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_bot _ h
  hcA := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_top _ h
  hAb := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_top _ h
  hAc := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_bot _ h

private lemma real_solution {I J : Type*} [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) (x : J → NNeg ℝ) :
    (realLP A b c).IsSolution x ↔ ∀ i, ∑ j, A i j * (x j).val ≤ b i := by
  change (∀ i, (fun j => toE (A i j)) ᵥ⬝ x ≤ toE (b i)) ↔ _
  simp only [e_dot, e_le]

private lemma real_dual_solution {I J : Type*} [Fintype I]
    (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) (y : I → NNeg ℝ) :
    (realLP A b c).dualize.IsSolution y ↔ ∀ j, ∑ i, -(A i j) * (y i).val ≤ c j := by
  change (∀ j, (fun i => toE (-(A i j))) ᵥ⬝ y ≤ toE (c j)) ↔ _
  simp only [e_dot, e_le]

private lemma paired_solution {K J : Type*} [Fintype J]
    (B : K → J → ℝ) (d : K → ℝ) (c : J → ℝ) (x : J → NNeg ℝ) :
    (realLP (Sum.elim B (fun k j => -B k j))
      (Sum.elim d (fun k => -d k)) c).IsSolution x ↔
      ∀ k, ∑ j, B k j * (x j).val = d k := by
  rw [real_solution]
  constructor
  · intro h k
    have hp := h (Sum.inl k)
    have hm := h (Sum.inr k)
    change (∑ j, B k j * (x j).val) ≤ d k at hp
    change (∑ j, -(B k j) * (x j).val) ≤ -(d k) at hm
    simp only [neg_mul, Finset.sum_neg_distrib] at hm
    linarith
  · intro h s
    cases s with
    | inl k => exact le_of_eq (h k)
    | inr k =>
      change (∑ j, -(B k j) * (x j).val) ≤ -(d k)
      simp only [neg_mul, Finset.sum_neg_distrib]
      exact le_of_eq (congrArg Neg.neg (h k))

private lemma paired_dual_sum {K J : Type*} [Fintype K]
    (B : K → J → ℝ) (y : K ⊕ K → NNeg ℝ) (j : J) :
    (∑ s : K ⊕ K, -(Sum.elim B (fun k j => -B k j) s j) * (y s).val) =
      ∑ k, B k j * ((y (Sum.inr k)).val - (y (Sum.inl k)).val) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

private lemma paired_objective {K : Type*} [Fintype K]
    (d : K → ℝ) (y : K ⊕ K → NNeg ℝ) :
    (∑ s : K ⊕ K, Sum.elim d (fun k => -d k) s * (y s).val) =
      -(∑ k, d k * ((y (Sum.inr k)).val - (y (Sum.inl k)).val)) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private def incidence : (m ⊕ n) → (m × n) → ℝ := fun s ij =>
  match s with
  | Sum.inl i => if i = ij.1 then 1 else 0
  | Sum.inr j => if j = ij.2 then 1 else 0

private lemma incidence_row (x : m × n → ℝ) (i : m) :
    (∑ ij, incidence (Sum.inl i) ij * x ij) = ∑ j, x (i,j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [incidence]

private lemma incidence_col (x : m × n → ℝ) (j : n) :
    (∑ ij, incidence (Sum.inr j) ij * x ij) = ∑ i, x (i,j) := by
  simp [incidence, Fintype.sum_prod_type]

private lemma incidence_dual (z : m ⊕ n → ℝ) (ij : m × n) :
    (∑ s, incidence s ij * z s) = z (Sum.inl ij.1) + z (Sum.inr ij.2) := by
  simp [incidence, Fintype.sum_sum_type]

end
noncomputable section
universe u v

private theorem finite_transport_attained {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (a : m → ℝ) (b : n → ℝ) (Cost : m → n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ j, b j = 1)
    (hCost : ∀ i j, 0 ≤ Cost i j) :
    ∃ (P : m → n → ℝ) (u : m → ℝ) (v : n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧
      (∀ i, ∑ j, P i j = a i) ∧
      (∀ j, ∑ i, P i j = b j) ∧
      (∀ i j, u i + v j ≤ Cost i j) ∧
      (∑ i, ∑ j, Cost i j * P i j) = (∑ i, a i * u i) + ∑ j, b j * v j := by
  classical
  let B : (m ⊕ n) → (m × n) → ℝ := incidence
  let d : (m ⊕ n) → ℝ := Sum.elim a b
  let A : ((m ⊕ n) ⊕ (m ⊕ n)) → (m × n) → ℝ :=
    Sum.elim B (fun k j => -B k j)
  let rhs : ((m ⊕ n) ⊕ (m ⊕ n)) → ℝ := Sum.elim d (fun k => -d k)
  let c : (m × n) → ℝ := fun ij => Cost ij.1 ij.2
  let L := realLP A rhs c
  let x0 : (m × n) → NNeg ℝ := fun ij => ⟨a ij.1 * b ij.2, mul_nonneg (ha _) (hb _)⟩
  have hx0 : L.IsSolution x0 := by
    apply (paired_solution B d c x0).mpr
    intro k
    cases k with
    | inl i =>
      change (∑ ij, incidence (Sum.inl i) ij * (a ij.1 * b ij.2)) = a i
      rw [incidence_row]
      change (∑ j, a i * b j) = a i
      rw [← Finset.mul_sum, hb1, mul_one]
    | inr j =>
      change (∑ ij, incidence (Sum.inr j) ij * (a ij.1 * b ij.2)) = b j
      rw [incidence_col]
      change (∑ i, a i * b j) = b j
      rw [← Finset.sum_mul, ha1, one_mul]
  have hP : L.IsFeasible :=
    ⟨toE (∑ ij, c ij * (x0 ij).val), ⟨x0, hx0, e_dot c x0⟩, e_ne_top _⟩
  let y0 : ((m ⊕ n) ⊕ (m ⊕ n)) → NNeg ℝ := fun _ => 0
  have hy0 : L.dualize.IsSolution y0 := by
    apply (real_dual_solution A rhs c y0).mpr
    intro ij
    change (∑ k : ((m ⊕ n) ⊕ (m ⊕ n)), -(A k ij) * (0 : ℝ)) ≤ Cost ij.1 ij.2
    simpa only [mul_zero, Finset.sum_const_zero] using hCost ij.1 ij.2
  have hQ : L.dualize.IsFeasible := by
    refine ⟨toE 0, ⟨y0, hy0, ?_⟩, e_ne_top 0⟩
    change (fun k => toE (rhs k)) ᵥ⬝ y0 = toE 0
    rw [e_dot]
    congr 1
    change (∑ k, rhs k * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  obtain ⟨r, ⟨x, hx, hcx⟩, ⟨y, hy, hdy⟩⟩ :=
    L.strong_duality_of_both_feasible hP hQ
  let z : (m ⊕ n) → ℝ := fun k => (y (Sum.inr k)).val - (y (Sum.inl k)).val
  have hxeq : ∀ k, ∑ ij, B k ij * (x ij).val = d k :=
    (paired_solution B d c x).mp hx
  have hrow (i : m) : ∑ j, (x (i,j)).val = a i := by
    have h := hxeq (Sum.inl i)
    change (∑ ij, incidence (Sum.inl i) ij * (x ij).val) = a i at h
    rwa [incidence_row] at h
  have hcol (j : n) : ∑ i, (x (i,j)).val = b j := by
    have h := hxeq (Sum.inr j)
    change (∑ ij, incidence (Sum.inr j) ij * (x ij).val) = b j at h
    rwa [incidence_col] at h
  have hpot (i : m) (j : n) : z (Sum.inl i) + z (Sum.inr j) ≤ Cost i j := by
    have h := (real_dual_solution A rhs c y).mp hy (i,j)
    change (∑ k, -(Sum.elim B (fun k j => -B k j) k (i,j)) * (y k).val) ≤ Cost i j at h
    rw [paired_dual_sum] at h
    change (∑ k, incidence k (i,j) * z k) ≤ Cost i j at h
    rwa [incidence_dual] at h
  have hcx_real : (∑ ij, c ij * (x ij).val) = -r := by
    change (fun ij => toE (c ij)) ᵥ⬝ x = toE (-r) at hcx
    rw [e_dot] at hcx
    exact (e_inj _ _).mp hcx
  have hdy_real : (∑ k, rhs k * (y k).val) = r := by
    change (fun k => toE (rhs k)) ᵥ⬝ y = toE r at hdy
    rw [e_dot] at hdy
    exact (e_inj _ _).mp hdy
  have hobj : (∑ ij, c ij * (x ij).val) = ∑ k, d k * z k := by
    have hsign : (∑ k, rhs k * (y k).val) = -(∑ k, d k * z k) :=
      paired_objective d y
    linarith
  refine ⟨(fun i j => (x (i,j)).val), (fun i => z (Sum.inl i)),
    (fun j => z (Sum.inr j)), (fun i j => (x (i,j)).property), hrow, hcol, hpot, ?_⟩
  simpa only [c, d, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr] using hobj

end
end FiniteTransportInterface

namespace CostTransport

private def finiteCTransform {α : Type*} (A : Finset α) (hA : A.Nonempty)
    (c : α → α → ℝ) (u : α → ℝ) (x : α) : ℝ :=
  A.sup' hA (fun a => u a - c x a)

private theorem finiteCTransform_properties {α : Type*}
    (A : Finset α) (hA : A.Nonempty) (c : α → α → ℝ)
    (hc_self : ∀ x, c x x = 0) (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z) (u v : α → ℝ) :
    (∀ x y, |finiteCTransform A hA c u x - finiteCTransform A hA c u y| ≤ c x y) ∧
    (∀ a ∈ A, u a ≤ finiteCTransform A hA c u a) ∧
    (∀ b, (∀ a ∈ A, u a + v b ≤ c a b) → finiteCTransform A hA c u b ≤ -v b) := by
  let g := finiteCTransform A hA c u
  have key (x y : α) : g x ≤ g y + c x y := by
    apply Finset.sup'_le
    intro a ha
    have h1 : u a - c y a ≤ g y := Finset.le_sup' (fun a => u a - c y a) ha
    have h2 := hc_triangle y x a
    have h3 := hc_symm x y
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [abs_sub_le_iff]
    exact ⟨by linarith [key x y], by linarith [key y x, hc_symm x y]⟩
  · intro a ha
    have h := Finset.le_sup' (fun b => u b - c a b) ha
    simpa only [hc_self, sub_zero, finiteCTransform] using h
  · intro b hb
    apply Finset.sup'_le
    intro a ha
    have h := hb a ha
    have hs := hc_symm b a
    linarith

private theorem finite_transport_balance {I : Type*} [Fintype I]
    (a b : I → ℝ) (P : I → I → ℝ)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (f : I → ℝ) :
    (∑ i, a i * f i) - ∑ j, b j * f j = ∑ i, ∑ j, (f i - f j) * P i j := by
  have hr : (∑ i, ∑ j, f i * P i j) = ∑ i, a i * f i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, hrow, mul_comm]
  have hc : (∑ i, ∑ j, f j * P i j) = ∑ j, b j * f j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, hcol, mul_comm]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hr, hc]

private theorem finite_transport_weak {I : Type*} [Fintype I]
    (a b : I → ℝ) (c P : I → I → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (f : I → ℝ) (hf : ∀ i j, |f i - f j| ≤ c i j) :
    (∑ i, a i * f i) - ∑ j, b j * f j ≤ ∑ i, ∑ j, c i j * P i j := by
  rw [finite_transport_balance a b P hrow hcol f]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hf i j)) (hP i j)

/-- Finite KR duality with an actual optimal matrix and an attained single-potential maximum. -/
theorem finite_kr_attained {I : Type*} [Fintype I]
    (a b : I → ℝ) (c : I → I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ j, b j = 1)
    (hc : ∀ i j, 0 ≤ c i j) (hc_self : ∀ i, c i i = 0)
    (hc_symm : ∀ i j, c i j = c j i)
    (hc_triangle : ∀ i j k, c i k ≤ c i j + c j k) :
    ∃ (P : I → I → ℝ) (f : I → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = a i) ∧
      (∀ j, ∑ i, P i j = b j) ∧ (∀ i j, |f i - f j| ≤ c i j) ∧
      (∑ i, ∑ j, c i j * P i j) = (∑ i, a i * f i) - ∑ j, b j * f j ∧
      (∀ Q : I → I → ℝ, (∀ i j, 0 ≤ Q i j) →
        (∀ i, ∑ j, Q i j = a i) → (∀ j, ∑ i, Q i j = b j) →
        (∑ i, ∑ j, c i j * P i j) ≤ ∑ i, ∑ j, c i j * Q i j) ∧
      (∀ g : I → ℝ, (∀ i j, |g i - g j| ≤ c i j) →
        (∑ i, a i * g i) - ∑ j, b j * g j ≤ (∑ i, a i * f i) - ∑ j, b j * f j) := by
  classical
  have hne : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : (∑ i, a i) = 0 := by rw [he]; rfl
    linarith
  obtain ⟨P, u, v, hP, hrow, hcol, hfeas, hobj⟩ :=
    FiniteTransportInterface.finite_transport_attained a b c ha hb ha1 hb1 hc
  let f := finiteCTransform Finset.univ hne c u
  obtain ⟨hf, hfu, hfv⟩ :=
    finiteCTransform_properties Finset.univ hne c hc_self hc_symm hc_triangle u v
  have hge : (∑ i, a i * u i) + ∑ j, b j * v j ≤
      (∑ i, a i * f i) - ∑ j, b j * f j := by
    have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hfu i (Finset.mem_univ i)) (ha i))
    have hv := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hfv j (fun i _ => hfeas i j)) (hb j))
    have h := add_le_add hu hv
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    dsimp only [f]
    linarith
  have heq : (∑ i, ∑ j, c i j * P i j) =
      (∑ i, a i * f i) - ∑ j, b j * f j := by
    exact le_antisymm (hobj.trans_le hge) (finite_transport_weak a b c P hP hrow hcol f hf)
  refine ⟨P, f, hP, hrow, hcol, hf, heq, ?_, ?_⟩
  · intro Q hQ hQr hQc
    rw [heq]
    exact finite_transport_weak a b c Q hQ hQr hQc f hf
  · intro g hg
    rw [← heq]
    exact finite_transport_weak a b c P hP hrow hcol g hg


private theorem finiteRange_optimal_coupling
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    ∃ (π : Measure (α × α)) (g : α → ℝ),
      IsCoupling π (Measure.map T μ) (Measure.map S ν) ∧
      (∀ x y, |g x - g y| ≤ c x y) ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π) =
        ENNReal.ofReal (∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν)) := by
  classical
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  let A := hTfin.toFinset ∪ hSfin.toFinset
  have hTA : ∀ x, T x ∈ A := fun x => Finset.mem_union_left _ (by simp)
  have hSA : ∀ x, S x ∈ A := fun x => Finset.mem_union_right _ (by simp)
  have hA : A.Nonempty := ⟨T (Classical.arbitrary α), hTA _⟩
  have : IsProbabilityMeasure (Measure.map T μ) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (Measure.map S ν) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have hμmap : Measure.map T μ = ∑ x ∈ A, (Measure.map T μ {x}) • Measure.dirac x := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map T μ) (s := A)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ A)} = (↑A : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hT A.measurableSet.compl, Set.preimage_compl]
    have huniv : T ⁻¹' (↑A : Set α) = Set.univ := by ext y; simp [hTA y]
    rw [huniv, Set.compl_univ, measure_empty]
  have hνmap : Measure.map S ν = ∑ y ∈ A, (Measure.map S ν {y}) • Measure.dirac y := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map S ν) (s := A)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ A)} = (↑A : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hS A.measurableSet.compl, Set.preimage_compl]
    have huniv : S ⁻¹' (↑A : Set α) = Set.univ := by ext y; simp [hSA y]
    rw [huniv, Set.compl_univ, measure_empty]
  let a : A → ℝ := fun i => ((Measure.map T μ) {(i : α)}).toReal
  let b : A → ℝ := fun i => ((Measure.map S ν) {(i : α)}).toReal
  have hμmass : (∑ x ∈ A, (Measure.map T μ {x})) = 1 := by
    have h1 : (∑ x ∈ A, (Measure.map T μ {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hμmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have hνmass : (∑ x ∈ A, (Measure.map S ν {x})) = 1 := by
    have h1 : (∑ x ∈ A, (Measure.map S ν {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hνmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have ha1 : ∑ i, a i = 1 := by
    rw [show (∑ i, a i) = ∑ x ∈ A, ((Measure.map T μ) {x}).toReal from
      Finset.sum_coe_sort A (fun x => ((Measure.map T μ) {x}).toReal),
      ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hμmass, ENNReal.toReal_one]
  have hb1 : ∑ i, b i = 1 := by
    rw [show (∑ i, b i) = ∑ x ∈ A, ((Measure.map S ν) {x}).toReal from
      Finset.sum_coe_sort A (fun x => ((Measure.map S ν) {x}).toReal),
      ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hνmass, ENNReal.toReal_one]
  obtain ⟨P, f, hP, hrow, hcol, hf, hval, _hmin, _hmax⟩ :=
    finite_kr_attained a b (fun i j => c i j) (fun _ => ENNReal.toReal_nonneg)
      (fun _ => ENNReal.toReal_nonneg) ha1 hb1 (fun i j => hc_nonneg i j)
      (fun i => hc_self i) (fun i j => hc_symm i j) (fun i j k => hc_triangle i j k)
  let u : α → ℝ := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else 0
  let g := finiteCTransform A hA c u
  obtain ⟨hg, hgu, hgv⟩ := finiteCTransform_properties A hA c hc_self hc_symm hc_triangle u (-u)
  have hgf : ∀ i : A, g i = f i := by
    intro i
    have hui : u i = f i := dite_eq_left i.2
    apply le_antisymm
    · have h := hgv i (fun j hj => ?_)
      · simpa only [Pi.neg_apply, neg_neg, hui] using h
      · have huj : u j = f ⟨j, hj⟩ := dite_eq_left hj
        rw [Pi.neg_apply, huj, hui]
        exact (le_abs_self _).trans (hf ⟨j, hj⟩ i)
    · simpa only [hui] using hgu i i.2
  have hint : ∀ (m : Measure α) [IsFiniteMeasure m],
      m = ∑ x ∈ A, m {x} • Measure.dirac x →
      (∫ x, g x ∂m) = ∑ i : A, (m {(i : α)}).toReal * f i := by
    intro m _ hm
    have hi : ∀ x ∈ A, Integrable g ((m {x}) • Measure.dirac x) := fun x _ =>
      (integrable_dirac (by simp)).smul_measure (measure_ne_top _ _)
    conv_lhs => rw [hm]
    rw [integral_finsetSum_measure hi]
    simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [← Finset.sum_coe_sort A (fun x => (m {x}).toReal * g x)]
    exact Finset.sum_congr rfl fun i _ => congrArg ((m {(i : α)}).toReal * ·) (hgf i)
  set π : Measure (α × α) := ∑ i : A, ∑ j : A,
    ENNReal.ofReal (P i j) • Measure.dirac ((↑i : α), (↑j : α)) with hπ_def
  have hofa : ∀ i : A, ENNReal.ofReal (a i) = Measure.map T μ {↑i} :=
    fun i => ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hofb : ∀ i : A, ENNReal.ofReal (b i) = Measure.map S ν {↑i} :=
    fun i => ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hfst : Measure.map Prod.fst π = Measure.map T μ := by
    ext E hE
    rw [Measure.map_apply measurable_fst hE, hπ_def, hμmap]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply]
    rw [← Finset.sum_coe_sort A (fun x => Measure.map T μ {x} * Set.indicator E 1 x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hind : ∀ j : A,
        Set.indicator (Prod.fst ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
          = Set.indicator E 1 (↑i : α) :=
      fun j => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP i j),
      hrow, hofa]
  have hsnd : Measure.map Prod.snd π = Measure.map S ν := by
    ext E hE
    rw [Measure.map_apply measurable_snd hE, hπ_def, hνmap]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply]
    rw [Finset.sum_comm, ← Finset.sum_coe_sort A
      (fun y => Measure.map S ν {y} * Set.indicator E 1 y)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hind : ∀ i : A,
        Set.indicator (Prod.snd ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
          = Set.indicator E 1 (↑j : α) :=
      fun i => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hP i j),
      hcol, hofb]
  have hcost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π
      = ENNReal.ofReal (∑ i : A, ∑ j : A, c i j * P i j) := by
    simp only [π, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hc_nonneg _ _) (hP i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc_nonneg _ _) (hP i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ENNReal.ofReal_mul (hP i j), mul_comm (P i j) (c (↑i) (↑j))]
  refine ⟨π, g, ⟨hfst, hsnd⟩, hg, ?_⟩
  rw [hcost, hint _ hμmap, hint _ hνmap]
  exact congrArg ENNReal.ofReal hval

private theorem wassersteinCostCoupling_le_dual_of_finiteRange
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) := by
  obtain ⟨π, g, hπ, hg, hcost⟩ :=
    finiteRange_optimal_coupling c hc_nonneg hc_self hc_symm hc_triangle μ ν T S hT hS hTfin hSfin
  exact (iInf_le_of_le π (iInf_le _ hπ)).trans
    (hcost.trans_le (le_iSup_of_le g (le_iSup_of_le hg le_rfl)))

theorem wassersteinCostCoupling_le_dual
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCostCoupling c μ ν ≤ wassersteinCost c μ ν := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _hb => ?_
  have hε4 : (0 : ℝ) < (ε : ℝ) / 4 := by positivity
  obtain ⟨T, hT, hTfin, hTcost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont
      hc_le_dist μ x₀ hμ_cm
      ((ε : ℝ) / 4) hε4
  obtain ⟨S, hS, hSfin, hScost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont
      hc_le_dist ν x₀ hν_cm
      ((ε : ℝ) / 4) hε4
  have : IsProbabilityMeasure (Measure.map T μ) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (Measure.map S ν) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  set q : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / 4) with hq
  have htri1 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    μ ν (Measure.map T μ)
  have htri2 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    (Measure.map T μ) ν (Measure.map S ν)
  have hμμ' : wassersteinCostCoupling c μ (Measure.map T μ) ≤ q :=
    (wassersteinCostCoupling_map_le c hc_cont μ T hT).trans hTcost
  have hν'ν : wassersteinCostCoupling c (Measure.map S ν) ν ≤ q := by
    rw [wassersteinCostCoupling_comm c hc_symm hc_cont.measurable (Measure.map S ν) ν]
    exact (wassersteinCostCoupling_map_le c hc_cont ν S hS).trans hScost
  have hmid : wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν + q + q :=
    (wassersteinCostCoupling_le_dual_of_finiteRange c hc_nonneg hc_self hc_symm hc_triangle
        μ ν T S hT hS hTfin hSfin).trans
      ((wassersteinCost_dual_le_add_map c hc_nonneg hc_self hc_symm hc_cont μ ν T S hT hS
          x₀ hμ_cm hν_cm).trans
        (add_le_add (add_le_add le_rfl hTcost) hScost))
  have hq4 : q + q + q + q = (ε : ℝ≥0∞) := by
    have h4 : q + q + q + q
        = ENNReal.ofReal ((ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4) := by
      rw [hq, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [h4, show (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 = (ε : ℝ) from by ring,
      ENNReal.ofReal_coe_nnreal]
  calc wassersteinCostCoupling c μ ν
      ≤ wassersteinCostCoupling c μ (Measure.map T μ)
          + wassersteinCostCoupling c (Measure.map T μ) ν := htri1
    _ ≤ q + (wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
          + wassersteinCostCoupling c (Measure.map S ν) ν) := add_le_add hμμ' htri2
    _ ≤ q + ((wassersteinCost c μ ν + q + q) + q) := add_le_add le_rfl (add_le_add hmid hν'ν)
    _ = wassersteinCost c μ ν + (q + q + q + q) := by ring
    _ = wassersteinCost c μ ν + (ε : ℝ≥0∞) := by rw [hq4]

end CostTransport
