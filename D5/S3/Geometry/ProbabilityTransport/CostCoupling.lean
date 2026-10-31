/- GID: D5/S3/Geometry/ProbabilityTransport/CostCoupling
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/CostCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General cost Kantorovich Rubinstein transport -/
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
