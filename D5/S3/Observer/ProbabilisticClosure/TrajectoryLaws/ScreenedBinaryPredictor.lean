/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ScreenedBinaryPredictor
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ScreenedBinaryPredictor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditioning within a screened pair gives a total bounded bit predictor. -/

import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal MeasureTheory ProbabilityTheory Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ScreenedBinaryPredictor

private theorem disintegrate_independent_pair
    {Q U V : Type*} [MeasurableSpace Q] [MeasurableSpace U] [MeasurableSpace V]
    [MeasurableSpace.CountableOrCountablyGenerated Q V]
    (η : Kernel Q U) [IsMarkovKernel η] (κ : Kernel Q (V × Bool)) [IsMarkovKernel κ] :
    (η ×ₖ κ).map MeasurableEquiv.prodAssoc.symm =
      (η ×ₖ κ.fst) ⊗ₖ (κ.condKernel.comap (fun z : Q × (U × V) => (z.1,z.2.2)) (by fun_prop)) := by
  ext a : 1
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  rw [Kernel.map_apply _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
  apply Measure.ext_prod₃
  intro A B C hA hB hC
  rw [Kernel.prod_apply_prod, Measure.map_apply (by fun_prop) (hA.prod (hB.prod hC))]
  have he : MeasurableEquiv.prodAssoc ⁻¹' (A ×ˢ B ×ˢ C) = (A ×ˢ B) ×ˢ C := by
    ext z
    simp [MeasurableEquiv.prodAssoc,and_assoc]
  rw [he, Kernel.compProd_apply_prod (hA.prod hB) hC]
  simp only [Kernel.comap_apply, Kernel.prod_apply]
  have hm : Measurable (fun b : U × V => κ.condKernel (a,b.2) C) :=
    (Kernel.measurable_coe κ.condKernel hC).comp (measurable_const.prodMk measurable_snd)
  rw [setLIntegral_prod _ hm.aemeasurable]
  simp only
  have hdis := congrArg (fun k : Kernel Q (V × Bool) => k a (B ×ˢ C)) (Kernel.disintegrate κ κ.condKernel)
  rw [Kernel.compProd_apply_prod hB hC] at hdis
  rw [hdis, lintegral_const]
  simp only [Measure.restrict_apply_univ, mul_comm]

/-- A binary conditional mean under screening has a measurable version defined
and bounded on every class/exterior pair, even a pair of zero actual mass. -/
theorem screened_binary_predictor
    {Ω Q U V : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    [MeasurableSpace.CountableOrCountablyGenerated Q V]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (u : Ω → U) (v : Ω → V) (x : Ω → Bool)
    (hq : Measurable q) (hu : Measurable u) (hv : Measurable v) (hx : Measurable x)
    (hI : CondIndepFun (MeasurableSpace.comap q inferInstance) hq.comap_le
      u (fun ω => (v ω,x ω)) μ) :
    ∃ g : Q × V → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      μ[fun ω => if x ω then (1 : ℝ) else 0 |
        MeasurableSpace.comap (fun ω => (q ω,(u ω,v ω))) inferInstance] =ᵐ[μ]
        fun ω => g (q ω,v ω) := by
  let η := condDistrib u q μ
  let κ := condDistrib (fun ω => (v ω,x ω)) q μ
  let δ := κ.condKernel.comap (fun z : Q × (U × V) => (z.1,z.2.2)) (by fun_prop)
  have hfull : μ.map (fun ω => (q ω,(u ω,(v ω,x ω)))) = μ.map q ⊗ₘ (η ×ₖ κ) := by
    have he := (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
      hu (hv.prodMk hx) hq).mp hI
    rwa [← Measure.compProd_eq_comp_prod] at he
  have he : μ.map (fun ω => ((q ω,(u ω,v ω)),x ω)) =
      (μ.map q ⊗ₘ (η ×ₖ κ.fst)) ⊗ₘ δ := by
    rw [← Measure.compProd_assoc]
    rw [← disintegrate_independent_pair η κ]
    rw [Measure.compProd_map MeasurableEquiv.prodAssoc.symm.measurable, ← hfull,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hbase : μ.map (fun ω => (q ω,(u ω,v ω))) = μ.map q ⊗ₘ (η ×ₖ κ.fst) := by
    have hh := congrArg Measure.fst he
    rw [Measure.fst_map_prodMk (hq.prodMk (hu.prodMk hv)) hx,
      Measure.fst_compProd] at hh
    exact hh
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hq.prodMk (hu.prodMk hv)) hx (he.trans (by rw [hbase]))
  have ha : ∀ᵐ ω ∂μ, condDistrib x (fun ω => (q ω,(u ω,v ω))) μ
      (q ω,(u ω,v ω)) = δ (q ω,(u ω,v ω)) :=
    ae_of_ae_map (hq.prodMk (hu.prodMk hv)).aemeasurable hcond
  refine ⟨fun z => (κ.condKernel z).real {true},
    (Kernel.measurable_coe _ (measurableSet_singleton true)).ennreal_toReal,?_,?_⟩
  · intro z
    exact ⟨ENNReal.toReal_nonneg,
      by simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using
        (measureReal_mono (μ := κ.condKernel z) (Set.subset_univ {true}))⟩
  · have hp := condDistrib_ae_eq_condExp (μ := μ) (hq.prodMk (hu.prodMk hv)) hx
      (measurableSet_singleton true)
    have hi : (x ⁻¹' {true}).indicator (fun _ => (1 : ℝ)) =
        (fun ω => if x ω then (1 : ℝ) else 0) := by
      ext ω
      cases heq : x ω <;> simp [heq]
    rw [hi] at hp
    filter_upwards [ha,hp] with ω hω hωp
    rw [← hωp,hω]
    rfl

#print axioms screened_binary_predictor

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ScreenedBinaryPredictor
