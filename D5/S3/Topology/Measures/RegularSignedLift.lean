/- GID: D5/S3/Topology/Measures/RegularSignedLift
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/RegularSignedLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: construction
   digest: Regular signed-measure lifts along arbitrary compact Hausdorff continuous surjections. -/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal CompactlySupported

namespace D5.S3.Topology.Measures.RegularSignedLift
universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
variable {L : Type v} [TopologicalSpace L] [CompactSpace L]
private def pullbackCLM (p : C(K,L)) : C(L,ℝ) →L[ℝ] C(K,ℝ) :=
  p.compCLM ℝ ℝ
private def pullback (p : C(K,L)) : C(L,ℝ) →ₗ[ℝ] C(K,ℝ) :=
  (pullbackCLM p).toLinearMap
private lemma pullback_norm (p : C(K,L)) (hp : Function.Surjective p) (f : C(L,ℝ)) :
    ‖pullback p f‖ = ‖f‖ := by
  rw [pullback, pullbackCLM, ContinuousMap.norm_eq_iSup_norm,
    ContinuousMap.norm_eq_iSup_norm]
  change (⨆ x : K, ‖f (p x)‖) = ⨆ y : L, ‖f y‖
  exact hp.iSup_comp (g := fun y : L => ‖f y‖)

private def pullbackIso (p : C(K,L)) (hp : Function.Surjective p) :
    C(L,ℝ) →ₗᵢ[ℝ] C(K,ℝ) :=
  { (pullbackCLM p).toLinearMap with norm_map' := pullback_norm p hp }

private noncomputable def rangeFunctional [MeasurableSpace L] [BorelSpace L]
    (m : Measure L) [IsFiniteMeasure m]
    (p : C(K,L)) (hp : Function.Surjective p) :
    (pullbackIso p hp).range →ₗ[ℝ] ℝ where
  toFun g := ∫ x, ((pullbackIso p hp).equivRange.symm g) x ∂m
  map_add' g h := by
    simp only [map_add]
    simpa only [ContinuousMap.add_apply] using
      (integral_add
        (((pullbackIso p hp).equivRange.symm g).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (((pullbackIso p hp).equivRange.symm h).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)))
  map_smul' c g := by
    simp only [map_smul]
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
      (integral_smul c (fun x => ((pullbackIso p hp).equivRange.symm g) x))

private lemma rangeFunctional_bound [MeasurableSpace L] [BorelSpace L]
    (m : Measure L) [IsFiniteMeasure m]
    (p : C(K,L)) (hp : Function.Surjective p) (g : (pullbackIso p hp).range) :
    ‖rangeFunctional m p hp g‖ ≤ m.real univ * ‖g‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := m)
    (f := fun x => ((pullbackIso p hp).equivRange.symm g) x)
    (C := ‖((pullbackIso p hp).equivRange.symm g)‖)
    (Eventually.of_forall (fun x =>
      ((pullbackIso p hp).equivRange.symm g).norm_coe_le_norm x))
  rw [show ‖((pullbackIso p hp).equivRange.symm g)‖ = ‖g‖ by
    exact (pullbackIso p hp).equivRange.symm.norm_map g] at h
  simpa [rangeFunctional, mul_comm] using h

private noncomputable def rangeFunctionalCLM [MeasurableSpace L] [BorelSpace L]
    (m : Measure L) [IsFiniteMeasure m]
    (p : C(K,L)) (hp : Function.Surjective p) :
    (pullbackIso p hp).range →L[ℝ] ℝ :=
  (rangeFunctional m p hp).mkContinuous (m.real univ) (rangeFunctional_bound m p hp)

private lemma positive_of_norm_le_one {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (Λ : C(K,ℝ) →L[ℝ] ℝ) (hΛ : ‖Λ‖ ≤ Λ 1) :
    ∀ f : C(K,ℝ), 0 ≤ f → 0 ≤ Λ f := by
  intro f hf
  let M : ℝ := ‖f‖
  have hM : 0 ≤ M := norm_nonneg _
  have hupper (x : K) : f x ≤ M := by
    exact (le_abs_self _).trans (f.norm_coe_le_norm x)
  let u : C(K,ℝ) := M • (1 : C(K,ℝ)) - f
  have hu (x : K) : 0 ≤ u x := by
    dsimp [u]
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    linarith [hupper x]
  have hnormu : ‖u‖ ≤ M := by
    apply (ContinuousMap.norm_le u hM).2
    intro x
    rw [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, Real.norm_eq_abs]
    simp only [mul_one]
    have hu' : 0 ≤ M - f x := by
      simpa [u, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul] using hu x
    have hfx : 0 ≤ f x := hf x
    apply (abs_le).2
    constructor <;> linarith [hu', hfx, hM, hupper x]
  have hbound : Λ u ≤ Λ 1 * M := by
    have h₁ : Λ u ≤ ‖Λ‖ * ‖u‖ :=
      (le_abs_self _).trans ((Λ.le_opNorm u))
    have h₂ : ‖Λ‖ * ‖u‖ ≤ Λ 1 * M := by
      calc
        ‖Λ‖ * ‖u‖ ≤ ‖Λ‖ * M := mul_le_mul_of_nonneg_left hnormu (norm_nonneg Λ)
        _ ≤ Λ 1 * M := mul_le_mul_of_nonneg_right hΛ hM
    exact h₁.trans h₂
  have hid : Λ u = M * Λ 1 - Λ f := by
    dsimp [u]
    rw [map_sub, map_smul]
    simp only [smul_eq_mul, mul_one]
  linarith

private noncomputable def restrictionPositive
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (Λ : C(K,ℝ) →L[ℝ] ℝ) (hpos : ∀ f : C(K,ℝ), 0 ≤ f → 0 ≤ Λ f) :
    C_c(K,ℝ) →ₚ[ℝ] ℝ := by
  let lin : C_c(K,ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := by
        intro f g
        change Λ (f.toContinuousMap + g.toContinuousMap) = _
        rw [map_add]
      map_smul' := by
        intro c f
        change Λ (c • f.toContinuousMap) = _
        rw [map_smul]
        rfl }
  exact PositiveLinearMap.mk₀ lin (fun f hf => hpos f.toContinuousMap hf)

theorem exists_regular_measure_lift
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    {L : Type v} [TopologicalSpace L] [CompactSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (p : K → L) (hp : Continuous p) (hsurj : Function.Surjective p)
    (α : Measure L) [IsFiniteMeasure α] [α.Regular] :
    ∃ η : Measure K, IsFiniteMeasure η ∧ η.Regular ∧
      Measure.map p η = α ∧ η univ = α univ := by
  let pc : C(K,L) := ⟨p, hp⟩
  let F : (pullbackIso pc hsurj).range →L[ℝ] ℝ := rangeFunctionalCLM α pc hsurj
  obtain ⟨Λ, hΛext, hΛnorm⟩ :=
    exists_extension_norm_eq (pullbackIso pc hsurj).range F
  let oneL : C(L,ℝ) := 1
  let oneK : C(K,ℝ) := pullback pc oneL
  have honeK : oneK = 1 := by
    ext x
    rfl
  have honeRange : (⟨oneK, ⟨oneL, rfl⟩⟩ : (pullbackIso pc hsurj).range) =
      (pullbackIso pc hsurj).equivRange oneL := by rfl
  have hFnorm : ‖F‖ ≤ α.real univ := by
    exact F.opNorm_le_bound (measureReal_nonneg)
      (fun g => by
        change ‖rangeFunctional α pc hsurj g‖ ≤ α.real univ * ‖g‖
        exact rangeFunctional_bound α pc hsurj g)
  have hΛone : Λ 1 = α.real univ := by
    rw [← honeK]
    have hone_val : ((pullbackIso pc hsurj).equivRange oneL : C(K,ℝ)) = oneK :=
      congrArg Subtype.val honeRange
    rw [← hone_val]
    have h := hΛext ((pullbackIso pc hsurj).equivRange oneL)
    rw [h]
    simp [F, rangeFunctionalCLM, rangeFunctional, oneL, Measure.real]
  have hΛle : ‖Λ‖ ≤ Λ 1 := by
    rw [hΛnorm, hΛone]
    exact hFnorm
  let P := restrictionPositive Λ (positive_of_norm_le_one Λ hΛle)
  let η : Measure K := RealRMK.rieszMeasure P
  have hηreg : η.Regular := by infer_instance
  have hηfinite : IsFiniteMeasure η := by infer_instance
  have hηmass_real : η.real univ = α.real univ := by
    have hI := RealRMK.integral_rieszMeasure P
      ((CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ))
        (1 : C(K,ℝ)))
    have hconst : (fun x : K =>
        ((CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ))
          (1 : C(K,ℝ))) x) = fun _ => (1 : ℝ) := by
      funext x
      rfl
    rw [hconst, integral_const, smul_eq_mul, mul_one] at hI
    change η.real univ = P _ at hI
    have hPone : P ((CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ))
        (1 : C(K, ℝ))) = α.real univ := by
      change Λ 1 = α.real univ
      exact hΛone
    rw [hPone] at hI
    exact hI
  have hηmass : η univ = α univ := by
    exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp hηmass_real
  have hmapint (f : C_c(L,ℝ)) :
      ∫ y, f y ∂(Measure.map p η) = ∫ y, f y ∂α := by
    rw [integral_map hp.measurable.aemeasurable]
    · let g := (CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ))
          (pullback pc f.toContinuousMap)
      calc
        _ = ∫ x, g x ∂η := by rfl
        _ = P g := RealRMK.integral_rieszMeasure P g
        _ = _ := by
          change Λ g.toContinuousMap = _
          have hval :
              ((pullbackIso pc hsurj).equivRange f.toContinuousMap : C(K, ℝ)) =
                pullback pc f.toContinuousMap := by
            rfl
          rw [show g.toContinuousMap = pullback pc f.toContinuousMap by rfl,
            ← hval, hΛext]
          simp [F, rangeFunctionalCLM, rangeFunctional]
    · exact f.continuous.stronglyMeasurable.aestronglyMeasurable
  have hmapreg : (Measure.map p η).Regular := by
    letI : (Measure.map p η).InnerRegular := Measure.InnerRegular.map_of_continuous (μ := η) hp
    infer_instance
  have hmap : Measure.map p η = α :=
    Measure.ext_of_integral_eq_on_compactlySupported hmapint
  exact ⟨η, hηfinite, hηreg, hmap, hηmass⟩

theorem regular_jordanParts_of_regular_totalVariation
    {L : Type v} [TopologicalSpace L] [CompactSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (mu : SignedMeasure L) [mu.totalVariation.Regular] :
    mu.toJordanDecomposition.posPart.Regular ∧
      mu.toJordanDecomposition.negPart.Regular := by
  let j := mu.toJordanDecomposition
  let S := j.mutuallySingular.nullSet
  have htv : mu.totalVariation = j.posPart + j.negPart := by
    rfl
  have hpos : j.posPart = mu.totalVariation.restrict Sᶜ := by
    calc
      j.posPart = j.posPart.restrict Sᶜ :=
        j.mutuallySingular.restrict_compl_nullSet'.symm
      _ = (j.posPart + j.negPart).restrict Sᶜ := by
        rw [Measure.restrict_add, j.mutuallySingular.restrict_compl_nullSet, add_zero]
      _ = mu.totalVariation.restrict Sᶜ := by rw [← htv]
  have hneg : j.negPart = mu.totalVariation.restrict S := by
    calc
      j.negPart = j.negPart.restrict S :=
        j.mutuallySingular.restrict_nullSet'.symm
      _ = (j.posPart + j.negPart).restrict S := by
        rw [Measure.restrict_add, j.mutuallySingular.restrict_nullSet, zero_add]
      _ = mu.totalVariation.restrict S := by rw [← htv]
  have hposreg : j.posPart.Regular := by
    rw [hpos]
    exact Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)
  have hnegreg : j.negPart.Regular := by
    rw [hneg]
    exact Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)
  exact ⟨by simpa [j] using hposreg, by simpa [j] using hnegreg⟩

private theorem regular_add
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    {μ ν : Measure K} [μ.Regular] [ν.Regular] : (μ + ν).Regular := by
  let hOuter : Measure.OuterRegular (μ + ν) := by
    refine ⟨fun A hA r hr => ?_⟩
    rw [Measure.coe_add, Pi.add_apply] at hr
    rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨rμ, hrμ, rν, hrν, hsum⟩
    obtain ⟨U, hAU, hUopen, hU⟩ := Set.exists_isOpen_lt_of_lt A rμ hrμ
    obtain ⟨V, hAV, hVopen, hV⟩ := Set.exists_isOpen_lt_of_lt A rν hrν
    refine ⟨U ∩ V, (fun x hx => ⟨hAU hx, hAV hx⟩), hUopen.inter hVopen, ?_⟩
    rw [Measure.coe_add, Pi.add_apply]
    calc
      μ (U ∩ V) + ν (U ∩ V) ≤ μ U + ν V :=
        add_le_add (measure_mono inter_subset_left) (measure_mono inter_subset_right)
      _ < rμ + rν := ENNReal.add_lt_add hU hV
      _ < r := hsum
  let hInner : Measure.InnerRegular (μ + ν) := inferInstance
  exact {
    toIsFiniteMeasureOnCompacts := inferInstance
    outerRegular := hOuter.outerRegular
    innerRegular := fun U hU r hr => hInner.innerRegular hU.measurableSet r hr }

theorem exists_regular_normPreserving_signedMeasure_lift
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K]
    {L : Type v} [TopologicalSpace L] [CompactSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (p : K → L) (hp : Continuous p) (hsurj : Function.Surjective p)
    (mu : SignedMeasure L) [mu.totalVariation.Regular] :
    ∃ nu : SignedMeasure K, nu.totalVariation.Regular ∧
      nu.map p = mu ∧ nu.totalVariation univ = mu.totalVariation univ := by
  let j := mu.toJordanDecomposition
  let S := j.mutuallySingular.nullSet
  have hS : MeasurableSet S := j.mutuallySingular.measurableSet_nullSet
  have htv : mu.totalVariation = j.posPart + j.negPart := by
    rfl
  obtain ⟨hposreg, hnegreg⟩ := regular_jordanParts_of_regular_totalVariation mu
  letI : j.posPart.Regular := hposreg
  letI : j.negPart.Regular := hnegreg
  obtain ⟨etaPlus, hetaPlusFinite, hetaPlusReg, hetaPlusMap, hetaPlusMass⟩ :=
    exists_regular_measure_lift p hp hsurj j.posPart
  obtain ⟨etaMinus, hetaMinusFinite, hetaMinusReg, hetaMinusMap, hetaMinusMass⟩ :=
    exists_regular_measure_lift p hp hsurj j.negPart
  let jeta : JordanDecomposition K :=
    { posPart := etaPlus
      negPart := etaMinus
      mutuallySingular := by
        refine ⟨p ⁻¹' S, hp.measurable hS, ?_, ?_⟩
        · calc
            etaPlus (p ⁻¹' S) = (Measure.map p etaPlus) S :=
              (Measure.map_apply hp.measurable hS).symm
            _ = j.posPart S := by rw [hetaPlusMap]
            _ = 0 := j.mutuallySingular.measure_nullSet
        · calc
            etaMinus (p ⁻¹' S)ᶜ = etaMinus (p ⁻¹' Sᶜ) := by rw [preimage_compl]
            _ = (Measure.map p etaMinus) Sᶜ := (Measure.map_apply hp.measurable hS.compl).symm
            _ = j.negPart Sᶜ := by rw [hetaMinusMap]
            _ = 0 := j.mutuallySingular.measure_compl_nullSet }
  let nu : SignedMeasure K := jeta.toSignedMeasure
  have hnuJordan : nu.toJordanDecomposition = jeta := by
    simpa [nu] using JordanDecomposition.toJordanDecomposition_toSignedMeasure jeta
  have hnuTV : nu.totalVariation = etaPlus + etaMinus := by
    rw [SignedMeasure.totalVariation, hnuJordan]
  have hnuReg : nu.totalVariation.Regular := by
    rw [hnuTV]
    letI : etaPlus.Regular := hetaPlusReg
    letI : etaMinus.Regular := hetaMinusReg
    exact regular_add
  have hplusSigned : (etaPlus.toSignedMeasure).map p = j.posPart.toSignedMeasure := by
    apply VectorMeasure.ext
    intro A hA
    rw [VectorMeasure.map_apply _ hp.measurable hA,
      Measure.toSignedMeasure_apply_measurable (hp.measurable hA),
      Measure.toSignedMeasure_apply_measurable hA]
    have hm := Measure.map_apply (μ := etaPlus) hp.measurable hA
    rw [hetaPlusMap] at hm
    simpa [Measure.real] using congrArg ENNReal.toReal hm.symm
  have hminusSigned : (etaMinus.toSignedMeasure).map p = j.negPart.toSignedMeasure := by
    apply VectorMeasure.ext
    intro A hA
    rw [VectorMeasure.map_apply _ hp.measurable hA,
      Measure.toSignedMeasure_apply_measurable (hp.measurable hA),
      Measure.toSignedMeasure_apply_measurable hA]
    have hm := Measure.map_apply (μ := etaMinus) hp.measurable hA
    rw [hetaMinusMap] at hm
    simpa [Measure.real] using congrArg ENNReal.toReal hm.symm
  have hnuMap : nu.map p = mu := by
    apply VectorMeasure.ext
    intro A hA
    change (jeta.toSignedMeasure).map p A = mu A
    rw [VectorMeasure.map_apply _ hp.measurable hA]
    change (etaPlus.toSignedMeasure - etaMinus.toSignedMeasure) (p ⁻¹' A) = mu A
    rw [Measure.toSignedMeasure_sub_apply (hp.measurable hA)]
    have hplusA := congrArg (fun q : SignedMeasure L => q A) hplusSigned
    have hminusA := congrArg (fun q : SignedMeasure L => q A) hminusSigned
    rw [VectorMeasure.map_apply (etaPlus.toSignedMeasure) hp.measurable hA,
      Measure.toSignedMeasure_apply_measurable (hp.measurable hA),
      Measure.toSignedMeasure_apply_measurable hA] at hplusA
    rw [VectorMeasure.map_apply (etaMinus.toSignedMeasure) hp.measurable hA,
      Measure.toSignedMeasure_apply_measurable (hp.measurable hA),
      Measure.toSignedMeasure_apply_measurable hA] at hminusA
    rw [hplusA, hminusA]
    exact (mu.apply_eq_posPart_real_sub_negPart_real hA).symm
  have hnuMass : nu.totalVariation univ = mu.totalVariation univ := by
    rw [hnuTV, Measure.coe_add, Pi.add_apply, hetaPlusMass, hetaMinusMass]
    exact congrArg (fun m : Measure L => m univ) htv.symm
  exact ⟨nu, hnuReg, hnuMap, hnuMass⟩
end D5.S3.Topology.Measures.RegularSignedLift
