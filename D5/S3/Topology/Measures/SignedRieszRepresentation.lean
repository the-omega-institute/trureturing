/- GID: D5/S3/Topology/Measures/SignedRieszRepresentation
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedRieszRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary real continuous functionals have regular signed representatives with exact total variation norm. -/

import D5.S3.Topology.Measures.NormPreservingLifts
import D5.S3.Topology.Measures.RegularSignedLift
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped Topology ENNReal CompactlySupported

namespace D5.S3.Topology.Measures.SignedRieszRepresentation

universe u

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

private def orderUnitMap : (C(K, ℝ) × ℝ) →ₗ[ℝ] C(K ⊕ K, ℝ) where
  toFun z := ⟨Sum.elim (fun x => z.2 + z.1 x) (fun x => z.2 - z.1 x),
    (continuous_const.add z.1.continuous).sumElim
      (continuous_const.sub z.1.continuous)⟩
  map_add' a b := by
    ext x
    cases x <;> simp <;> ring
  map_smul' c a := by
    ext x
    cases x <;> simp <;> ring

private lemma orderUnitMap_norm [Nonempty K] (z : C(K, ℝ) × ℝ) :
    ‖orderUnitMap z‖ = |z.2| + ‖z.1‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    cases x with
    | inl x =>
      exact (norm_add_le z.2 (z.1 x)).trans
        (by simpa only [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using
          add_le_add_left (z.1.norm_coe_le_norm x) ‖z.2‖)
    | inr x =>
      exact (norm_sub_le z.2 (z.1 x)).trans
        (by simpa only [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc] using
          add_le_add_left (z.1.norm_coe_le_norm x) ‖z.2‖)
  · have hx (x : K) : |z.2| + |z.1 x| ≤ ‖orderUnitMap z‖ := by
      have hl := (orderUnitMap z).norm_coe_le_norm (Sum.inl x)
      have hr := (orderUnitMap z).norm_coe_le_norm (Sum.inr x)
      change |z.2 + z.1 x| ≤ _ at hl
      change |z.2 - z.1 x| ≤ _ at hr
      rcases le_total 0 z.2 with ht | ht <;>
        rcases le_total 0 (z.1 x) with hf | hf
      · rw [abs_of_nonneg ht, abs_of_nonneg hf]
        rw [abs_of_nonneg (by linarith)] at hl
        exact hl
      · rw [abs_of_nonneg ht, abs_of_nonpos hf]
        rw [abs_of_nonneg (by linarith)] at hr
        linarith
      · rw [abs_of_nonpos ht, abs_of_nonneg hf]
        rw [abs_of_nonpos (by linarith)] at hr
        linarith
      · rw [abs_of_nonpos ht, abs_of_nonpos hf]
        rw [abs_of_nonpos (by linarith)] at hl
        linarith
    have hf : ‖z.1‖ ≤ ‖orderUnitMap z‖ - |z.2| := by
      apply (ContinuousMap.norm_le_of_nonempty _).2
      intro x
      simpa only [Real.norm_eq_abs] using (le_sub_iff_add_le.mpr (by linarith [hx x]))
    linarith

private lemma orderUnitMap_injective [Nonempty K] :
    Function.Injective (orderUnitMap (K := K)) := by
  intro z w hzw
  have hz : orderUnitMap (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hn : |(z - w).2| + ‖(z - w).1‖ = 0 := by
    rw [← orderUnitMap_norm, hz, norm_zero]
  have hf : (z - w).1 = 0 :=
    norm_eq_zero.mp (by linarith [abs_nonneg (z - w).2, norm_nonneg (z - w).1])
  have ht : (z - w).2 = 0 :=
    abs_eq_zero.mp (by linarith [abs_nonneg (z - w).2, norm_nonneg (z - w).1])
  exact sub_eq_zero.mp (Prod.ext hf ht)

private noncomputable def leftInclusion : C(K, ℝ) →L[ℝ] C(K ⊕ K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨Sum.elim f (fun _ => 0), f.continuous.sumElim continuous_const⟩
      map_add' := by intro f g; ext x; cases x <;> simp
      map_smul' := by intro c f; ext x; cases x <;> simp }
    1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro x
      cases x with
      | inl x => exact f.norm_coe_le_norm x
      | inr x => simpa using norm_nonneg f)

private noncomputable def rightInclusion : C(K, ℝ) →L[ℝ] C(K ⊕ K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨Sum.elim (fun _ => 0) f, continuous_const.sumElim f.continuous⟩
      map_add' := by intro f g; ext x; cases x <;> simp
      map_smul' := by intro c f; ext x; cases x <;> simp }
    1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro x
      cases x with
      | inl x => simpa using norm_nonneg f
      | inr x => exact f.norm_coe_le_norm x)

private theorem positive_decomposition [Nonempty K] (F : StrongDual ℝ C(K, ℝ)) :
    ∃ P Q : StrongDual ℝ C(K, ℝ),
      (∀ f, 0 ≤ f → 0 ≤ P f) ∧ (∀ f, 0 ≤ f → 0 ≤ Q f) ∧
      (∀ f, P f - Q f = F f) ∧ P 1 + Q 1 = ‖F‖ := by
  let E := LinearEquiv.ofInjective (orderUnitMap (K := K)) orderUnitMap_injective
  let L₀ : (C(K, ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    F.toLinearMap.comp (LinearMap.fst ℝ _ _) +
      ‖F‖ • LinearMap.snd ℝ _ _
  let Llin := L₀.comp E.symm.toLinearMap
  have hb (z : (orderUnitMap (K := K)).range) : ‖Llin z‖ ≤ ‖F‖ * ‖z‖ := by
    have hz : ‖z‖ = |(E.symm z).2| + ‖(E.symm z).1‖ := by
      have h := orderUnitMap_norm (E.symm z)
      have heq : orderUnitMap (E.symm z) = (z : C(K ⊕ K, ℝ)) :=
        congrArg Subtype.val (E.apply_symm_apply z)
      rw [heq] at h
      exact h
    change ‖F (E.symm z).1 + ‖F‖ * (E.symm z).2‖ ≤ _
    calc
      _ ≤ ‖F (E.symm z).1‖ + ‖‖F‖ * (E.symm z).2‖ := norm_add_le _ _
      _ ≤ ‖F‖ * ‖(E.symm z).1‖ + ‖F‖ * |(E.symm z).2| := by
        apply add_le_add
        · exact F.le_opNorm (E.symm z).1
        · simpa only [norm_mul, norm_norm, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg F)] using
            (le_refl (‖F‖ * |(E.symm z).2|))
      _ = ‖F‖ * ‖z‖ := by rw [hz]; ring
  let L : StrongDual ℝ (orderUnitMap (K := K)).range := Llin.mkContinuous ‖F‖ hb
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (orderUnitMap (K := K)).range L
  have hGJ (z : C(K, ℝ) × ℝ) : G (orderUnitMap z) = F z.1 + ‖F‖ * z.2 := by
    have h := hG (E z)
    change G (orderUnitMap z) = L₀ (E.symm (E z)) at h
    simpa [L₀] using h
  have hGone : G 1 = ‖F‖ := by
    have hJ : orderUnitMap ((0 : C(K, ℝ)), (1 : ℝ)) = 1 := by
      ext x
      cases x <;> simp [orderUnitMap]
    simpa only [hJ, map_zero, zero_add, mul_one] using hGJ (0, 1)
  have hGpos : ∀ f, 0 ≤ f → 0 ≤ G f :=
    RegularSignedLift.positive_of_norm_le_one G (by
      rw [hGn, hGone]
      exact Llin.mkContinuous_norm_le (norm_nonneg F) hb)
  refine ⟨G.comp leftInclusion, G.comp rightInclusion, ?_, ?_, ?_, ?_⟩
  · intro f hf
    apply hGpos
    intro x
    cases x with
    | inl x => exact hf x
    | inr x => exact le_rfl
  · intro f hf
    apply hGpos
    intro x
    cases x with
    | inl x => exact le_rfl
    | inr x => exact hf x
  · intro f
    change G (leftInclusion f) - G (rightInclusion f) = F f
    rw [← map_sub]
    have hJ : leftInclusion f - rightInclusion f = orderUnitMap (f, 0) := by
      ext x
      cases x <;> simp [leftInclusion, rightInclusion, orderUnitMap]
    rw [hJ, hGJ]
    simp
  · change G (leftInclusion 1) + G (rightInclusion 1) = ‖F‖
    rw [← map_add]
    have hone : leftInclusion (1 : C(K, ℝ)) + rightInclusion 1 = 1 := by
      ext x
      cases x <;> simp [leftInclusion, rightInclusion]
    rw [hone, hGone]

private theorem regular_of_le_finite
    {α : Type u} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [R1Space α] {ρ σ : Measure α}
    [IsFiniteMeasure σ] [Measure.InnerRegularCompactLTTop σ]
    (hρσ : ρ ≤ σ) : Measure.Regular ρ := by
  letI : IsFiniteMeasure ρ := isFiniteMeasure_of_le σ hρσ
  letI : Measure.InnerRegular ρ := ⟨by
    intro A hA r hr
    let δ := ρ A - r
    have hδ : δ ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hr)
    obtain ⟨C, hCA, hCc, hCcl, hC⟩ :=
      hA.exists_isCompact_isClosed_sdiff_lt (μ := σ) (measure_ne_top σ A) hδ
    refine ⟨C, hCA, hCc, ?_⟩
    by_contra h
    have hCr : ρ C ≤ r := le_of_not_gt h
    have hsmall : ρ (A \ C) < δ := (hρσ (A \ C)).trans_lt hC
    have hpart : ρ (A \ C) + ρ C = ρ A := by
      simpa only [inter_eq_right.mpr hCA] using
        (measure_sdiff_add_inter (μ := ρ) A hCcl.measurableSet)
    have hlt : ρ A < δ + r := calc
      ρ A = ρ (A \ C) + ρ C := hpart.symm
      _ < δ + ρ C := ENNReal.add_lt_add_right (measure_ne_top ρ C) hsmall
      _ ≤ δ + r := by simpa only [add_comm] using add_le_add_left hCr δ
    exact (ne_of_lt hlt) (tsub_add_cancel_of_le hr.le).symm⟩
  infer_instance

variable [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- Real signed Riesz representation with regular total variation and exact norm,
    for every continuous linear functional, including on an empty carrier. -/
private theorem exists_regular_signedMeasure_representation (F : StrongDual ℝ C(K, ℝ)) :
    ∃ s : SignedMeasure K, s.totalVariation.Regular ∧
      NormPreservingLifts.signedFunctional s = F ∧
      s.totalVariation.real univ = ‖F‖ := by
  classical
  by_cases hK : Nonempty K
  · letI := hK
    obtain ⟨P, Q, hP, hQ, hPQ, hmass⟩ := positive_decomposition F
    let μ := RealRMK.rieszMeasure (RegularSignedLift.restrictionPositive P hP)
    let ν := RealRMK.rieszMeasure (RegularSignedLift.restrictionPositive Q hQ)
    have hμ (f : C(K, ℝ)) : (∫ x, f x ∂μ) = P f := by
      change (∫ x, f x ∂RealRMK.rieszMeasure
        (RegularSignedLift.restrictionPositive P hP)) = P f
      convert RealRMK.integral_rieszMeasure (RegularSignedLift.restrictionPositive P hP)
        ((CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ)) f) using 1 <;>
        rfl
    have hν (f : C(K, ℝ)) : (∫ x, f x ∂ν) = Q f := by
      change (∫ x, f x ∂RealRMK.rieszMeasure
        (RegularSignedLift.restrictionPositive Q hQ)) = Q f
      convert RealRMK.integral_rieszMeasure (RegularSignedLift.restrictionPositive Q hQ)
        ((CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ)) f) using 1 <;>
        rfl
    have hmass' : μ.real univ + ν.real univ = ‖F‖ := by
      have hp := hμ 1
      have hq := hν 1
      simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at hp hq
      rw [hp, hq]
      exact hmass
    let s := μ.toSignedMeasure - ν.toSignedMeasure
    have hdom : s.totalVariation ≤ μ + ν :=
      NormPreservingLifts.totalVariation_sub_toSignedMeasure_le μ ν
    have hreg : s.totalVariation.Regular := regular_of_le_finite hdom
    have hrep : NormPreservingLifts.signedFunctional s = F := by
      ext f
      rw [NormPreservingLifts.signedFunctional_sub_toSignedMeasure, hμ, hν, hPQ]
    refine ⟨s, hreg, hrep, le_antisymm ?_ ?_⟩
    · calc
        s.totalVariation.real univ ≤ (μ + ν).real univ :=
          ENNReal.toReal_mono (measure_ne_top _ _) (hdom univ)
        _ = μ.real univ + ν.real univ := measureReal_add_apply
        _ = ‖F‖ := hmass'
    · rw [← hrep]
      exact NormPreservingLifts.signedFunctional_norm_le s
  · letI : IsEmpty K := not_nonempty_iff.mp hK
    have hF : F = 0 := Subsingleton.elim _ _
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [SignedMeasure.totalVariation_zero]
      infer_instance
    · exact Subsingleton.elim _ _
    · simp [hF, SignedMeasure.totalVariation_zero, Measure.real]

/-- Regular signed measures are determined by their continuous integrals. -/
private theorem regular_signedMeasure_unique (s t : SignedMeasure K)
    (hs : s.totalVariation.Regular) (ht : t.totalVariation.Regular)
    (hfun : NormPreservingLifts.signedFunctional s =
      NormPreservingLifts.signedFunctional t) : s = t := by
  letI := hs
  letI := ht
  obtain ⟨hsa, hsb⟩ := RegularSignedLift.regular_jordanParts_of_regular_totalVariation s
  obtain ⟨htd, hte⟩ := RegularSignedLift.regular_jordanParts_of_regular_totalVariation t
  let a := s.toJordanDecomposition.posPart
  let b := s.toJordanDecomposition.negPart
  let d := t.toJordanDecomposition.posPart
  let e := t.toJordanDecomposition.negPart
  letI : a.Regular := hsa
  letI : b.Regular := hsb
  letI : d.Regular := htd
  letI : e.Regular := hte
  have hsrec : a.toSignedMeasure - b.toSignedMeasure = s :=
    s.toSignedMeasure_toJordanDecomposition
  have htrec : d.toSignedMeasure - e.toSignedMeasure = t :=
    t.toSignedMeasure_toJordanDecomposition
  have hsum : a + e = b + d := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    have h := DFunLike.congr_fun hfun f.toContinuousMap
    rw [← hsrec, ← htrec,
      NormPreservingLifts.signedFunctional_sub_toSignedMeasure,
      NormPreservingLifts.signedFunctional_sub_toSignedMeasure] at h
    rw [integral_add_measure f.integrable f.integrable,
      integral_add_measure f.integrable f.integrable]
    change (∫ x, f x ∂a) - (∫ x, f x ∂b) =
      (∫ x, f x ∂d) - (∫ x, f x ∂e) at h
    linarith
  have h := Measure.toSignedMeasure_congr hsum
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at h
  rw [← hsrec, ← htrec]
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h)

/-- The real signed Riesz–Markov–Kakutani theorem: continuous integrals determine
regular signed measures, every such measure has its exact variation norm, and
all continuous linear functionals have a regular signed representative. -/
theorem signed_riesz_markov_kakutani :
    (∀ s t : SignedMeasure K, s.totalVariation.Regular → t.totalVariation.Regular →
      NormPreservingLifts.signedFunctional s = NormPreservingLifts.signedFunctional t → s = t) ∧
    (∀ s : SignedMeasure K, s.totalVariation.Regular →
      s.totalVariation.real univ = ‖NormPreservingLifts.signedFunctional s‖) ∧
    (∀ F : StrongDual ℝ C(K, ℝ), ∃ s : SignedMeasure K, s.totalVariation.Regular ∧
      NormPreservingLifts.signedFunctional s = F ∧ s.totalVariation.real univ = ‖F‖) := by
  refine ⟨regular_signedMeasure_unique, ?_, exists_regular_signedMeasure_representation⟩
  intro s hs
  obtain ⟨t, ht, hrep, hnorm⟩ :=
    exists_regular_signedMeasure_representation (NormPreservingLifts.signedFunctional s)
  have hts : t = s := regular_signedMeasure_unique t s ht hs hrep
  simpa only [hts] using hnorm

end D5.S3.Topology.Measures.SignedRieszRepresentation
