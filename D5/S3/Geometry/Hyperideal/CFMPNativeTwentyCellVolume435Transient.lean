import D5.S3.Geometry.Hyperideal.CFMPNativeMeasureBridge435Transient
import D5.S3.Geometry.Hyperideal.CFMPTwentyCellIntegralAssembly435Transient
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPActualGramJacobian435Transient CFMPNativeMeasureBridge435Transient
open CFMPTwentyCellIntegralAssembly435Transient

namespace CFMPNativeTwentyCellVolume435Transient

-- All declarations here are temporary applications, with no retention claim.
def density (l : Fin 6 → ℝ) (z : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift3 z))^2

lemma drop_lift (z : Fin 3 → ℝ) :
    CFMPCellIntersections435Transient.drop (lift3 z) = z := by
  ext i
  fin_cases i <;> rfl

lemma chartDomain_eq_projected_body (l : Fin 6 → ℝ) : chartDomain l = K l := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨lift3 z,hz,drop_lift z⟩
  · rintro z ⟨x,hx,rfl⟩
    change lift3 (drop3 x) ∈ cutBody l
    rw [lift3_drop3 x hx.1.2]
    exact hx

lemma body_compact (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) : IsCompact (K l) := by
  exact (shared_radial_body l hl).1.image
    CFMPCellIntersections435Transient.drop.continuous_of_finiteDimensional

lemma quadratic_positive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (z : Fin 3 → ℝ) (hz : z ∈ K l) : 0 < -gramQuadratic l (lift3 z) := by
  have h : lift3 z ∈ cutBody l := by
    change z ∈ chartDomain l
    rw [chartDomain_eq_projected_body]
    exact hz
  exact neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 _ h)

lemma density_continuousOn (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    ContinuousOn (density l) (K l) := by
  have hq : Continuous (fun z : Fin 3 → ℝ => -gramQuadratic l (lift3 z)) := by
    unfold gramQuadratic lift3
    fun_prop
  unfold density
  apply continuousOn_const.div (hq.pow 2).continuousOn
  intro z hz
  exact pow_ne_zero 2 (ne_of_gt (quadratic_positive l hl z hz))

lemma density_nonnegative (l : Fin 6 → ℝ) (z : Fin 3 → ℝ) : 0 ≤ density l z :=
  div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

lemma density_integrableOn (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    IntegrableOn (density l) (K l) :=
  ContinuousOn.integrableOn_compact (body_compact l hl) (density_continuousOn l hl)

lemma density_lintegral_finite (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    (∫⁻ z in K l, ENNReal.ofReal (density l z)) < ∞ :=
  (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (density_nonnegative l))).mp
    (density_integrableOn l hl).hasFiniteIntegral

lemma density_lintegral_eq_ofReal_integral (l : Fin 6 → ℝ)
    (hl : ∀ k, 0 < l k) :
    (∫⁻ z in K l, ENNReal.ofReal (density l z)) =
      ENNReal.ofReal (∫ z in K l, density l z) :=
  (ofReal_integral_eq_lintegral_ofReal (density_integrableOn l hl)
    (Filter.Eventually.of_forall (density_nonnegative l))).symm

-- Original shared_radial_body realization and the original genuine-domain hypotheses.
example (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hgen : let c := fun k : Fin 6 => Real.cosh (l k);
      -1 < D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
        (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) ∧
      D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
        (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) < 1) :
    ∃ (c : ℝ≥0∞) (M : Matrix (Fin 4) (Fin 4) ℝ)
      (f : cutBody l → HyperbolicThreeSpace),
      c ≠ 0 ∧ c ≠ ∞ ∧
      c = (Measure.hausdorffMeasure 3 : Measure (Ambient ℂ))
        (parallelepiped (stdOrthonormalBasis ℝ (Ambient ℂ))) ∧
      (∀ i j, lorentz (M i) (M j) = lengthGram l i j) ∧ 0 < M.det ∧
      Continuous f ∧ Function.Injective f ∧ IsCompact (range f) ∧
      (range f).Nonempty ∧
      (c⁻¹ • rawNativeMeasure) (range f) =
        ∑ n : Fin 20, ∫⁻ z in C l n, ENNReal.ofReal (density l z) ∧
      (c⁻¹ • rawNativeMeasure) (range f) =
        ENNReal.ofReal (∑ n : Fin 20, ∫ z in C l n, density l z) ∧
      (c⁻¹ • rawNativeMeasure) (range f) < ∞ := by
  obtain ⟨M,hg,hM,_,f,hf,hfi,hcompact,hne,hsource⟩ :=
    (shared_radial_body l hl).2.2.2.2.2.2.2.2.2 hgen
  obtain ⟨c,hc0,hct,hcube,hcal⟩ :=
    CFMPHausdorffNormalization435Transient.normalized_native_measure_exists
  have hvol : (c⁻¹ • rawNativeMeasure) (range f) =
      ∫⁻ z in K l, ENNReal.ofReal (density l z) := by
    simpa only [density,chartDomain_eq_projected_body] using
      actual_native_volume c hcal M l hl hg hM f hfi hcompact hsource
  refine ⟨c,M,f,hc0,hct,hcube,hg,hM,hf,hfi,hcompact,hne,?_,?_,?_⟩
  · exact hvol.trans (actual_body_lintegral l hl _)
  · rw [hvol,density_lintegral_eq_ofReal_integral l hl,
      actual_body_integral l hl _ (density_integrableOn l hl)]
  · rw [hvol]
    exact density_lintegral_finite l hl

end CFMPNativeTwentyCellVolume435Transient
