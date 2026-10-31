/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleTheorem42
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleTheorem42
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native closed-component rectangle bounds and both original geometric tails. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectanglePosteriors
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleRoutes
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarErasureTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Filter
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectanglePosteriors
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarErasureTail
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleTheorem42
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/- The root tail is the source's A_P(R); `erasureTail` is its squared tau_P(R).
   The summands use the risks from OriginalErasureComparison verbatim. -/
def rootErasureTail (θ : Presentation H) (R : ℕ) : ℝ :=
  ∑' n : ℕ, (Real.sqrt (leftRisk θ (R+n)) + Real.sqrt (rightRisk θ (R+n)))

private theorem native_visible_pushforward (κ : Presentation H)
    (K : Measure (PathSpace H))
    (hK : K = (jointLaw κ : Measure (PathSpace H))) :
    K.map Prod.snd = (visibleLaw κ : Measure (ℤ → Bool)) := by
  subst K
  change ((retainedLaw κ : Measure (PathSpace (Positive κ))).map (includePath κ)).map Prod.snd = _
  rw [Measure.map_map measurable_snd (inclusion_measurable κ)]
  exact (same_law_trimming κ).2.2.2.1

private theorem native_component_irreducible
    (θ : Presentation H)
    (D : FiniteClosedClasses.ClosedClass (θ.matrix false + θ.matrix true))
    (hc : 0 < ∑ i : D.val, θ.initial i.val) :
    ∀ i j : D.val, ∃ n : ℕ,
      0 < ((nativeComponent θ D hc).matrix false +
        (nativeComponent θ D hc).matrix true)^n i j := by
  let T := θ.matrix false + θ.matrix true
  have hT : T ∈ rowStochastic ℝ H := Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨fun i j => add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _), θ.stochastic⟩
  have hi : IsIrreducible (FiniteClosedClasses.restriction T D.val) :=
    (FiniteClosedClasses.actual_structure T hT).class_irreducible D
  have hκ : IsIrreducible ((nativeComponent θ D hc).matrix false +
      (nativeComponent θ D hc).matrix true) := by
    simpa [nativeComponent, FiniteClosedClasses.restriction, Matrix.add_apply] using hi
  have hnonneg : ∀ i j : D.val,
      0 ≤ ((nativeComponent θ D hc).matrix false +
        (nativeComponent θ D hc).matrix true) i j := by
    intro i j
    exact add_nonneg ((nativeComponent θ D hc).matrix_nonneg false i j)
      ((nativeComponent θ D hc).matrix_nonneg true i j)
  exact (Matrix.isIrreducible_iff_exists_pow_pos hnonneg).mp hκ

private theorem component_rho_range {S : Type u} [Fintype S]
    (B : Matrix S S ℝ) (R : Rectangle B) :
    0 ≤ 1 - rectangleMinimum B R / rectangleMaximum B R ∧
      1 - rectangleMinimum B R / rectangleMaximum B R < 1 := by
  let S := (R.rows ×ˢ R.cols).image fun ij => B ij.1 ij.2
  have hS : S.Nonempty := (R.rows_nonempty.product R.cols_nonempty).image _
  have hu : 0 < rectangleMinimum B R := by
    obtain ⟨ij, hij, he⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    change 0 < S.min' hS
    rw [← he]
    exact R.positive ij.1 (Finset.mem_product.mp hij).1 ij.2
      (Finset.mem_product.mp hij).2
  have huv : rectangleMinimum B R ≤ rectangleMaximum B R := Finset.min'_le_max' hS
  have hv : 0 < rectangleMaximum B R := hu.trans_le huv
  exact ⟨sub_nonneg.mpr ((div_le_one hv).mpr huv),
    sub_lt_self _ (div_pos hu hv)⟩

private theorem geometric_root_tail
    (b : ℕ) (hb : 0 < b) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (eL eR : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ eL n ∧ 0 ≤ eR n)
    (hbound : ∀ n, eL n ≤ η^(n/b) ∧ eR n ≤ η^(n/b)) (R : ℕ) :
    Summable (fun n => Real.sqrt (eL (R+n)) + Real.sqrt (eR (R+n))) ∧
      (∑' n, Real.sqrt (eL (R+n)) + Real.sqrt (eR (R+n))) ≤
        2 * (b : ℝ) * (Real.sqrt η)^(R/b) / (1-Real.sqrt η) := by
  have hsη0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have hsη1 : Real.sqrt η < 1 := by
    rw [Real.sqrt_lt_iff]
    exact ⟨hη0, by nlinarith [hη1]⟩
  have hseries := tail_series (1 : ℝ) (Real.sqrt η) (by norm_num) hsη0 hsη1 b hb R
  have hsqrt (n : ℕ) (h : 0 ≤ eL (R+n)) :
      Real.sqrt (eL (R+n)) ≤ (Real.sqrt η)^((R+n)/b) := by
    calc
      Real.sqrt (eL (R+n)) ≤ Real.sqrt (η^((R+n)/b)) :=
        Real.sqrt_le_sqrt (hbound (R+n)).1
      _ = (Real.sqrt η)^((R+n)/b) := by rw [Real.sqrt_pow]
  have hsqrt' (n : ℕ) (h : 0 ≤ eR (R+n)) :
      Real.sqrt (eR (R+n)) ≤ (Real.sqrt η)^((R+n)/b) := by
    calc
      Real.sqrt (eR (R+n)) ≤ Real.sqrt (η^((R+n)/b)) :=
        Real.sqrt_le_sqrt (hbound (R+n)).2
      _ = (Real.sqrt η)^((R+n)/b) := by rw [Real.sqrt_pow]
  have hpoint (n : ℕ) :
      Real.sqrt (eL (R+n)) + Real.sqrt (eR (R+n)) ≤
        2 * (Real.sqrt η)^((R+n)/b) := by
    exact add_le_add (hsqrt n (hnonneg (R+n)).1) (hsqrt' n (hnonneg (R+n)).2)
  have hnon (n : ℕ) : 0 ≤ Real.sqrt (eL (R+n)) + Real.sqrt (eR (R+n)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : Summable (fun n => Real.sqrt (eL (R+n)) + Real.sqrt (eR (R+n))) :=
    Summable.of_nonneg_of_le hnon hpoint (hseries.1.mul_left 2)
  refine ⟨hsum, (hsum.tsum_le_tsum hpoint (hseries.1.mul_left 2)).trans_eq ?_⟩
  rw [← tsum_mul_left]
  calc
    2 * ∑' n : ℕ, (Real.sqrt η)^((R+n)/b) ≤
        2 * ((b : ℝ)/(1-Real.sqrt η) * (Real.sqrt η)^(R/b)) :=
      mul_le_mul_of_nonneg_left hseries.2 (by norm_num)
    _ = 2 * (b : ℝ) * (Real.sqrt η)^(R/b) / (1-Real.sqrt η) := by ring

private theorem geometric_square_tail
    (b : ℕ) (hb : 0 < b) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (eL eR : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ eL n ∧ 0 ≤ eR n)
    (hbound : ∀ n, eL n ≤ η^(n/b) ∧ eR n ≤ η^(n/b)) (R : ℕ) :
    ∑' n : ℕ, (ENNReal.ofReal (eL (R+n)) + ENNReal.ofReal (eR (R+n))) ≤
      ENNReal.ofReal (2 * (b : ℝ) * η^(R/b) / (1-η)) := by
  have hseries := tail_series (1 : ℝ) η (by norm_num) hη0 hη1 b hb R
  have hpoint (n : ℕ) :
      ENNReal.ofReal (eL (R+n)) + ENNReal.ofReal (eR (R+n)) ≤
        ENNReal.ofReal (2 * η^((R+n)/b)) := by
    rw [← ENNReal.ofReal_add (hnonneg (R+n)).1 (hnonneg (R+n)).2]
    exact ENNReal.ofReal_le_ofReal (by
      linarith [(hbound (R+n)).1, (hbound (R+n)).2])
  have hsum : Summable (fun n : ℕ => 2 * η^((R+n)/b)) := hseries.1.mul_left 2
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * η^((R+n)/b)) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (2 * ∑' n : ℕ, η^((R+n)/b)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (by norm_num) (pow_nonneg hη0 _)) hsum]
      rw [← tsum_mul_left]
    _ ≤ ENNReal.ofReal (2 * ((b : ℝ)/(1-η) * η^(R/b))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hseries.2 (by norm_num)
    _ = ENNReal.ofReal (2 * (b : ℝ) * η^(R/b) / (1-η)) := by
      congr 1 <;> ring

/-! The complete native-component consumer of the finite posterior/count bridge.

The class is the actual closed communicating class of the original M₀+M₁
support.  `K` is definitionally the selected original law of the native
component; `component_restriction` is retained in the conclusion so every
payment and every risk remains on the same original measure J. -/
theorem native_component_rectangle_theorem42
    (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (hJ : HasOriginalCylinders J θ)
    (D : FiniteClosedClasses.ClosedClass (θ.matrix false + θ.matrix true))
    (hc : 0 < ∑ i : D.val, θ.initial i.val)
    (w : List Bool) (hw : w ≠ [])
    (R : Rectangle (product (nativeComponent θ D hc) w))
    (r : D.val) (hr : r ∈ R.rows) :
    let κ := nativeComponent θ D hc
    let K : ProbabilityMeasure (PathSpace D.val) := jointLaw κ
    let b := w.length + Fintype.card D.val
    ∃ a : ∀ h, LabelledRoute κ h r,
      (a r).length = 0 ∧ (∀ h, (a h).length ≤ Fintype.card D.val) ∧
      (∀ t : ℤ,
        ENNReal.ofReal (∑ i : D.val, θ.initial i.val) •
            K.map (componentInclusion D.val) =
          J.restrict (state t ⁻¹' (D.val : Set H))) ∧
      (∀ w' (i j : D.val),
        product κ w' i j = product θ w' i.val j.val) ∧
      (∀ j : ℕ,
        let ρ := 1 - rectangleMinimum (product κ w) R /
          rectangleMaximum (product κ w) R
        let ε := selectedEpsilon κ w r a
        let η := 1 - ε * (1-ρ^2)
        (0 ≤ ρ ∧ ρ < 1) ∧ (0 < ε ∧ ε ≤ 1) ∧ (0 ≤ η ∧ η < 1) ∧
        ((∀ᵐ z ∂K,
          |bitPredictor (visibleLaw κ : Measure _) (fun z => z 0) exterior
              (exterior z.2) -
            bitPredictor (visibleLaw κ : Measure _) (fun z => z 0)
              (leftObservation j) (leftObservation j z.2)| ≤
            ρ ^ OriginalRectangleMoments.chronologicalCount w b
              (-((j/b : ℕ) : ℤ)*b) (j/b) z ∧
          |bitPredictor (visibleLaw κ : Measure _) (fun z => z 0) exterior
              (exterior z.2) -
            bitPredictor (visibleLaw κ : Measure _) (fun z => z 0)
              (rightObservation j) (rightObservation j z.2)| ≤
            ρ ^ OriginalRectangleMoments.chronologicalCount w b 1 (j/b) z) ∧
        leftRisk κ j ≤ η^(j/b) ∧ rightRisk κ j ≤ η^(j/b)) ∧
      (∀ R₀ : ℕ,
        rootErasureTail κ R₀ ≤
          2 * (b : ℝ) * (Real.sqrt (1 - selectedEpsilon κ w r a *
            (1-(1-rectangleMinimum (product κ w) R /
              rectangleMaximum (product κ w) R)^2)))^(R₀/b) /
            (1-Real.sqrt (1 - selectedEpsilon κ w r a *
              (1-(1-rectangleMinimum (product κ w) R /
                rectangleMaximum (product κ w) R)^2))) ∧
        erasureTail κ R₀ ≤ ENNReal.ofReal
          (2 * (b : ℝ) *
            (1 - selectedEpsilon κ w r a *
              (1-(1-rectangleMinimum (product κ w) R /
                rectangleMaximum (product κ w) R)^2))^(R₀/b) /
            (1-(1 - selectedEpsilon κ w r a *
              (1-(1-rectangleMinimum (product κ w) R /
                rectangleMaximum (product κ w) R)^2)))) ∧
        rootErasureTail κ 0 ≤
          2 * (b : ℝ) /
            (1-Real.sqrt (1 - selectedEpsilon κ w r a *
              (1-(1-rectangleMinimum (product κ w) R /
              rectangleMaximum (product κ w) R)^2))))) := by
  dsimp only
  let κ := nativeComponent θ D hc
  let K : ProbabilityMeasure (PathSpace D.val) := jointLaw κ
  let b := w.length + Fintype.card D.val
  have hK : HasOriginalCylinders K κ := by
    exact (same_law_trimming κ).1
  have hcomponent := native_component_irreducible θ D hc
  obtain ⟨a, ha0, hab, _, _, _, hocc⟩ :=
    irreducible_rectangle_occurrence κ K hK hcomponent w R r hr
  have hclass := component_restriction θ D hc J hJ K hK
  have hvis : K.map Prod.snd = (visibleLaw κ : Measure (ℤ → Bool)) :=
    native_visible_pushforward κ K rfl
  have hρ := component_rho_range (product κ w) R
  let ρ := 1 - rectangleMinimum (product κ w) R /
    rectangleMaximum (product κ w) R
  let ε := selectedEpsilon κ w r a
  let η := 1 - ε * (1-ρ^2)
  have hε : 0 < ε ∧ ε ≤ 1 := by simpa [ε] using hocc.1
  have hη : 0 ≤ η ∧ η < 1 := by
    dsimp [η]
    have hs : 0 < 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
    constructor <;> nlinarith [hε.1, hε.2, hs]
  have hbound (j : ℕ) :
      leftRisk κ j ≤ η^(j/b) ∧ rightRisk κ j ≤ η^(j/b) := by
    have hh := original_rectangle_erasure_bounds κ K hK w hw R r hr a hab j
    have hhL := hh.2.1
    have hhR := hh.2.2
    simpa [leftRisk, rightRisk, fullMean, leftMean, rightMean, hvis, ρ, ε, η] using
      And.intro hhL hhR
  have hnonneg (j : ℕ) : 0 ≤ leftRisk κ j ∧ 0 ≤ rightRisk κ j := by
    exact ⟨integral_nonneg (fun z => sq_nonneg _), integral_nonneg (fun z => sq_nonneg _)⟩
  have hb : 0 < b := by
    have hcD : 0 < Fintype.card D.val :=
      (FiniteClosedClasses.actual_structure (θ.matrix false + θ.matrix true)
        (Matrix.mem_rowStochastic_iff_sum.mpr
          ⟨fun i j => add_nonneg (θ.matrix_nonneg _ _ _) (θ.matrix_nonneg _ _ _), θ.stochastic⟩)).class_card D |>.1
    have hwlen : 0 < w.length := List.length_pos.mpr hw
    omega
  have hroot (R₀ : ℕ) := geometric_root_tail b hb η hη.1 hη.2
    (leftRisk κ) (rightRisk κ) hnonneg hbound R₀
  have hsq (R₀ : ℕ) := geometric_square_tail b hb η hη.1 hη.2
    (leftRisk κ) (rightRisk κ) hnonneg hbound R₀
  refine ⟨a, ha0, hab, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hclass t).1
  · intro w' i j
    exact (hclass 0).2 w' i j
  · intro j
    have hh := original_rectangle_erasure_bounds κ K hK w hw R r hr a hab j
    have hρ' : ρ = 1 - rectangleMinimum (product κ w) R /
        rectangleMaximum (product κ w) R := rfl
    refine ⟨⟨by simpa [ρ] using hρ.1, by simpa [ρ] using hρ.2⟩,
      hε, hη, ?_, ?_⟩
    · simpa [ρ, ε, η, hvis, bitPredictor, fullMean, leftMean, rightMean]
        using hh.1
    · simpa [ρ, ε, η, hvis, bitPredictor, fullMean, leftMean, rightMean]
        using hh.2.1
    · simpa [ρ, ε, η, hvis, bitPredictor, fullMean, leftMean, rightMean]
        using hh.2.2
  · intro R₀
    have hroot0 := hroot R₀
    have hsq0 := hsq R₀
    refine ⟨?_, ?_, ?_⟩
    · simpa [rootErasureTail, η, ε, ρ] using hroot0.2
    · simpa [erasureTail, η, ε, ρ] using hsq0
    · simpa [rootErasureTail, η, ε, ρ] using (hroot 0).2

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleTheorem42
