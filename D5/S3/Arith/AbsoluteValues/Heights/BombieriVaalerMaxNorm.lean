/- GID: D5/S3/Arith/AbsoluteValues/Heights/BombieriVaalerMaxNorm
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/BombieriVaalerMaxNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An integral basis of a matrix kernel has a discriminant and row-space height bound. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.Duality
public import D5.S3.Arith.AbsoluteValues.Heights.Extraction
public import D5.S3.Arith.AbsoluteValues.Heights.MinkowskiSecond
public import D5.S3.Arith.AbsoluteValues.Heights.MixedCube
public import Mathlib.Algebra.Module.LinearMap.Rat

public section

open scoped Real

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
open scoped Classical in
/-- **The sup-norm height of an integral tuple in a dilate of the body.** -/
theorem mulHeight_le_of_mem_smul_mixedCube [Finite ι] {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0)
    (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) :
    Height.mulHeight x ≤ (r * ballRadius 1) ^ nrRealPlaces K
      * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
  have hmem' : (∀ w j, |realCoord K ι w j (mixedPiEmb K ι x)| ≤ r * ballRadius 1) ∧
      ∀ w j, ‖complexCoord K ι w j (mixedPiEmb K ι x)‖ ≤ r * ballRadius 2 := by
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', (show r⁻¹ • mixedPiEmb K ι x ∈ mixedCube K ι ↔
        (∀ w j, |realCoord K ι w j (r⁻¹ • mixedPiEmb K ι x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K ι w j (r⁻¹ • mixedPiEmb K ι x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])] at hmem
    simpa only [map_smul, smul_eq_mul, abs_mul, abs_inv, _root_.norm_smul,
      norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr] using hmem
  have hreal (w : {w : InfinitePlace K // IsReal w}) :
      (⨆ j, w.1 (x j)) ≤ r * ballRadius 1 := by
    refine Real.iSup_le (fun j ↦ ?_) (mul_nonneg hr.le ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1).le)
    have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
      rw [mixedPiEmb]
      exact (toMixedPi K ι).symm_apply_apply _
    have hval : realCoord K ι w j (mixedPiEmb K ι x)
        = (((toMixedPi K ι).symm (mixedPiEmb K ι x)) j).1 w := rfl
    have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).1 w‖ := by
      rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
    have hcoord : |realCoord K ι w j (mixedPiEmb K ι x)| = w.1 (x j) := by
      rw [hval, hs, hw, Real.norm_eq_abs]
    rw [← hcoord]
    exact hmem'.1 w j
  have hcomplex (w : {w : InfinitePlace K // IsComplex w}) :
      (⨆ j, w.1 (x j)) ≤ r * ballRadius 2 := by
    refine Real.iSup_le (fun j ↦ ?_) (mul_nonneg hr.le ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 2).le)
    have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
      rw [mixedPiEmb]
      exact (toMixedPi K ι).symm_apply_apply _
    have hval : complexCoord K ι w j (mixedPiEmb K ι x)
        = (((toMixedPi K ι).symm (mixedPiEmb K ι x)) j).2 w := rfl
    have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).2 w‖ := by
      rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
    have hcoord : ‖complexCoord K ι w j (mixedPiEmb K ι x)‖ = w.1 (x j) := by
      rw [hval, hs, hw]
    rw [← hcoord]
    exact hmem'.2 w j
  have hb1 : (0 : ℝ) ≤ r * ballRadius 1 := mul_nonneg hr.le ((fun (n : ℕ) =>
    (show 0 < ballRadius n from Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1).le
  have hb2 : (0 : ℝ) ≤ r * ballRadius 2 := mul_nonneg hr.le ((fun (n : ℕ) =>
    (show 0 < ballRadius n from Real.rpow_pos_of_pos
      (ENNReal.toReal_pos
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 2).le
  have harch : (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      ≤ (r * ballRadius 1) ^ nrRealPlaces K * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (InfinitePlace K))
      (fun v ↦ v.IsReal)]
    refine mul_le_mul ?_ ?_
      (Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _)
      (by positivity)
    · calc ∏ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ v.IsReal),
              (⨆ i, v (x i)) ^ v.mult
          ≤ ∏ _v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ v.IsReal), (r * ballRadius 1) := by
            refine Finset.prod_le_prod₀
              (fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _) fun v hv ↦ ?_
            rw [Finset.mem_filter] at hv
            rw [show v.mult = 1 from mult_isReal ⟨v, hv.2⟩, pow_one]
            exact hreal ⟨v, hv.2⟩
        _ = (r * ballRadius 1) ^ nrRealPlaces K := by
            rw [Finset.prod_const, ← Fintype.card_subtype]
    · calc ∏ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ ¬ v.IsReal),
              (⨆ i, v (x i)) ^ v.mult
          ≤ ∏ _v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ ¬ v.IsReal),
              ((r * ballRadius 2) ^ 2) := by
            refine Finset.prod_le_prod₀
              (fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _) fun v hv ↦ ?_
            rw [Finset.mem_filter] at hv
            have hc : v.IsComplex := not_isReal_iff_isComplex.1 hv.2
            rw [show v.mult = 2 from mult_isComplex ⟨v, hc⟩]
            exact pow_le_pow_left₀ (Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
              (hcomplex ⟨v, hc⟩) 2
        _ = ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
            rw [Finset.prod_const, ← Fintype.card_subtype]
            congr 1
            exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex)
  have hfin : (∏ᶠ v : FinitePlace K, ⨆ i, v (x i)) ≤ 1 := by
    choose z hz using hint
    have hzne : ∃ i, z i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext fun i ↦ by rw [← hz i, hcon i]; simp)
    have heq : (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
        = ∏ᶠ v : FinitePlace K, ⨆ i, v ((z i : K)) :=
      finprod_congr fun v ↦ iSup_congr fun i ↦ by rw [hz i]
    have hzne' : z ≠ 0 := Function.ne_iff.mpr hzne
    have hfinite := NumberField.absNorm_mul_finprod_finitePlace_eq_one (K := K) hzne'
    have hnormFinite : (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((z i : 𝓞 K) : K))
        = ((Ideal.absNorm (Ideal.span (Set.range z)) : ℝ))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by exact_mod_cast hfinite)
    rw [heq, hnormFinite]
    have hI : Ideal.span (Set.range z) ≠ (⊥ : Ideal (𝓞 K)) := by
      obtain ⟨i, hi⟩ := hzne
      exact fun h ↦ hi ((Ideal.span_eq_bot.1 h) (z i) ⟨i, rfl⟩)
    have h1 : (1 : ℝ) ≤ (Ideal.absNorm (Ideal.span (Set.range z)) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2
        (fun h ↦ hI (Ideal.absNorm_eq_zero_iff.1 h))
    rw [inv_le_one_iff₀]
    exact Or.inr h1
  have hfin0 : 0 ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  have harch0 : 0 ≤ ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult :=
    Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _
  rw [NumberField.mulHeight_eq hx]
  calc (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
      ≤ ((r * ballRadius 1) ^ nrRealPlaces K * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K) * 1 :=
        mul_le_mul harch hfin hfin0 (by positivity)
    _ = _ := mul_one _

end NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
open scoped Classical in
theorem mulHeight_le_pow_of_mem_smul_mixedCube [Finite ι] {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0)
    (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) :
    Height.mulHeight x ≤ ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (π : ℝ)⁻¹ ^ nrComplexPlaces K)
      * r ^ finrank ℚ K := by
  refine (mulHeight_le_of_mem_smul_mixedCube hr hx hint hmem).trans (le_of_eq ?_)
  have hb2 : (ballRadius 2) ^ 2 = (π : ℝ)⁻¹ := by
    rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (show ballRadius 2 = 1 / Real.sqrt π from by
        rw [(show ballRadius 2 = unitBallVolume 2 ^ (-(1 / ((2 : ℕ) : ℝ))) from by
            rw [ballRadius, unitVolumeRadius, finrank_euclideanSpace_fin, unitBallVolume]), (show unitBallVolume 2 = π from by
            rw [unitBallVolume, EuclideanSpace.volume_ball_fin_two]
            simp [Real.pi_pos.le]), show ((2 : ℕ) : ℝ) = 2 by norm_num,
          Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow, one_div]))), div_pow, one_pow, Real.sq_sqrt Real.pi_pos.le, inv_eq_one_div]
  have e1 : (r * ballRadius 1) ^ nrRealPlaces K
      = (2 : ℝ)⁻¹ ^ nrRealPlaces K * r ^ nrRealPlaces K := by
    rw [(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (show ballRadius 1 = 1 / 2 from by
        rw [(show ballRadius 1 = unitBallVolume 1 ^ (-(1 / ((1 : ℕ) : ℝ))) from by
            rw [ballRadius, unitVolumeRadius, finrank_euclideanSpace_fin, unitBallVolume]), (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal in (show unitBallVolume 1 = 2 from by
                rw [unitBallVolume, EuclideanSpace.volume_ball]
                simp only [Fintype.card_fin, Nat.cast_one, ofReal_one, one_mul, pow_one]
                rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
                  ENNReal.toReal_ofReal (by positivity), div_eq_iff (by positivity)]
                have h : Real.sqrt π ≠ 0 := by positivity
                field_simp))), Nat.cast_one, div_one, Real.rpow_neg_one]
        norm_num))), mul_pow, one_div]; ring
  have e2 : ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K
      = (π : ℝ)⁻¹ ^ nrComplexPlaces K * r ^ (2 * nrComplexPlaces K) := by
    rw [mul_pow, hb2, mul_pow, ← pow_mul]; ring
  rw [e1, e2, ← InfinitePlace.card_add_two_mul_card_eq_rank K, pow_add]
  ring

section Span

variable [LinearOrder ι] (V : Submodule K (ι → K))

open scoped Classical in
/-- **Minkowski's second theorem for the sup-norm body over a number field.** -/
theorem prod_successiveMinimum_mixedCube_le :
    (∏ i ∈ Finset.range (finrank ℚ K * finrank K V),
        ZLattice.successiveMinimum V.mixedLattice
          ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) i)
      ≤ (2 : ℝ) ^ (finrank ℚ K * finrank K V)
          * (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|)
              ^ finrank K V * V.arakelovMulHeight) := by
  have hconvCube : Convex ℝ (mixedCube K ι) := by
    refine Convex.inter (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
      (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
    · exact (convex_closedBall _ _).linear_preimage (realCoord K ι w j)
    · exact (convex_closedBall _ _).linear_preimage (complexCoord K ι w j)
  have hnegCube {x : mixedPi K ι} (hx : x ∈ mixedCube K ι) : -x ∈ mixedCube K ι := by
    rw [(show x ∈ mixedCube K ι ↔
        (∀ w j, |realCoord K ι w j (x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K ι w j (x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])] at hx
    rw [(show -x ∈ mixedCube K ι ↔
        (∀ w j, |realCoord K ι w j (-x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K ι w j (-x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])]
    simpa using hx
  have hconvPre : Convex ℝ ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :=
    hconvCube.linear_preimage (V.mixedSpan.subtype)
  have hnegPre {x : ↥V.mixedSpan}
      (hx : x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :
      -x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι := by
    simpa using hnegCube hx
  have hintn : (interior ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι)).Nonempty := by
    let _i : Fintype ι := Fintype.ofFinite ι
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    refine continuous_subtype_val.continuousAt.preimage_mem_nhds ?_
    refine Filter.inter_mem (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
      (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
    · refine (realCoord K ι w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
      change Metric.closedBall 0 (ballRadius 1) ∈
        nhds ((realCoord K ι w j) (0 : mixedPi K ι))
      rw [map_zero]
      exact Metric.closedBall_mem_nhds (0 : ℝ) ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1)
    · refine (complexCoord K ι w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
      change Metric.closedBall 0 (ballRadius 2) ∈
        nhds ((complexCoord K ι w j) (0 : mixedPi K ι))
      rw [map_zero]
      exact Metric.closedBall_mem_nhds (0 : ℂ) ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 2)
  have hbdd : Bornology.IsBounded
      ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) := by
    apply (Bornology.isBounded_image_subtype_val).mp
    exact (isBounded_mixedCube (K := K)).subset (by
      rintro x ⟨y, hy, rfl⟩
      exact hy)
  have hmink := ZLattice.prod_successiveMinimum_mul_measure_le V.mixedLattice volume
    (hconvPre) (fun x hx ↦ hnegPre hx)
    hintn hbdd
  rw [V.finrank_mixedSpan, Submodule.covolume_mixedLattice] at hmink
  have hfinite : volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) ≠ ⊤ :=
    hbdd.measure_lt_top.ne
  have hvol1 : (1 : ℝ)
      ≤ (volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι)).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hfinite (one_le_volume_preimage_mixedCube _)
  have hprod0 : 0 ≤ ∏ i ∈ Finset.range (finrank ℚ K * finrank K V),
      ZLattice.successiveMinimum V.mixedLattice
        ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) i :=
    Finset.prod_nonneg fun i hi ↦ (ZLattice.successiveMinimum_pos V.mixedLattice
      (hconvPre) (fun x hx ↦ hnegPre hx)
      hintn hbdd
      (by rw [V.finrank_mixedSpan]; exact Finset.mem_range.1 hi)).le
  refine le_trans ?_ hmink
  nlinarith [hprod0, hvol1]

end Span

end NumberField.mixedEmbedding
namespace NumberField

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open NumberField.mixedEmbedding
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

section Main

variable [LinearOrder ι] (V : Submodule K (ι → K))

open scoped Classical in
/-- **Layer 5.4, the relative form.** -/
theorem exists_basis_prod_mulHeight_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, Height.mulHeight (x l))
        ≤ (2 / π) ^ (finrank K V * nrComplexPlaces K)
            * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
  have hconvCube : Convex ℝ (mixedCube K ι) := by
    refine Convex.inter (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
      (convex_iInter fun w ↦ convex_iInter fun j ↦ ?_)
    · exact (convex_closedBall _ _).linear_preimage (realCoord K ι w j)
    · exact (convex_closedBall _ _).linear_preimage (complexCoord K ι w j)
  have hnegCube {x : mixedPi K ι} (hx : x ∈ mixedCube K ι) : -x ∈ mixedCube K ι := by
    rw [(show x ∈ mixedCube K ι ↔
        (∀ w j, |realCoord K ι w j (x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K ι w j (x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])] at hx
    rw [(show -x ∈ mixedCube K ι ↔
        (∀ w j, |realCoord K ι w j (-x)| ≤ ballRadius 1) ∧
          ∀ w j, ‖complexCoord K ι w j (-x)‖ ≤ ballRadius 2 from by
        simp [mixedCube, Real.norm_eq_abs])]
    simpa using hx
  have hclosedCube : IsClosed (mixedCube K ι) := by
    let _i : Fintype ι := Fintype.ofFinite ι
    refine IsClosed.inter (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
      (isClosed_iInter fun w ↦ isClosed_iInter fun j ↦ ?_)
    · exact Metric.isClosed_closedBall.preimage
        (realCoord K ι w j).continuous_of_finiteDimensional
    · exact Metric.isClosed_closedBall.preimage
        (complexCoord K ι w j).continuous_of_finiteDimensional
  have hconvPre : Convex ℝ ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :=
    hconvCube.linear_preimage (V.mixedSpan.subtype)
  have hnegPre {x : ↥V.mixedSpan}
      (hx : x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :
      -x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι := by
    simpa using hnegCube hx
  have hclosedPre : IsClosed ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :=
    hclosedCube.preimage continuous_subtype_val
  set B : Set ↥V.mixedSpan := (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι with hB
  have hconv := hconvPre
  have hsymm : ∀ z ∈ B, -z ∈ B := fun z hz ↦ hnegPre hz
  have hintn : (interior ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι)).Nonempty := by
    let _i : Fintype ι := Fintype.ofFinite ι
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    refine continuous_subtype_val.continuousAt.preimage_mem_nhds ?_
    refine Filter.inter_mem (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
      (Filter.iInter_mem.2 fun w ↦ Filter.iInter_mem.2 fun j ↦ ?_)
    · refine (realCoord K ι w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
      change Metric.closedBall 0 (ballRadius 1) ∈
        nhds ((realCoord K ι w j) (0 : mixedPi K ι))
      rw [map_zero]
      exact Metric.closedBall_mem_nhds (0 : ℝ) ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 1)
    · refine (complexCoord K ι w j).continuous_of_finiteDimensional.continuousAt.preimage_mem_nhds ?_
      change Metric.closedBall 0 (ballRadius 2) ∈
        nhds ((complexCoord K ι w j) (0 : mixedPi K ι))
      rw [map_zero]
      exact Metric.closedBall_mem_nhds (0 : ℂ) ((fun (n : ℕ) =>
      (show 0 < ballRadius n from Real.rpow_pos_of_pos
        (ENNReal.toReal_pos
          (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne' measure_ball_lt_top.ne) _)) 2)
  have hbdd : Bornology.IsBounded B := by
    apply (Bornology.isBounded_image_subtype_val).mp
    exact (isBounded_mixedCube (K := K)).subset (by
      rintro x ⟨y, hy, rfl⟩
      exact hy)
  have hcl := hclosedPre
  obtain ⟨v, hvL, hvind, hvmem⟩ :=
    ZLattice.exists_linearIndependent_mem_smul_successiveMinimum V.mixedLattice hconv hsymm hintn
      hbdd hcl
  have hfr : finrank ℝ ↥V.mixedSpan = finrank ℚ K * finrank K V := V.finrank_mixedSpan
  set e : Fin (finrank ℚ K * finrank K V) ≃ Fin (finrank ℝ ↥V.mixedSpan) := finCongr hfr.symm
    with he
  have hlift : ∀ j, ∃ z ∈ V.integerPoints, mixedPiEmb K ι z = ((v (e j) : mixedPi K ι)) :=
    fun j ↦ by
      have h := hvL (e j)
      change ((v (e j) : mixedPi K ι)) ∈
        Submodule.map (mixedPiEmb K ι) (V.integerPoints.restrictScalars ℤ) at h
      rw [Submodule.mem_map] at h
      simpa using h
  choose x hxmem hxemb using hlift
  set fQ : (ι → K) →ₗ[ℚ] mixedPi K ι := (mixedPiEmb K ι).toAddMonoidHom.toRatLinearMap with hfQ
  have hindR : LinearIndependent ℝ (fQ ∘ x) := by
    have h1 : LinearIndependent ℝ (fun j ↦ v (e j)) := hvind.comp e e.injective
    have h2 : LinearIndependent ℝ (fun j ↦ ((v (e j) : mixedPi K ι))) :=
      h1.map' (V.mixedSpan.subtype) (Submodule.ker_subtype _)
    have hfQapp : ∀ z, fQ z = mixedPiEmb K ι z := fun z ↦ rfl
    simpa only [Function.comp_def, hfQapp, hxemb] using h2
  obtain ⟨s, hsind, hsle⟩ :=
    LinearIndependent.exists_linearIndependent_comp_finrank_mul (F := ℚ) (E := ℝ) fQ hindR
  refine ⟨x ∘ s, hsind, fun l ↦ hxmem _, ?_⟩
  set lam : ℕ → ℝ := ZLattice.successiveMinimum V.mixedLattice B with hlam
  set C : ℝ := (2 : ℝ)⁻¹ ^ nrRealPlaces K * (π : ℝ)⁻¹ ^ nrComplexPlaces K with hC
  have hCpos : 0 < C := by
    have := Real.pi_pos
    positivity
  have hdpos : 0 < finrank ℚ K := Module.finrank_pos
  have hlampos : ∀ i, i < finrank ℚ K * finrank K V → 0 < lam i := fun i hi ↦
    ZLattice.successiveMinimum_pos V.mixedLattice hconv hsymm hintn hbdd (by rw [hfr]; exact hi)
  have hlamnn : ∀ i, 0 ≤ lam i := by
    intro i
    rcases lt_or_ge i (finrank ℚ K * finrank K V) with h | h
    · exact (hlampos i h).le
    · have hempty : {t : ℝ | 0 < t ∧ ∃ w : Fin (i + 1) → ↥V.mixedSpan,
          (∀ k, w k ∈ (t • B) ∩ (V.mixedLattice : Set ↥V.mixedSpan)) ∧
            LinearIndependent ℝ w} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro -
        rintro ⟨w, -, hind⟩
        have hcard := hind.fintype_card_le_finrank
        simp only [Fintype.card_fin] at hcard
        rw [hfr] at hcard
        omega
      rw [hlam, ZLattice.successiveMinimum, hempty, Real.sInf_empty]
  have hlammono : ∀ i j, i ≤ j → j < finrank ℚ K * finrank K V → lam i ≤ lam j :=
    fun i j hij hj ↦
      ZLattice.successiveMinimum_le_of_le hij (by rw [hfr]; exact hj) hconv hsymm hintn
  have hsmulcoe : ∀ (r : ℝ) (z : ↥V.mixedSpan), z ∈ r • B →
      (z : mixedPi K ι) ∈ r • mixedCube K ι := by
    rintro r z ⟨b, hb, rfl⟩
    exact ⟨(b : mixedPi K ι), hb, by simp⟩
  have hheight : ∀ l : Fin (finrank K V),
      Height.mulHeight ((x ∘ s) l) ≤ C * lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
    intro l
    have hsl : (s l).val < finrank ℚ K * finrank K V := (s l).isLt
    have hdl : finrank ℚ K * l.val < finrank ℚ K * finrank K V :=
      (Nat.mul_lt_mul_left hdpos).2 l.isLt
    have hmem : mixedPiEmb K ι (x (s l)) ∈ (lam (s l).val) • mixedCube K ι := by
      have h := hsmulcoe _ _ (hvmem (e (s l)))
      rwa [← hxemb (s l)] at h
    have hintg : ∀ j, ∃ z : 𝓞 K, (z : K) = (x (s l)) j :=
      ((show (x (s l)) ∈ (V).integerPoints ↔
      (x (s l)) ∈ (V) ∧ ∀ j, ∃ z : 𝓞 K, (z : K) = (x (s l)) j from by
      simp [Submodule.integerPoints, Submodule.mem_inf, NumberField.integralTuples,
        Submodule.mem_pi, Submodule.one_eq_range]).1 (hxmem (s l))).2
    have h1 : Height.mulHeight (x (s l)) ≤ C * (lam (s l).val) ^ finrank ℚ K :=
      mulHeight_le_pow_of_mem_smul_mixedCube (hlampos _ hsl) (hsind.ne_zero l) hintg hmem
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hlampos _ hsl).le (hlammono _ _ (hsle l) hdl) _) hCpos.le
  have key : ∀ (t h : ℝ) (a b k : ℕ),
      ((2 : ℝ)⁻¹ ^ a * (π : ℝ)⁻¹ ^ b) ^ k * ((2 : ℝ) ^ ((a + 2 * b) * k)
          * (((2 : ℝ)⁻¹ ^ b * t) ^ k * h))
        = (2 / π : ℝ) ^ (k * b) * (t ^ k * h) := by
    intro t h a b k
    have hπ : π ≠ 0 := Real.pi_ne_zero
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_pow, ← pow_mul, div_pow]
    simp only [inv_pow]
    field_simp
    ring
  calc (∏ l, Height.mulHeight ((x ∘ s) l))
      ≤ ∏ l : Fin (finrank K V), C * lam (finrank ℚ K * l.val) ^ finrank ℚ K :=
        Finset.prod_le_prod₀ (fun l _ ↦ (Height.mulHeight_pos _).le) fun l _ ↦ hheight l
    _ = C ^ finrank K V * ∏ l : Fin (finrank K V), lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ C ^ finrank K V * ∏ j ∈ Finset.range (finrank ℚ K * finrank K V), lam j := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fin.prod_univ_eq_prod_range (fun i ↦ lam (finrank ℚ K * i) ^ finrank ℚ K)]
        exact Finset.prod_pow_le_prod_range hlamnn hlammono _ _ le_rfl
    _ ≤ C ^ finrank K V * ((2 : ℝ) ^ (finrank ℚ K * finrank K V)
          * (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|)
              ^ finrank K V * V.arakelovMulHeight)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact prod_successiveMinimum_mixedCube_le V
    _ = (2 / π) ^ (finrank K V * nrComplexPlaces K)
          * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
        rw [hC, ← InfinitePlace.card_add_two_mul_card_eq_rank K]
        exact key _ _ _ _ _

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Layer 5.4, the absolute form, at Bombieri–Vaaler's constant.** -/
theorem exists_basis_prod_absMulHeight_le' :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, absMulHeight (x l))
        ≤ (2 / π) ^ ((finrank K V * nrComplexPlaces K : ℝ) / finrank ℚ K)
          * |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K))
          * V.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  let nativeSource12 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) {c : K} (hc : c ≠ 0) => (show NumberField.arakelovMulHeight (c • x) = NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · rw [smul_zero]
    have hcx : c • x ≠ 0 := by simp [hc, hx]
    have hFinite :
        (∏ v : NumberField.InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((c • x) i)
          = ∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i) := by
      have hA : (0 : ℝ) < ∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
        exact Finset.prod_pos fun v _ ↦ pow_pos
          ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
      have h := Height.mulHeight_smul_eq_mulHeight x hc
      rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
      have hSupInfinite (v : NumberField.InfinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      have hSupFinite (v : NumberField.FinitePlace K) :
          (⨆ i, v ((c • x) i)) = v c * ⨆ i, v (x i) := by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (NonnegHomClass.apply_nonneg v c)]
      simp only [hSupInfinite, hSupFinite, mul_pow, Finset.prod_mul_distrib] at h ⊢
      exact mul_left_cancel₀ hA.ne' (by linear_combination h)
    have harch (v : NumberField.InfinitePlace K) :
        (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
          = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
      have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_pow]
      have hPower : (v c ^ 2) ^ ((v.mult : ℝ) / 2) = v c ^ v.mult := by
        rw [← Real.rpow_natCast (v c) v.mult, ← Real.rpow_natCast (v c) 2,
          ← Real.rpow_mul (NonnegHomClass.apply_nonneg v c)]
        congr 1
        push_cast
        ring
      rw [hsum, Real.mul_rpow (by positivity) (by positivity),
        hPower]
    rw [NumberField.arakelovMulHeight, if_neg hcx, NumberField.arakelovMulHeight, if_neg hx]
    simp only [harch, Finset.prod_mul_distrib]
    rw [mul_right_comm, hFinite, mul_comm])))
  let nativeSource13 := (open Finset Function Height Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : ι → K) => (show 1 ≤ NumberField.arakelovMulHeight x from by
    classical
    rcases eq_or_ne x 0 with rfl | hx
    · simp [NumberField.arakelovMulHeight]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
    have hi' : ((x i)⁻¹ • x) i = 1 := by simp [hi]
    rw [← nativeSource12 x (inv_ne_zero hi), NumberField.arakelovMulHeight, if_neg hx']
    refine one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun v _ ↦ ?_)
      (one_le_finprod fun v ↦ Finite.le_ciSup_of_le i (by simp [hi']))
    have h1 : (1 : ℝ) ≤ ∑ j, v (((x i)⁻¹ • x) j) ^ 2 :=
      le_trans (le_of_eq (by simp [hi']))
        (Finset.single_le_sum (f := fun j ↦ v (((x i)⁻¹ • x) j) ^ 2) (fun j _ ↦ by positivity) (mem_univ i))
    exact Real.one_le_rpow h1 (by positivity))))
  let nativeSource73 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} [instSource1 : Field K] [instSource3 : NumberField K] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∃ (d : K) (y : ι → 𝓞 K), d ≠ 0 ∧ ∀ i, (y i : K) = d * x i from by
    classical
    letI : FaithfulSMul (𝓞 K) K :=
      (faithfulSMul_iff_algebraMap_injective (𝓞 K) K).2
        (IsFractionRing.injective (𝓞 K) K)
    have := Fintype.ofFinite ι
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
      (Finset.univ : Finset ι) x
    refine ⟨Algebra.algebraMap (𝓞 K) K (b : 𝓞 K), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
        (nonZeroDivisors.coe_ne_zero b)
    · have h := (hb i (Finset.mem_univ i)).choose_spec
      rw [show (((hb i (Finset.mem_univ i)).choose : 𝓞 K) : K)
        = Algebra.algebraMap (𝓞 K) K (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def])))
  let nativeSource74 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) => (show ∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)) =
        (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (y i : K)) ^ Module.finrank K L from by
    classical
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
    have hy' : (fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
    have hspan : Ideal.span (Set.range fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) =
        (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have hK := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy
    have hL := NumberField.absNorm_mul_finprod_finitePlace_eq_one hy'
    rw [hspan, ← Ideal.absNorm_relNorm (𝓞 K), Ideal.relNorm_algebraMap, map_pow,
      ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hL
    have hcoe (a : 𝓞 K) :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) := by
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
    simp_rw [hcoe] at hL
    have hN : ((Ideal.span (Set.range y)).absNorm : ℝ) ≠ 0 := by
      have : Ideal.span (Set.range y) ≠ ⊥ := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
        exact fun h ↦ hi (by simpa using (Ideal.span_eq_bot.mp h) (y i) ⟨i, rfl⟩)
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr this
    refine mul_left_cancel₀ (pow_ne_zero (Module.finrank K L) hN) ?_
    rw [← mul_pow, hK, one_pow]
    exact_mod_cast hL)))
  let nativeSource75 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (ψ : K →+* ℂ) => (show #{φ : L →+* ℂ | φ.comp (Algebra.algebraMap K L) = ψ} = Module.finrank K L from by
    classical
    letI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
    letI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
    letI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
    let : Algebra K ℂ := ψ.toAlgebra
    rw [← AlgHom.card K L ℂ]
    refine (Finset.card_nbij AlgHom.toRingHom (fun σ _ ↦ ?_) (fun σ _ τ _ h => AlgHom.ext fun x => DFunLike.congr_fun h x)
      (fun φ hφ ↦ ?_)).symm
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
      ext r
      simp [RingHom.algebraMap_toAlgebra]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hφ
      exact ⟨⟨φ, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← hφ]⟩, mem_univ _, rfl⟩))))
  let nativeSource76 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (F : (K →+* ℂ) → ℝ) => (show ∏ φ : L →+* ℂ, F (φ.comp (algebraMap K L)) = (∏ ψ : K →+* ℂ, F ψ) ^ Module.finrank K L from by
    classical
    rw [← Finset.prod_fiberwise Finset.univ (fun φ : L →+* ℂ ↦ φ.comp (algebraMap K L))
      (fun φ ↦ F (φ.comp (algebraMap K L))), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun ψ _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, nativeSource75]))))
  let nativeSource77 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} [instSource1 : Field K] [instSource3 : NumberField K] {M : Type _} [CommMonoid M] (f : NumberField.InfinitePlace K → M) => (show ∏ φ : K →+* ℂ, f (NumberField.InfinitePlace.mk φ) = ∏ w : NumberField.InfinitePlace K, f w ^ w.mult from by
    classical
    classical
    rw [← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk (fun φ ↦ f (NumberField.InfinitePlace.mk φ))]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
      Finset.prod_const, NumberField.InfinitePlace.card_filter_mk_eq])))
  let nativeSource78 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] (f : NumberField.InfinitePlace K → ℝ) (g : NumberField.InfinitePlace L → ℝ)
      (h : ∀ φ : L →+* ℂ, g (NumberField.InfinitePlace.mk φ) = f (NumberField.InfinitePlace.mk (φ.comp (Algebra.algebraMap K L)))) => (show ∏ w : NumberField.InfinitePlace L, g w ^ w.mult = (∏ v : NumberField.InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L from by
    classical
    rw [← nativeSource77 (K := L) g, ← nativeSource77 (K := K) f,
      ← nativeSource76 (fun ψ ↦ f (NumberField.InfinitePlace.mk ψ))]
    exact Finset.prod_congr rfl fun φ _ ↦ h φ))))
  let nativeSource79 := (open Finset Function Height InfinitePlace Module in (open scoped Classical in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show ∏ w : NumberField.InfinitePlace L, (⨆ i, w (Algebra.algebraMap K L (x i))) ^ w.mult =
        (∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank K L from by
    classical
    exact (
      nativeSource78 _ _ fun φ ↦ iSup_congr fun i ↦ by simp [InfinitePlace.apply]
    )))))
  let nativeSource80 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (y : ι → 𝓞 K) => (show Height.mulHeight (fun i ↦ (y i : K)) ^ Module.finrank K L
        = Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) from by
    classical
    letI : FaithfulSMul (𝓞 K) K :=
      (faithfulSMul_iff_algebraMap_injective (𝓞 K) K).2
        (IsFractionRing.injective (𝓞 K) K)
    letI : FaithfulSMul K L :=
      (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have hz : (fun i ↦ (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
    have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (FaithfulSMul.algebraMap_injective K L
        (by simpa using h))⟩
    rw [NumberField.mulHeight_eq hz, NumberField.mulHeight_eq hz', mul_pow,
      nativeSource79 (L := L), nativeSource74 hy])))
  let nativeSource81 := (open Finset Function Height InfinitePlace Module in (fun {K : Type _} {L : Type _} [instSource1 : Field K] [instSource2 : Field L] [instSource3 : NumberField K] [instSource4 : NumberField L] [instSource5 : Algebra K L] {ι : Type _} [instSource7 : Finite ι] (x : ι → K) => (show Height.mulHeight x ^ Module.finrank K L = Height.mulHeight (algebraMap K L ∘ x) from by
    classical
    letI : FaithfulSMul K L :=
      (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
    obtain ⟨d, y, hd, hy⟩ := nativeSource73 (K := K) x
    have hd' : algebraMap K L d ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr hd
    have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
    have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
      funext i
      simp [hy i]
    have e1 : Height.mulHeight (fun i ↦ (y i : K)) = Height.mulHeight x :=
      h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
    have e2 : Height.mulHeight (fun i ↦ algebraMap K L (y i : K))
        = Height.mulHeight (algebraMap K L ∘ x) :=
      h2 ▸ Height.mulHeight_smul_eq_mulHeight _ hd'
    rw [← e1, ← e2]
    exact nativeSource80 y)))
  let nativeSource82 := (open Function IntermediateField Module in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Finite ι] (x : ι → K) => (show NumberField.absMulHeight x = Height.mulHeight x ^ ((finrank ℚ K : ℝ))⁻¹ from by
    classical
    letI : Algebra.IsIntegral ℚ K := Algebra.IsIntegral.of_finite ℚ K
    have hint : ∀ i, IsIntegral ℚ (x i) := fun i ↦ Algebra.IsIntegral.isIntegral _
    haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range (x))) :=
      IntermediateField.finiteDimensional_adjoin fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        exact hint i
    haveI : NumberField (adjoin ℚ (Set.range (x))) := {}
    have : Module.Finite (adjoin ℚ (Set.range x)) K :=
      Module.Finite.of_restrictScalars_finite ℚ _ K
    have hcomp : (Algebra.algebraMap (adjoin ℚ (Set.range x)) K) ∘
        (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x))) = x := rfl
    letI : Module.Free ℚ (adjoin ℚ (Set.range x)) :=
      Module.Free.of_divisionRing ℚ _
    letI : IsTorsionFree ℚ (adjoin ℚ (Set.range x)) :=
      Module.Free.instIsTorsionFree ℚ _
    letI : Module.Free (adjoin ℚ (Set.range x)) K :=
      Module.Free.of_divisionRing _ K
    letI : IsTorsionFree (adjoin ℚ (Set.range x)) K :=
      Module.Free.instIsTorsionFree _ K
    rw [NumberField.absMulHeight, dif_pos hint]
    conv_rhs => rw [← hcomp]
    rw [← nativeSource81, ← Module.finrank_mul_finrank ℚ (adjoin ℚ (Set.range x)) K]
    rw [← Real.rpow_natCast (Height.mulHeight (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))) (finrank (adjoin ℚ (Set.range x)) K), ← Real.rpow_mul ((Height.mulHeight_pos (fun i ↦ (⟨x i, subset_adjoin ℚ _ ⟨i, rfl⟩⟩ : adjoin ℚ (Set.range x)))).le)]
    congr 1
    have hm' : ((finrank ℚ (adjoin ℚ (Set.range x))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := ℚ) (M := adjoin ℚ (Set.range x))).ne'
    have hn' : ((finrank (adjoin ℚ (Set.range x)) K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Module.finrank_pos (R := adjoin ℚ (Set.range x)) (M := K)).ne'
    push_cast
    field_simp)))
  let nativeSource125 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 1 ≤ Projectivization.projectiveArakelovMulHeight x from by
    classical
    rw [← x.mk_rep, (fun {x : _ → _} hx ↦ (show Projectivization.projectiveArakelovMulHeight (Projectivization.mk _ x hx) =
        NumberField.arakelovMulHeight x from rfl))]
    exact nativeSource13 _)))
  let nativeSource128 := (open NumberField Real in (fun {K : Type _} [instSource1 : Field K] [instSource2 : NumberField K] {ι : Type _} [instSource4 : Fintype ι] (x : Projectivization K (ι → K)) => (show 0 < Projectivization.projectiveArakelovMulHeight x from by
    classical
    exact (
      zero_lt_one.trans_le <| nativeSource125 x
    ))))
  let nativeSource144 := (open Module exteriorPower in (fun {K : Type _} [instSource1 : Field K] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] [instSource7 : NumberField K] (V : Submodule K (ι → K)) => (show 0 < V.arakelovMulHeight from by
    classical
    exact (
      nativeSource128 _
    ))))
  obtain ⟨x, hind, hmem, hle⟩ := exists_basis_prod_mulHeight_le V
  refine ⟨x, hind, hmem, ?_⟩
  have hdne : ((finrank ℚ K : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Module.finrank_pos).ne'
  have hHpos := (nativeSource144 V)
  have hprod : (∏ l, absMulHeight (x l))
      = (∏ l, Height.mulHeight (x l)) ^ (finrank ℚ K : ℝ)⁻¹ := by
    rw [← Real.finsetProd_rpow _ _ (fun l _ ↦ (Height.mulHeight_pos _).le) _]
    exact Finset.prod_congr rfl fun l _ ↦ nativeSource82 _
  rw [hprod]
  have hstep := Real.rpow_le_rpow (Finset.prod_nonneg fun l _ ↦ (Height.mulHeight_pos _).le)
    hle (by positivity : (0 : ℝ) ≤ (finrank ℚ K : ℝ)⁻¹)
  refine hstep.trans (le_of_eq ?_)
  have hD : (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V) ^ ((finrank ℚ K : ℝ))⁻¹
      = |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K)) := by
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ)) (finrank K V),
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hpi : ((2 / π : ℝ) ^ (finrank K V * nrComplexPlaces K)) ^ ((finrank ℚ K : ℝ))⁻¹
      = (2 / π : ℝ) ^ ((finrank K V * nrComplexPlaces K : ℝ) / finrank ℚ K) := by
    have h0 : (0 : ℝ) ≤ 2 / π := by positivity
    rw [← Real.rpow_natCast (2 / π : ℝ) (finrank K V * nrComplexPlaces K), ← Real.rpow_mul h0]
    congr 1
    push_cast
    ring
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), hD, hpi]
  ring

end Main

section Kernel

variable [LinearOrder ι] {m : ℕ}

open scoped Classical in
/-- **Layer 5.4 — Bombieri–Vaaler over a number field, max-norm form, at their own constant.** -/
theorem exists_basis_ker_prod_absMulHeight_le {μ : Type*} (A : Matrix μ ι K) {k : ℕ}
    (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight (fun j ↦ (b l : ι → K) j)) ≤
        (2 / π) ^ ((k * nrComplexPlaces K : ℝ) / finrank ℚ K)
          * |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  subst hk
  obtain ⟨x, hind, hmem, hle⟩ :=
    exists_basis_prod_absMulHeight_le' (LinearMap.ker A.mulVecLin)
  have hxV : ∀ l, x l ∈ LinearMap.ker A.mulVecLin :=
    fun l ↦ ((show (x l) ∈ (LinearMap.ker A.mulVecLin).integerPoints ↔
      (x l) ∈ (LinearMap.ker A.mulVecLin) ∧ ∀ j, ∃ z : 𝓞 K, (z : K) = (x l) j from by
      simp [Submodule.integerPoints, Submodule.mem_inf, NumberField.integralTuples,
        Submodule.mem_pi, Submodule.one_eq_range]).1 (hmem l)).1
  have hind' : LinearIndependent K (fun l ↦ (⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin))) :=
    LinearIndependent.of_comp (LinearMap.ker A.mulVecLin).subtype hind
  have hsp : Submodule.span K
      (Set.range (fun l ↦ (⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin)))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hind', Fintype.card_fin]
  refine ⟨Basis.mk hind' (le_of_eq hsp.symm), ?_, ?_⟩
  · intro l j
    rw [Basis.coe_mk]
    obtain ⟨z, hz⟩ := ((show (x l) ∈ (LinearMap.ker A.mulVecLin).integerPoints ↔
      (x l) ∈ (LinearMap.ker A.mulVecLin) ∧ ∀ j, ∃ z : 𝓞 K, (z : K) = (x l) j from by
      simp [Submodule.integerPoints, Submodule.mem_inf, NumberField.integralTuples,
        Submodule.mem_pi, Submodule.one_eq_range]).1 (hmem l)).2 j
    rw [show ((⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin)) : ι → K) j = x l j from rfl, ← hz]
    exact z.2
  · rw [Basis.coe_mk, ← (open scoped Classical NumberField in (open Height Module Matrix Set Matrix in (fun {K : Type _} [instK : Field K] [instN : NumberField K] {ι : Type _} [instI : Fintype ι] [instL : LinearOrder ι] {m : Type _} (A : Matrix m ι K) => (show (LinearMap.ker A.mulVecLin).arakelovMulHeight =
          (Submodule.span K (Set.range A.row)).arakelovMulHeight from by
      rw [(fun (A : Matrix m ι K) => (show LinearMap.ker A.mulVecLin =
          (Submodule.span K (Set.range A.row)).dualAnnihilator.comap
            (Module.piEquiv ι K K).toLinearMap from by
      refine (fun {V W : Submodule K (ι → K)} (h : ∀ x, x ∈ W ↔ ∀ v ∈ V, v ⬝ᵥ x = 0) => (show W = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap from SetLike.ext fun x ↦ (h x).trans (fun {V : Submodule K (ι → K)} {x : ι → K} => (show x ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ↔ ∀ v ∈ V, v ⬝ᵥ x = 0 from by
      simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      refine forall₂_congr fun v _ ↦ ?_
      rw [show ((Module.piEquiv ι K K).toLinearMap x) v = Module.piEquiv ι K K x v from rfl,
        Module.piEquiv_apply_apply]
      simp [dotProduct])).symm)) fun x ↦ ?_
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      refine ⟨fun h v hv ↦ ?_, fun h ↦ _root_.funext fun i ↦ h _ (Submodule.subset_span ⟨i, rfl⟩)⟩
      have hker := (fun {s : Set (ι → K)} {x : ι → K} (h : ∀ v ∈ s, v ⬝ᵥ x = 0) => (show Submodule.span K s ≤ LinearMap.ker (Module.piEquiv ι K K x) from by
      rw [Submodule.span_le]
      intro v hv
      simpa only [SetLike.mem_coe, LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul,
        dotProduct] using h v hv)) (s := Set.range A.row) (x := x)
        (fun y hy ↦ by obtain ⟨i, rfl⟩ := hy; exact congrFun h i) hv
      simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct] using hker)),
        Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator])))) A]
    exact hle

end Kernel

end NumberField
