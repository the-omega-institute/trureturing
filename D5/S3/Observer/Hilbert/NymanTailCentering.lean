/- GID: D5/S3/Observer/Hilbert/NymanTailCentering
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/NymanTailCentering
   mirror-E: none(waiver:universal-hilbert-approximation)
   anchors: []
   utility: none
   digest: The reciprocal tail controls exact centering of finite Nyman approximants. -/

import OmegaBuild.Commands
import D5.S3.Observer.Hilbert.NymanHalflineMellinKernel
import D5.S3.Observer.Hilbert.NymanUnitIntervalMellin

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanTailCentering

open Set MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators
open D5.S3.Observer.Hilbert.NymanBeurlingFiniteGramDistance
open D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct

/-- The coefficient carried by the reciprocal tail beyond one. -/
def tailMoment (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ∑ i : Fin N, c i / ((i.val + 1 : ℕ) : ℂ)

/-- The same arithmetic synthesis on the open unit interval. -/
def unitSynthesis (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) : NymanUnitIntervalMellin.Carrier :=
  ∑ i : Fin N, c i • NymanUnitIntervalMellin.source (1 / ((i.val + 1 : ℕ) : ℝ))

/-- Correction at parameter one enforces the exact Nyman coefficient constraint. -/
def centered (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) : NymanUnitIntervalMellin.Carrier :=
  unitSynthesis N c - tailMoment N c • NymanUnitIntervalMellin.source 1

private theorem squared_norm_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  congr 1
  funext x
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (f x)

private theorem synthesis_representative (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) :
    (synthesis N c : ℝ → ℂ) =ᵐ[positiveMeasure]
      fun x => ∑ i : Fin N, c i *
        ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) := by
  rw [synthesis_apply]
  have hs : ∀ i : Fin N,
      (c i • sourceVector (i.val + 1) (by omega) : Carrier) =ᵐ[positiveMeasure]
        fun x => c i * ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) := by
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (sourceVector (i.val + 1) (by omega)),
      sourceVector_coe_ae (i.val + 1) (by omega)] with x hsm hsrc
    simpa only [Pi.smul_apply, smul_eq_mul, hsrc] using hsm
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin N => c i • sourceVector (i.val + 1) (by omega)),
    Filter.eventually_all.mpr hs] with x hsum hx
  simpa only [Finset.sum_apply, hx] using hsum

/-- The half-line error is exactly the local error plus the reciprocal-tail energy. -/
theorem finite_error_split (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) :
    ‖target - synthesis N c‖ ^ 2 =
      ‖NymanUnitIntervalMellin.unitTarget - unitSynthesis N c‖ ^ 2 + ‖tailMoment N c‖ ^ 2 := by
  let f : Carrier := target - synthesis N c
  let h : NymanUnitIntervalMellin.Carrier := NymanUnitIntervalMellin.unitTarget - unitSynthesis N c
  have hf : (f : ℝ → ℂ) =ᵐ[positiveMeasure]
      fun x => (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x -
        ∑ i : Fin N, c i *
          ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) :=
    (Lp.coeFn_sub target (synthesis N c)).trans
      (target_coe_ae.sub (synthesis_representative N c))
  have hh : (h : ℝ → ℂ) =ᵐ[NymanUnitIntervalMellin.unitMeasure]
      fun x => 1 - ∑ i : Fin N, c i *
        ((Int.fract ((1 / ((i.val + 1 : ℕ) : ℝ)) / x) : ℝ) : ℂ) :=
    (Lp.coeFn_sub NymanUnitIntervalMellin.unitTarget (unitSynthesis N c)).trans
      (NymanUnitIntervalMellin.unitTarget_coe_ae.sub
        (NymanUnitIntervalMellin.finite_sum_coe_ae N c (fun i => 1 / ((i.val + 1 : ℕ) : ℝ))))
  have hlocal : (f : ℝ → ℂ) =ᵐ[NymanUnitIntervalMellin.unitMeasure] h := by
    filter_upwards [ae_mono (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl) hf,
      hh, ae_restrict_mem measurableSet_Ioo] with x hfx hhx hx
    rw [hfx, hhx, indicator_of_mem hx]
    simp only [div_div]
  have hunit : (∫ x in Ioo (0 : ℝ) 1, ‖f x‖ ^ 2) = ‖h‖ ^ 2 := by
    rw [squared_norm_integral h]
    apply integral_congr_ae
    filter_upwards [hlocal] with x hx
    rw [hx]
  have htail : (∫ x in Ioi (1 : ℝ), ‖f x‖ ^ 2) = ‖tailMoment N c‖ ^ 2 := by
    have hrep : (fun x => ‖f x‖ ^ 2) =ᵐ[volume.restrict (Ioi (1 : ℝ))]
        fun x => ‖tailMoment N c‖ ^ 2 * x ^ (-2 : ℝ) := by
      filter_upwards [ae_mono (Measure.restrict_mono
        (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)) le_rfl) hf,
        ae_restrict_mem measurableSet_Ioi] with x hfx hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hsum : (∑ i : Fin N, c i *
          ((Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ)) =
            tailMoment N c / (x : ℂ) := by
        rw [tailMoment, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [D5.S3.Observer.Hilbert.NymanHalflineMellinKernel.realSourceVector_tail
          _ (by exact_mod_cast (show 1 ≤ (i.val + 1 : ℕ) by omega)) hx]
        push_cast
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
      have hxnot : x ∉ Ioo (0 : ℝ) 1 := fun hx' => (not_lt_of_ge hx.le) hx'.2
      rw [hfx, indicator_of_notMem hxnot, zero_sub, hsum, norm_neg,
        norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
        Real.rpow_neg hx0.le, Real.rpow_two]
      simp [div_eq_mul_inv, mul_pow]
    rw [integral_congr_ae hrep, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  have hint : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  change ‖f‖ ^ 2 = ‖h‖ ^ 2 + ‖tailMoment N c‖ ^ 2
  rw [squared_norm_integral f]
  change (∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2) = _
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (disjoint_left.mpr (fun x hx hy => (not_lt_of_ge hx.2) hy))
      measurableSet_Ioi (hint.mono_set (fun _ hx => hx.1))
      (hint.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))),
    integral_Ioc_eq_integral_Ioo, hunit, htail]

private theorem centered_mem_B0 (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) :
    centered N c ∈ NymanUnitIntervalMellin.B0 := by
  refine ⟨N + 1, Fin.cons (-tailMoment N c) (fun i => c i),
    Fin.cons 1 (fun i => 1 / ((i.val + 1 : ℕ) : ℝ)), ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases (by norm_num) (fun i => ?_) j
    simp only [Fin.cons_succ]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show 1 ≤ i.val + 1 by omega)
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_one,
      mul_one, Complex.ofReal_div, Complex.ofReal_natCast]
    simp [tailMoment, div_eq_mul_inv]
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp [centered, unitSynthesis, sub_eq_add_neg, neg_smul, add_comm]

/-- An explicit constrained approximant with a quantitative squared-error estimate. -/
theorem centered_approximation (N : ℕ) (c : EuclideanSpace ℂ (Fin N)) :
    centered N c ∈ NymanUnitIntervalMellin.B0 ∧
      ‖NymanUnitIntervalMellin.unitTarget - centered N c‖ ^ 2 ≤
        (1 + ‖NymanUnitIntervalMellin.source 1‖ ^ 2) * ‖target - synthesis N c‖ ^ 2 := by
  refine ⟨centered_mem_B0 N c, ?_⟩
  have ht : ‖NymanUnitIntervalMellin.unitTarget - centered N c‖ ≤
      ‖NymanUnitIntervalMellin.unitTarget - unitSynthesis N c‖ +
        ‖tailMoment N c‖ * ‖NymanUnitIntervalMellin.source 1‖ := by
    calc
      _ = ‖(NymanUnitIntervalMellin.unitTarget - unitSynthesis N c) +
          tailMoment N c • NymanUnitIntervalMellin.source 1‖ := by
        congr 1
        simp [centered, sub_sub_eq_add_sub, sub_add_eq_add_sub]
      _ ≤ ‖NymanUnitIntervalMellin.unitTarget - unitSynthesis N c‖ +
          ‖tailMoment N c • NymanUnitIntervalMellin.source 1‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul]
  have hs : ‖NymanUnitIntervalMellin.unitTarget - centered N c‖ ^ 2 ≤
      (‖NymanUnitIntervalMellin.unitTarget - unitSynthesis N c‖ +
        ‖tailMoment N c‖ * ‖NymanUnitIntervalMellin.source 1‖) ^ 2 := by
    nlinarith [norm_nonneg (NymanUnitIntervalMellin.unitTarget - centered N c),
      norm_nonneg (NymanUnitIntervalMellin.unitTarget - unitSynthesis N c),
      mul_nonneg (norm_nonneg (tailMoment N c)) (norm_nonneg (NymanUnitIntervalMellin.source 1))]
  rw [finite_error_split]
  nlinarith [sq_nonneg (‖NymanUnitIntervalMellin.source 1‖ *
    ‖NymanUnitIntervalMellin.unitTarget - unitSynthesis N c‖ - ‖tailMoment N c‖)]

/-- The literal finite Gram distance controls the constrained unit-interval distance. -/
theorem constrained_distance_le (N : ℕ) :
    Metric.infDist NymanUnitIntervalMellin.unitTarget (closure NymanUnitIntervalMellin.B0) ^ 2 ≤
      (1 + ‖NymanUnitIntervalMellin.source 1‖ ^ 2) * distance N ^ 2 := by
  have hp : (shell N).starProjection target ∈ (synthesis N).range := by
    rw [synthesis_range]
    exact (shell N).starProjection_mem target
  obtain ⟨c, hc⟩ := hp
  have hd : ‖target - synthesis N c‖ = distance N := by
    rw [hc, ← dist_eq_norm, (shell N).dist_starProjection_eq_infDist]
    rfl
  obtain ⟨hmem, hbound⟩ := centered_approximation N c
  have hle : Metric.infDist NymanUnitIntervalMellin.unitTarget (closure NymanUnitIntervalMellin.B0) ≤
      ‖NymanUnitIntervalMellin.unitTarget - centered N c‖ := by
    simpa only [dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (subset_closure hmem)
  calc
    _ ≤ ‖NymanUnitIntervalMellin.unitTarget - centered N c‖ ^ 2 := by
      nlinarith [Metric.infDist_nonneg (x := NymanUnitIntervalMellin.unitTarget)
        (s := closure NymanUnitIntervalMellin.B0), norm_nonneg (NymanUnitIntervalMellin.unitTarget - centered N c)]
    _ ≤ _ := by simpa only [hd] using hbound

#print axioms finite_error_split
#print axioms centered_approximation
#print axioms constrained_distance_le

end D5.S3.Observer.Hilbert.NymanTailCentering
