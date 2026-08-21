/- GID: D5/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct
   generality: G
   mirror-B: D5/B/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluate a fractional-reciprocal function against the unit-interval indicator. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Order.SuccPred.IntervalSucc

namespace D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct

open Set MeasureTheory Real
open scoped ENNReal InnerProductSpace MeasureTheory NNReal
open scoped Function

/- Library-search audit trail (2026-08-22):
   * D5 searches for fractional-reciprocal and Euler-constant inner products found no theorem.
   * Pinned Mathlib provides the exact tail evaluation as
     `ZetaAsymptotics.term_tsum_one`; the proof below applies it directly.
   * `L2.inner_indicatorConstLp_one`, `memLp_two_iff_integrable_sq`, and
     `integral_image_eq_integral_abs_deriv_smul` provide the carrier and substitution bridges. -/

/-- Lebesgue measure on the positive half-line, the source Hilbert-space measure. -/
noncomputable def positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- The indicator of `(0, 1)` as a vector in the real `L²(0,∞)` space. -/
noncomputable def unitIntervalIndicator : Lp ℝ 2 positiveMeasure :=
  indicatorConstLp 2 (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)) (by
    change positiveMeasure (Ioo (0 : ℝ) 1) ≠ ∞
    rw [positiveMeasure, Measure.restrict_apply measurableSet_Ioo]
    rw [inter_eq_left.mpr Ioo_subset_Ioi_self]
    exact measure_Ioo_lt_top.ne) (1 : ℝ)

/-- The source fractional-reciprocal function before passage to its `L²` class. -/
noncomputable def fractionalReciprocalFn (a : ℕ) (x : ℝ) : ℝ :=
  Int.fract (1 / ((a : ℝ) * x))

private lemma fractionalReciprocalFn_measurable (a : ℕ) :
    Measurable (fractionalReciprocalFn a) := by
  exact (measurable_const.div (measurable_const.mul measurable_id)).fract

private lemma fractionalReciprocalFn_sq_integrableOn_Ioc (a : ℕ) :
    IntegrableOn (fun x => fractionalReciprocalFn a x ^ 2) (Ioc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      ((fractionalReciprocalFn_measurable a).pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [fractionalReciprocalFn]
    nlinarith [Int.fract_nonneg (1 / ((a : ℝ) * x)),
      Int.fract_lt_one (1 / ((a : ℝ) * x))]

private lemma fractionalReciprocalFn_eq_on_Ioi_one (a : ℕ) (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∈ Ioi (1 : ℝ)) : fractionalReciprocalFn a x = 1 / ((a : ℝ) * x) := by
  rw [fractionalReciprocalFn, Int.fract_eq_self]
  constructor
  · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zero_lt_one.trans hx)))
  · have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have ha0 : (0 : ℝ) < a := zero_lt_one.trans_le haR
    have hax : (a : ℝ) < (a : ℝ) * x := by
      nlinarith [mul_pos ha0 (sub_pos.mpr hx)]
    have hprod : 1 < (a : ℝ) * x := haR.trans_lt hax
    simpa using one_div_lt_one_div_of_lt zero_lt_one hprod

private lemma fractionalReciprocalFn_sq_integrableOn_Ioi (a : ℕ) (ha : 1 ≤ a) :
    IntegrableOn (fun x => fractionalReciprocalFn a x ^ 2) (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hscaled : IntegrableOn (fun x : ℝ => (1 / (a : ℝ) ^ 2) * x ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) := hpow.const_mul _
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change (1 / (a : ℝ) ^ 2) * x ^ (-2 : ℝ) = fractionalReciprocalFn a x ^ 2
  rw [fractionalReciprocalFn_eq_on_Ioi_one a ha hx]
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  rw [show x ^ (-2 : ℝ) = x⁻¹ ^ 2 by
    rw [Real.rpow_neg (le_of_lt (zero_lt_one.trans hx)), Real.rpow_two]
    exact (inv_pow x 2).symm]
  field_simp

private lemma fractionalReciprocalFn_memLp (a : ℕ) (ha : 1 ≤ a) :
    MemLp (fractionalReciprocalFn a) 2 positiveMeasure := by
  apply (memLp_two_iff_integrable_sq
    ((fractionalReciprocalFn_measurable a).aestronglyMeasurable.restrict)).2
  change Integrable (fun x => fractionalReciprocalFn a x ^ 2)
    (volume.restrict (Ioi (0 : ℝ)))
  change IntegrableOn (fun x => fractionalReciprocalFn a x ^ 2) (Ioi (0 : ℝ))
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  exact ⟨fractionalReciprocalFn_sq_integrableOn_Ioc a,
    fractionalReciprocalFn_sq_integrableOn_Ioi a ha⟩

/-- The fractional-reciprocal function as a vector in the exact source carrier `L²(0,∞)`. -/
noncomputable def fractionalReciprocal (a : ℕ) (ha : 1 ≤ a) : Lp ℝ 2 positiveMeasure :=
  (fractionalReciprocalFn_memLp a ha).toLp (fractionalReciprocalFn a)

private lemma fractionalReciprocal_coe_ae (a : ℕ) (ha : 1 ≤ a) :
    (fractionalReciprocal a ha : ℝ → ℝ) =ᵐ[positiveMeasure] fractionalReciprocalFn a := by
  exact MemLp.coeFn_toLp (fractionalReciprocalFn_memLp a ha)

private noncomputable def tailIntegrand (x : ℝ) : ℝ := Int.fract x / x ^ 2

private lemma tailIntegrand_measurable : Measurable tailIntegrand := by
  exact (measurable_fract : Measurable (Int.fract : ℝ → ℝ)).div
    (measurable_id.pow_const 2)

private lemma tailIntegrand_integrableOn_Ioi_one :
    IntegrableOn tailIntegrand (Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  apply hpow.mono' tailIntegrand_measurable.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [tailIntegrand, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (Int.fract_nonneg x) (sq_nonneg x))]
  have hfract : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  rw [show x ^ (-2 : ℝ) = 1 / x ^ 2 by
    rw [Real.rpow_neg (le_of_lt (zero_lt_one.trans hx)), Real.rpow_two, one_div]]
  exact div_le_div_of_nonneg_right hfract (sq_nonneg x)

private lemma tailIntegrand_integrableOn_Ioi (a : ℕ) (ha : 1 ≤ a) :
    IntegrableOn tailIntegrand (Ioi (1 / (a : ℝ))) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlower : 0 < 1 / (a : ℝ) := by positivity
  have hbounded : IntegrableOn tailIntegrand (Ioc (1 / (a : ℝ)) 1) := by
    apply Measure.integrableOn_of_bounded (M := 1 / (1 / (a : ℝ)) ^ 2)
        measure_Ioc_lt_top.ne
        tailIntegrand_measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [tailIntegrand, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Int.fract_nonneg x) (sq_nonneg x))]
    have hfract : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
    have hx_sq : (1 / (a : ℝ)) ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ hlower.le (hlower.trans hx.1).le).2 hx.1.le
    exact div_le_div₀ zero_le_one hfract (sq_pos_of_pos hlower) hx_sq
  have hlower_le : 1 / (a : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one haR
  rw [← Ioc_union_Ioi_eq_Ioi hlower_le, integrableOn_union]
  exact ⟨hbounded, tailIntegrand_integrableOn_Ioi_one⟩

private lemma image_fractional_substitution (a : ℕ) (ha : 1 ≤ a) :
    (fun x : ℝ => (1 / (a : ℝ)) * x⁻¹) '' Ioo 0 1 = Ioi (1 / (a : ℝ)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (zero_lt_one.trans_le ha)
    rw [mem_Ioi]
    have hax : (a : ℝ) * x < (a : ℝ) := by
      nlinarith [mul_pos ha0 (sub_pos.mpr hx.2)]
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
      one_div_lt_one_div_of_lt (mul_pos ha0 hx.1) hax
  · intro hy
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (zero_lt_one.trans_le ha)
    have hy0 : 0 < y := (one_div_pos.mpr ha0).trans hy
    refine ⟨1 / ((a : ℝ) * y), ?_, ?_⟩
    · constructor
      · positivity
      · have hprod : 1 < (a : ℝ) * y := by
          have := (div_lt_iff₀ ha0).1 hy
          nlinarith
        simpa using one_div_lt_one_div_of_lt zero_lt_one hprod
    · field_simp [ha0.ne', hy0.ne']

private lemma unit_interval_integral_eq_scaled_tail (a : ℕ) (ha : 1 ≤ a) :
    ∫ x in Ioo (0 : ℝ) 1, fractionalReciprocalFn a x =
      (1 / (a : ℝ)) * ∫ t in Ioi (1 / (a : ℝ)), tailIntegrand t := by
  let transform : ℝ → ℝ := fun x => (1 / (a : ℝ)) * x⁻¹
  let transform' : ℝ → ℝ := fun x => -(1 / (a : ℝ)) * (x ^ 2)⁻¹
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (zero_lt_one.trans_le ha)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt transform (transform' x) (Ioo (0 : ℝ) 1) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    change HasDerivWithinAt (fun y : ℝ => (1 / (a : ℝ)) * y⁻¹)
      (-(1 / (a : ℝ)) * (x ^ 2)⁻¹) (Ioo (0 : ℝ) 1) x
    simpa only [mul_neg, neg_mul] using
      ((hasDerivAt_inv hx0).const_mul (1 / (a : ℝ))).hasDerivWithinAt
  have hinj : Set.InjOn transform (Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    dsimp [transform] at hxy
    field_simp [ha0.ne', hx0, hy0] at hxy
    exact hxy.symm
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj tailIntegrand
  rw [image_fractional_substitution a ha] at hchange
  rw [hchange]
  have hintegrand : ∀ x ∈ Ioo (0 : ℝ) 1,
      |transform' x| • tailIntegrand (transform x) =
        (a : ℝ) * fractionalReciprocalFn a x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have haR0 : (a : ℝ) ≠ 0 := ne_of_gt ha0
    simp only [transform', transform, tailIntegrand, fractionalReciprocalFn]
    rw [abs_mul, abs_neg, abs_of_nonneg (one_div_nonneg.mpr ha0.le),
      abs_inv, abs_pow, abs_of_pos hx.1]
    simp only [smul_eq_mul]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hintegrand, ← integral_const_mul]
  field_simp

private lemma tail_interval_integral_eq_term (n : ℕ) :
    ∫ x in Ioc ((n + 1 : ℕ) : ℝ) ((n + 1 + 1 : ℕ) : ℝ), tailIntegrand x =
      ZetaAsymptotics.term (n + 1) 1 := by
  rw [ZetaAsymptotics.term, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  norm_num only [Nat.cast_add, Nat.cast_one]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hfloor : ⌊x⌋ = (n + 1 : ℕ) := by
    rw [Int.floor_eq_iff]
    norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    exact ⟨hx.1.le, hx.2⟩
  rw [tailIntegrand, Int.fract, hfloor]
  norm_cast

private lemma tail_integral_eq_one_sub_euler :
    ∫ x in Ioi (1 : ℝ), tailIntegrand x = 1 - Real.eulerMascheroniConstant := by
  let intervals : ℕ → Set ℝ := fun n =>
    Ioc ((n + 1 : ℕ) : ℝ) ((n + 1 + 1 : ℕ) : ℝ)
  have hmono : Monotone (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    intro m n h
    simpa only [Nat.cast_le] using Nat.add_le_add_right h 1
  have hdisjoint : Pairwise (Disjoint on intervals) := by
    simpa [intervals, Nat.cast_add, Nat.cast_one, add_assoc] using
      hmono.pairwise_disjoint_on_Ioc_succ
  have hunion : ⋃ n, intervals n = Ioi (1 : ℝ) := by
    dsimp [intervals]
    simpa [show (⊥ : ℕ) = 0 by rfl, Order.succ_eq_add_one, Nat.cast_add] using
      iUnion_Ioc_map_succ_eq_Ioi
        (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ)) (by simp)
        (by
        rw [not_bddAbove_iff]
        intro b
        obtain ⟨n, hn⟩ := exists_nat_gt b
        exact ⟨((n + 1 : ℕ) : ℝ), ⟨n, rfl⟩, hn.trans_le (by norm_num)⟩)
  have hsum := hasSum_integral_iUnion (f := tailIntegrand)
    (fun _ => measurableSet_Ioc) hdisjoint
    (hunion.symm ▸ tailIntegrand_integrableOn_Ioi_one)
  rw [hunion] at hsum
  have hsum' : HasSum (fun n => ZetaAsymptotics.term (n + 1) 1)
      (∫ x in Ioi (1 : ℝ), tailIntegrand x) := by
    apply HasSum.congr_fun hsum
    intro n
    exact (tail_interval_integral_eq_term n).symm
  exact hsum'.unique ZetaAsymptotics.term_tsum_one

private lemma tail_integral_closed_form (a : ℕ) (ha : 1 ≤ a) :
    ∫ x in Ioi (1 / (a : ℝ)), tailIntegrand x =
      Real.log a + 1 - Real.eulerMascheroniConstant := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (zero_lt_one.trans_le ha)
  have hlower : 0 < 1 / (a : ℝ) := one_div_pos.mpr ha0
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlower_le : 1 / (a : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one haR
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (tailIntegrand_integrableOn_Ioi a ha)
    tailIntegrand_integrableOn_Ioi_one
  have hinterval : ∫ x : ℝ in 1 / (a : ℝ)..1, tailIntegrand x = Real.log a := by
    calc
      ∫ x : ℝ in 1 / (a : ℝ)..1, tailIntegrand x =
          ∫ x : ℝ in 1 / (a : ℝ)..1, 1 / x := by
            apply intervalIntegral.integral_congr_uIoo
            intro x hx
            rw [uIoo_of_le hlower_le] at hx
            rw [tailIntegrand, Int.fract_eq_self.2]
            · field_simp
            · exact ⟨(hlower.trans hx.1).le, hx.2⟩
      _ = Real.log (1 / (1 / (a : ℝ))) :=
        integral_one_div_of_pos hlower zero_lt_one
      _ = Real.log a := by field_simp
  rw [hinterval, tail_integral_eq_one_sub_euler] at hsplit
  linarith

/-- The integer-indexed source vector, constructed through its positive natural representative. -/
noncomputable def integerFractionalReciprocal (a : ℤ) (ha : 1 ≤ a) :
    Lp ℝ 2 positiveMeasure :=
  fractionalReciprocal a.toNat (by omega)

private theorem fractional_reciprocal_inner_product_nat (a : ℕ) (ha : 1 ≤ a) :
    @inner ℝ (Lp ℝ 2 positiveMeasure) _ unitIntervalIndicator (fractionalReciprocal a ha) =
      (Real.log a + 1 - Real.eulerMascheroniConstant) / a := by
  rw [unitIntervalIndicator, L2.inner_indicatorConstLp_one]
  rw [setIntegral_congr_ae measurableSet_Ioo
    ((fractionalReciprocal_coe_ae a ha).mono fun _ h _ => h)]
  rw [positiveMeasure, Measure.restrict_restrict measurableSet_Ioo]
  have hinter : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 := inter_eq_left.mpr Ioo_subset_Ioi_self
  rw [hinter, unit_interval_integral_eq_scaled_tail a ha, tail_integral_closed_form a ha]
  field_simp

/-- For every integer `a ≥ 1`, the inner product of the unit-interval indicator with
`x ↦ fract(1 / (a*x))` in the real Hilbert space `L²(0,∞)` has the stated Euler-constant value. -/
theorem fractional_reciprocal_inner_product (a : ℤ) (ha : 1 ≤ a) :
    @inner ℝ (Lp ℝ 2 positiveMeasure) _ unitIntervalIndicator
        (integerFractionalReciprocal a ha) =
      (Real.log (a : ℝ) + 1 - Real.eulerMascheroniConstant) / (a : ℝ) := by
  have hnat : 1 ≤ a.toNat := by omega
  have hcast : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
    norm_cast
    exact Int.toNat_of_nonneg (by omega)
  simpa only [integerFractionalReciprocal, hcast] using
    fractional_reciprocal_inner_product_nat a.toNat hnat

#print axioms fractional_reciprocal_inner_product

end D5.S3.Constants.InnerProducts.FractionalReciprocalInnerProduct
