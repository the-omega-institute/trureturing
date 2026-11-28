/- GID: D5/S3/MeasureTheory/MatrixFieldEntropy
   generality: G
   mirror-B: none(waiver:covered-by-observer-crossed-product-entropy-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive scalar weight and a measurable projection determine the trace entropy of matrix fields in a cut-down algebra. -/

import D5.S3.MeasureTheory.BoundedRing
import D5.S3.MeasureTheory.ExponentialClock
import D5.S3.Matrix.BlockEntropy

/-!
Omega original.

A positive scalar weight and a measurable projection determine the trace entropy
of matrix fields in a cut-down algebra. The Klein gap gives an extended-valued
entropy and identifies the normalized trace as the unique maximum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.MeasureTheory.MatrixFieldEntropy

open _root_.MeasureTheory _root_.Matrix Set Omega.Matrix.BlockEntropy
open Omega.MeasureTheory.ExponentialClock
open scoped Omega.MeasureTheory.BoundedRing ENNReal ComplexOrder CStarAlgebra
  MatrixOrder Matrix.Norms.L2Operator

variable {X n : Type*} [MeasurableSpace X] {μ : Measure X}
  [Fintype n] [DecidableEq n]

abbrev Field (n : Type*) {X : Type*} [MeasurableSpace X] (μ : Measure X) :=
  X →ₘ[μ] Matrix n n ℂ

def ofProjection {P : X → Matrix n n ℂ} (hP : Measurable P) : Field n μ :=
  AEEqFun.mk P hP.aestronglyMeasurable

omit [DecidableEq n] in
theorem measurable_trace : Measurable (Matrix.trace : Matrix n n ℂ → ℂ) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp (measurable_pi_apply i)

theorem trace_posSemidef_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i

private theorem trace_posSemidef_re_eq_zero {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.trace.re = 0 ↔ A = 0 := by
  rw [← hA.trace_eq_zero_iff, hA.isHermitian.trace_eq_sum_eigenvalues]
  change (∑ i, (hA.isHermitian.eigenvalues i : ℂ)).re = 0 ↔
    (∑ i, (hA.isHermitian.eigenvalues i : ℂ)) = 0
  simp only [← Complex.ofReal_sum, Complex.ofReal_re, Complex.ofReal_eq_zero]

/-- The extended trace of a positive field, using the real part of its matrix trace. -/
def weight (w : X → ℝ) (A : Field n μ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (w x * (A x).trace.re) ∂μ

/-- The complex trace of an integrable matrix field. -/
def weightedTrace (w : X → ℝ) (A : Field n μ) : ℂ :=
  ∫ x, (w x : ℂ) * (A x).trace ∂μ

/-- Strictly positive weights give faithful traces. -/
theorem weight_faithful {w : X → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (A : Field n μ) (hA : ∀ᵐ x ∂μ, (A x).PosSemidef) :
    weight w A = 0 ↔ A = 0 := by
  let t := fun y => (A y).trace.re
  have ht : Measurable t := Complex.continuous_re.measurable.comp (measurable_trace.comp A.measurable)
  rw [weight, lintegral_ofReal_weighted_eq_zero_iff hw ht (Filter.Eventually.of_forall hpos)
    (hA.mono fun _ => trace_posSemidef_nonneg)]
  constructor
  · intro h
    apply AEEqFun.ext
    filter_upwards [h, hA, AEEqFun.coeFn_zero (α := X) (β := Matrix n n ℂ) (μ := μ)]
      with x hz hx hzero
    exact ((trace_posSemidef_re_eq_zero hx).mp hz).trans hzero.symm
  · rintro rfl
    filter_upwards [AEEqFun.coeFn_zero (α := X) (β := Matrix n n ℂ) (μ := μ)] with x hx
    change ((0 : Field n μ) x).trace.re = 0
    rw [hx]
    simp

/-- Faithfulness of the complex integral on integrable positive fields. -/
theorem weightedTrace_faithful {w : X → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (A : Field n μ) (hA : ∀ᵐ x ∂μ, (A x).PosSemidef)
    (hI : Integrable (fun x => (w x : ℂ) * (A x).trace) μ) :
    weightedTrace w A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hi := hI.re
    have he := integral_re hI
    simp only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul] at hi he
    have hn : (fun _ : X => 0) ≤ᵐ[μ] fun x => w x * (A x).trace.re :=
      hA.mono fun x hx => mul_nonneg (hpos x).le (trace_posSemidef_nonneg hx)
    apply (weight_faithful hw hpos A hA).mp
    rw [weight, ← ofReal_integral_eq_lintegral_ofReal hi hn, he]
    change ENNReal.ofReal (weightedTrace w A).re = 0
    simp [h]
  · intro h
    rw [h, weightedTrace, ← integral_zero (α := X) (G := ℂ) (μ := μ)]
    apply integral_congr_ae
    filter_upwards [AEEqFun.coeFn_zero (α := X) (β := Matrix n n ℂ) (μ := μ)] with x hx
    change (w x : ℂ) * ((0 : Field n μ) x).trace = 0
    rw [hx]
    simp

/-- A positive trace-one density may be unbounded. -/
structure Density (w : X → ℝ) (P : Field n μ) where
  field : Field n μ
  positive : ∀ᵐ x ∂μ, (field x).PosSemidef
  compressed : P * field * P = field
  mass_one : weight w field = 1

variable {P : X → Matrix n n ℂ}

def entropyGapField (P : X → Matrix n n ℂ) (A : Field n μ) (x : X) : Matrix n n ℂ :=
  cfc kleinGap (A x + (1 - P x))

/-- Extended trace entropy, with value minus infinity when the gap has infinite integral. -/
def traceEntropy {w : X → ℝ} (hP : Measurable P) (ρ : Density w (ofProjection (μ := μ) hP)) :
    EReal :=
  -(↑(∫⁻ x, ENNReal.ofReal (w x * (entropyGapField P ρ.field x).trace.re) ∂μ) : EReal)

theorem trace_entropy_le_zero {w : X → ℝ} (hP : Measurable P)
    (ρ : Density w (ofProjection (μ := μ) hP)) : traceEntropy hP ρ ≤ 0 :=
  EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)

/-- The projection is the unique density at which the gap vanishes. -/
theorem trace_entropy_eq_zero_iff {w : X → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (hP : Measurable P) (hCompl : ∀ x, ((1 : Matrix n n ℂ) - P x).PosSemidef)
    (ρ : Density w (ofProjection (μ := μ) hP)) :
    traceEntropy hP ρ = 0 ↔ ρ.field = ofProjection hP := by
  let g := fun x => ENNReal.ofReal (w x * (entropyGapField P ρ.field x).trace.re)
  have hG : Measurable (entropyGapField P ρ.field) :=
    (measurable_matrix_cfc kleinGap kleinGap_continuous).comp
      (ρ.field.measurable.add (measurable_const.sub hP))
  have hg : Measurable g := (hw.mul (Complex.continuous_re.measurable.comp
    (measurable_trace.comp hG))).ennreal_ofReal
  change -(↑(∫⁻ x, g x ∂μ) : EReal) = 0 ↔ _
  rw [EReal.neg_eq_zero_iff, ← EReal.coe_ennreal_zero, EReal.coe_ennreal_injective.eq_iff,
    lintegral_eq_zero_iff hg]
  have hcut := AEEqFun.coeFn_mk (μ := μ) P hP.aestronglyMeasurable
  constructor
  · intro hz
    apply AEEqFun.ext
    filter_upwards [hz, ρ.positive, hcut] with x hgz hx hpx
    have hpad := hx.add (hCompl x)
    have hgap := cfc_kleinGap_nonneg hpad
    have htr := le_antisymm (nonpos_of_mul_nonpos_right (ENNReal.ofReal_eq_zero.mp hgz)
      (hpos x)) (trace_posSemidef_nonneg hgap)
    have hB := (cfc_kleinGap_eq_zero hpad).mp ((trace_posSemidef_re_eq_zero hgap).mp htr)
    change ρ.field x = ofProjection hP x
    rw [show ofProjection hP x = _ from hpx]
    calc
      ρ.field x = (ρ.field x + (1 - P x)) - (1 - P x) := (add_sub_cancel_right _ _).symm
      _ = P x := by rw [hB, sub_sub_cancel]
  · intro h
    dsimp only [g]
    rw [h]
    filter_upwards [hcut] with x hx
    simp only [entropyGapField, show ofProjection hP x = _ from hx, add_sub_cancel]
    rw [(cfc_kleinGap_eq_zero (Matrix.nonneg_iff_posSemidef.mp zero_le_one)).mpr rfl]
    simp

def paddedEntropyTrace (P : X → Matrix n n ℂ) (A : Field n μ) (x : X) : ℝ :=
  (cfc (fun r : ℝ => r * Real.log r) (A x + (1 - P x))).trace.re

private theorem entropyGapTrace_split (P : X → Matrix n n ℂ) (A : Field n μ) (x : X)
    (hA : (A x + (1 - P x)).PosSemidef) :
    (entropyGapField P A x).trace.re = paddedEntropyTrace P A x - (A x).trace.re + (P x).trace.re := by
  let B := A x + (1 - P x)
  have hB : IsSelfAdjoint B := hA.isHermitian.isSelfAdjoint
  have hcalc : cfc kleinGap B = cfc (fun r : ℝ => r * Real.log r) B - A x + P x := by
    unfold kleinGap
    rw [cfc_add_const 1 (fun r : ℝ => r * Real.log r - r) B
      ((Real.continuous_mul_log.sub continuous_id).continuousOn) hB,
      cfc_sub (fun r : ℝ => r * Real.log r) (fun r => r) B
        Real.continuous_mul_log.continuousOn continuous_id.continuousOn, cfc_id' ℝ B hB, map_one]
    dsimp [B]
    abel
  change (cfc kleinGap B).trace.re = _
  rw [hcalc, Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  rfl

/-- For finite entropy the normalized gap integral is the ordinary logarithmic integral. -/
theorem traceEntropy_eq_neg_integral {w : X → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (hP : Measurable P) (hCompl : ∀ x, ((1 : Matrix n n ℂ) - P x).PosSemidef)
    (hUnit : Integrable (fun x => (w x : ℂ) * (ofProjection (μ := μ) hP x).trace) μ)
    (hOne : weightedTrace w (ofProjection (μ := μ) hP) = 1)
    (ρ : Density w (ofProjection (μ := μ) hP))
    (hℓ : Integrable (fun x => w x * paddedEntropyTrace P ρ.field x) μ) :
    traceEntropy hP ρ = (-(∫ x, w x * paddedEntropyTrace P ρ.field x ∂μ) : ℝ) := by
  let g := fun x => w x * (ρ.field x).trace.re
  let j := fun x => w x * (P x).trace.re
  let k := fun x => w x * (entropyGapField P ρ.field x).trace.re
  have hgm : Measurable g := hw.mul
    (Complex.continuous_re.measurable.comp (measurable_trace.comp ρ.field.measurable))
  have hgn : 0 ≤ᵐ[μ] g := ρ.positive.mono fun x hx =>
    mul_nonneg (hpos x).le (trace_posSemidef_nonneg hx)
  have hg : Integrable g μ := (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable hgn).mp
    (by change weight w ρ.field ≠ ∞; rw [ρ.mass_one]; exact ENNReal.one_ne_top)
  have hn : (∫ x, g x ∂μ) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae hgn hg.1]
    change (weight w ρ.field).toReal = 1
    rw [ρ.mass_one, ENNReal.toReal_one]
  have hcut : j =ᵐ[μ] fun x => w x * (ofProjection (μ := μ) hP x).trace.re :=
    (AEEqFun.coeFn_mk (μ := μ) P hP.aestronglyMeasurable).mono fun x h => by
      dsimp [j]
      rw [show ofProjection (μ := μ) hP x = _ from h]
  have hj : Integrable j μ := by
    refine (hUnit.re.congr ?_).congr hcut.symm
    exact Filter.Eventually.of_forall fun x => Complex.re_ofReal_mul _ _
  have hjOne : (∫ x, j x ∂μ) = 1 := by
    rw [integral_congr_ae hcut]
    have hr := integral_re hUnit
    simp only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul] at hr
    rw [hr]
    change (weightedTrace w (ofProjection (μ := μ) hP)).re = 1
    rw [hOne, Complex.one_re]
  have hk : k =ᵐ[μ] fun x => w x * paddedEntropyTrace P ρ.field x - g x + j x :=
    ρ.positive.mono fun x hx => by
      dsimp [k, g, j]
      rw [entropyGapTrace_split P ρ.field x (hx.add (hCompl x))]
      ring
  have hkn : 0 ≤ᵐ[μ] k := ρ.positive.mono fun x hx => mul_nonneg (hpos x).le
    (trace_posSemidef_nonneg (cfc_kleinGap_nonneg (hx.add (hCompl x))))
  exact neg_lintegral_gap_eq hℓ hg hj (hn.trans hjOne.symm) hk hkn

/-- Restriction along a measurable exhaustion realizes the weight of every bounded
positive matrix field as the supremum of finite weights of positive subfields. -/
theorem weight_semifinite {w : X → ℝ} (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hd : Directed (· ⊆ ·) s)
    (hu : (⋃ k, s k) = univ) (hwi : ∀ k, IntegrableOn w (s k) μ)
    (A : Field n μ) (hA : A ∈ BoundedRing.boundedSubring) (hp : ∀ᵐ x ∂μ, 0 ≤ A x) :
    ∃ B : ℕ → Field n μ, (∀ k, B k ∈ BoundedRing.boundedSubring ∧
      (∀ᵐ x ∂μ, 0 ≤ B k x ∧ B k x ≤ A x) ∧ weight w (B k) ≠ ∞) ∧
      weight w A = ⨆ k, weight w (B k) := by
  let B : ℕ → Field n μ := fun k => AEEqFun.mk ((s k).indicator A) ((A.measurable.indicator
    (hs k)).aestronglyMeasurable)
  have hB (k : ℕ) : B k =ᵐ[μ] (s k).indicator A :=
    AEEqFun.coeFn_mk _ _
  have hres (k : ℕ) : weight w (B k) = ∫⁻ x in s k, ENNReal.ofReal (w x * (A x).trace.re) ∂μ := by
    rw [weight, ← lintegral_indicator (hs k)]
    apply lintegral_congr_ae
    filter_upwards [hB k] with x hx
    change ENNReal.ofReal (w x * (B k x).trace.re) =
      (s k).indicator (fun y => ENNReal.ofReal (w y * (A y).trace.re)) x
    rw [hx]
    by_cases h : x ∈ s k <;> simp [h]
  refine ⟨B, ?_, ?_⟩
  · intro k
    have hb : B k ∈ BoundedRing.boundedSubring := by
      obtain ⟨C, hC⟩ := hA
      refine ⟨max C 0, ?_⟩
      filter_upwards [hB k, hC] with x hx hc
      rw [hx]
      by_cases h : x ∈ s k
      · simpa [h] using hc.trans (le_max_left C 0)
      · simp [h]
    have hb₀ : ∀ᵐ x ∂μ, 0 ≤ B k x ∧ B k x ≤ A x := by
      filter_upwards [hB k, hp] with x hx hpx
      rw [hx]
      by_cases h : x ∈ s k <;> simp [h, hpx]
    refine ⟨hb, hb₀, ?_⟩
    let tr : Matrix n n ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap (n := n) ℂ ℂ).toContinuousLinearMap
    have haux := BoundedRing.integrable_weighted_linear (B k) hb tr (hs k) hw hw₀ (hwi k)
      ((hB k).mono fun x hx h => by simp [hx, h])
    change Integrable (fun x => (w x : ℂ) * (B k x).trace) μ at haux
    have hI : Integrable (fun x => w x * (B k x).trace.re) μ := by
      simpa only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul] using haux.re
    unfold weight
    rw [← ofReal_integral_eq_lintegral_ofReal hI (hb₀.mono fun x hx =>
      mul_nonneg (hw₀ x) (trace_posSemidef_nonneg hx.1.posSemidef))]
    exact ENNReal.ofReal_ne_top
  · simp_rw [hres]
    rw [← setLIntegral_iUnion_of_directed _ hd, hu, Measure.restrict_univ]
    rfl

theorem totalWeight_semifinite [Nonempty n] {β : ℝ} (hβ : 0 < β)
    (E : n → ℝ) (A : Field n (volume : Measure ℝ)) (hA : A ∈ BoundedRing.boundedSubring)
    (hp : ∀ᵐ x ∂volume, 0 ≤ A x) :
    ∃ B : ℕ → Field n (volume : Measure ℝ), (∀ k, B k ∈ BoundedRing.boundedSubring ∧
      (∀ᵐ x ∂volume, 0 ≤ B k x ∧ B k x ≤ A x) ∧ weight (totalWeight β E) (B k) ≠ ∞) ∧
      weight (totalWeight β E) A = ⨆ k, weight (totalWeight β E) (B k) := by
  let s (k : ℕ) := Ici (-(k : ℝ))
  have hw : Measurable (totalWeight β E) := by unfold totalWeight; fun_prop
  refine weight_semifinite hw (fun x => (totalWeight_pos hβ E x).le) s
    (fun _ => measurableSet_Ici) ?_ ?_ (fun k => integrableOn_totalWeight hβ E _) A hA hp
  · have hm : Monotone s := by
      intro a b hab
      exact Ici_subset_Ici.mpr (neg_le_neg (Nat.cast_le.mpr hab))
    exact hm.directed_le
  · ext x
    simp only [s, mem_univ, iff_true, mem_iUnion, mem_Ici]
    obtain ⟨k, hk⟩ := exists_nat_gt (-x)
    exact ⟨k, by linarith⟩

end Omega.MeasureTheory.MatrixFieldEntropy
