import CFMPActualLineAngleDerivative283Transient
import Mathlib.Analysis.Convex.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPActualExtendedAngle268Transient
open CFMPActualPositivePrimitive279Transient
open CFMPActualPrimitiveCalibration267Transient (normalizedPrimitive)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPActualAnalyticDiscriminant280Transient
open CFMPActualDegenerateSegment281Transient
open CFMPFiniteExceptionMonotone282Transient
open CFMPActualLineAngleDerivative283Transient

namespace CFMPActualPositiveConvex284Transient

theorem primitive_segment_jensen (F : Lengths → ℝ)
    (hF : ∀ p ∈ positiveLengths, HasFDerivAt F (sourceDifferential p) p)
    (a b : Lengths) (ha : a ∈ positiveLengths) (hb : b ∈ positiveLengths) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      F (AffineMap.lineMap a b t) ≤ (1-t) * F a + t * F b := by
  rcases lineDiscriminant_zero_or_finite a b 0 1 with hzero | hfinite
  · intro t ht
    exact (zero_segment_primitive_affine F hF a b ha hb
      (fun s _ => hzero s) t ht).le
  · let f : ℝ → ℝ := fun t => F (AffineMap.lineMap a b t)
    let S : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ lineDiscriminant a b t = 0}
    have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        AffineMap.lineMap a b t ∈ positiveLengths :=
      positiveLengths_convex.lineMap_mem ha hb ht
    have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt f (directionAngle a b t) t :=
      (hF _ (hpos t ht)).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
      fun t ht => (hD t ht).continuousAt.continuousWithinAt
    have hgc : ContinuousOn (directionAngle a b) (Icc (0 : ℝ) 1) :=
      (sourceDifferential_continuousOn_positive.comp
        AffineMap.lineMap_continuous.continuousOn hpos).eval_const (b-a)
    have hgmono : MonotoneOn (directionAngle a b) (Icc (0 : ℝ) 1) := by
      apply monotoneOn_of_nonneg_derivative_off_finite S hfinite
        (directionAngle a b) 0 1 hgc
      intro t ht hts
      have hne : lineDiscriminant a b t ≠ 0 := by
        intro hz
        exact hts ⟨Ioo_subset_Icc_self ht,hz⟩
      exact directionAngle_nonneg_derivative a b t (hpos t (Ioo_subset_Icc_self ht)) hne
    have hfm : MonotoneOn (deriv f) (interior (Icc (0 : ℝ) 1)) := by
      intro x hx y hy hxy
      rw [(hD x (interior_subset hx)).deriv,(hD y (interior_subset hy)).deriv]
      exact hgmono (interior_subset hx) (interior_subset hy) hxy
    have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f :=
      hfm.convexOn_of_deriv (convex_Icc 0 1) hfc
        (fun t ht => (hD t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    have hj := hconv.2 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,f,
      AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hj

/-- The original angle derivative forces convexity on the positive orthant.
Analytic exceptional zeros and the identically-degenerate segment case are
both included; no convexity of individual flat sectors is assumed. -/
theorem primitive_convexOn_positive (F : Lengths → ℝ)
    (hF : ∀ p ∈ positiveLengths, HasFDerivAt F (sourceDifferential p) p) :
    ConvexOn ℝ positiveLengths F := by
  refine ⟨positiveLengths_convex,?_⟩
  intro a ha b hb c d hc hd hcd
  have hd1 : d ≤ 1 := by linarith
  have hcd' : 1-d = c := by linarith
  simpa only [AffineMap.lineMap_apply_module,hcd',smul_eq_mul] using
    primitive_segment_jensen F hF a b ha hb d ⟨hd,hd1⟩

/-- At any genuine calibration point the constructed segment primitive
extends the same actual physical covolume as a C1 convex function on the
entire strictly positive length domain. -/
theorem positive_C1_convex_actual_extension (a0 : Lengths) (ha0 : genuine a0) :
    ContDiffOn ℝ 1 (normalizedPrimitive (positivePrimitive a0) a0) positiveLengths ∧
      ConvexOn ℝ positiveLengths (normalizedPrimitive (positivePrimitive a0) a0) ∧
      (∀ a ∈ positiveLengths,
        HasFDerivAt (normalizedPrimitive (positivePrimitive a0) a0)
          (sourceDifferential a) a) ∧
      ∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn (normalizedPrimitive (positivePrimitive a0) a0)
          (physicalCovolume G) {a | genuine a} := by
  have h := positive_C1_actual_extension a0 ha0
  exact ⟨h.1,primitive_convexOn_positive _ h.2.1,h.2.1,h.2.2⟩

end CFMPActualPositiveConvex284Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPositiveConvex284Transient.primitive_segment_jensen,
      ``CFMPActualPositiveConvex284Transient.primitive_convexOn_positive,
      ``CFMPActualPositiveConvex284Transient.positive_C1_convex_actual_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP284 actual positive-domain convex covolume absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP284 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP284 CHECKED {name} axioms={axioms}"
