import CFMPActualAnalyticDiscriminant280Transient
import Mathlib.Topology.Separation.Connected

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPActualExtendedAngle268Transient
open CFMPActualPositivePrimitive279Transient (positiveLengths_convex)
open CFMPActualAnalyticDiscriminant280Transient

namespace CFMPActualDegenerateSegment281Transient

/-- If the original discriminant vanishes along an entire positive segment,
the continuous original angle covector has finite image and is constant.
This treats the identically-zero analytic restriction without discarding it. -/
theorem zero_segment_covector_constant (a b : Lengths)
    (ha : a ∈ positiveLengths) (hb : b ∈ positiveLengths)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, lineDiscriminant a b t = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      sourceDifferential (AffineMap.lineMap a b t) = sourceDifferential a := by
  let H : ℝ → Lengths →L[ℝ] ℝ := fun t => sourceDifferential (AffineMap.lineMap a b t)
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap a b t ∈ positiveLengths :=
    positiveLengths_convex.lineMap_mem ha hb ht
  have hH : ContinuousOn H (Icc (0 : ℝ) 1) :=
    sourceDifferential_continuousOn_positive.comp
      AffineMap.lineMap_continuous.continuousOn hpos
  have hpre : IsPreconnected (H '' Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).isPreconnected.image H hH
  have hfinite : (H '' Icc (0 : ℝ) 1).Finite := by
    apply (Set.finite_range flatDifferential).subset
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨k,hk⟩ := zero_discriminant_has_flat_covector
      (AffineMap.lineMap a b t) (hpos t ht) (hzero t ht)
    exact ⟨k,hk.symm⟩
  have hsub : (H '' Icc (0 : ℝ) 1).Subsingleton :=
    Set.not_nontrivial_iff.mp (fun h => (hpre.infinite_of_nontrivial h) hfinite)
  intro t ht
  have heq : H t = H 0 := hsub (mem_image_of_mem H ht)
    (mem_image_of_mem H ⟨le_refl 0,zero_le_one⟩)
  simpa only [H,AffineMap.lineMap_apply_zero] using heq

/-- Every primitive of the original angle covector is affine on a positive
segment lying identically in the original discriminant-zero set. -/
theorem zero_segment_primitive_affine (F : Lengths → ℝ)
    (hF : ∀ p ∈ positiveLengths, HasFDerivAt F (sourceDifferential p) p)
    (a b : Lengths) (ha : a ∈ positiveLengths) (hb : b ∈ positiveLengths)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, lineDiscriminant a b t = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      F (AffineMap.lineMap a b t) = (1-t) * F a + t * F b := by
  let c : ℝ := sourceDifferential a (b-a)
  have hconstant := zero_segment_covector_constant a b ha hb hzero
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => F (AffineMap.lineMap a b s)) c t := by
    have hd := (hF (AffineMap.lineMap a b t)
      (positiveLengths_convex.lineMap_mem ha hb ht)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
    rw [hconstant t ht] at hd
    exact hd
  have hFTC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      F (AffineMap.lineMap a b t) - F a = t * c := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := t) (f := fun s => F (AffineMap.lineMap a b s))
      (f' := fun _ => c) (fun s hs => hder s (by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1,hs.2.trans ht.2⟩)) intervalIntegrable_const
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
      AffineMap.lineMap_apply_zero] using hi.symm
  have h1 := hFTC 1 ⟨zero_le_one,le_refl 1⟩
  simp only [AffineMap.lineMap_apply_one,one_mul] at h1
  intro t ht
  have htF := hFTC t ht
  rw [← h1] at htF
  nlinarith

end CFMPActualDegenerateSegment281Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualDegenerateSegment281Transient.zero_segment_covector_constant,
      ``CFMPActualDegenerateSegment281Transient.zero_segment_primitive_affine] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP281 original degenerate positive segment absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP281 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP281 CHECKED {name} axioms={axioms}"
