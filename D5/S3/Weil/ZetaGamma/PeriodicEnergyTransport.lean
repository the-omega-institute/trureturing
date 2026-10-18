/- GID: D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/PeriodicEnergyTransport
   mirror-E: none(waiver:analytic-periodic-Gamma-energy)
   anchors: []
   utility: none
   digest: Transport original half-open interval L2 correlations through the actual circle and full image lattice. -/

import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ComplexConjugate ENNReal Topology

namespace D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

def zeroExtension (d t : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Ioc t (t + d)).indicator u

def periodicExtension (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (z : ℝ) : ℂ := AddCircle.liftIoc d t u (z : AddCircle d)

/-- There is one exact half-open copy, including at every endpoint. -/
private theorem periodic_copy_and_zero_cancellation
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) :
    periodicExtension d t u z =
      (∑' m : ℤ, zeroExtension d t u (z + m • d)) ∧
    periodicExtension d t u z - zeroExtension d t u z =
      ∑' m : ℤ, if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
  classical
  obtain ⟨m, hm, hUnique⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  have hOnly (n : ℤ) (hn : n ≠ m) :
      zeroExtension d t u (z + n • d) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    exact hn (hUnique n hmem)
  have hCoe : ((z + m • d : ℝ) : AddCircle d) = (z : AddCircle d) := by
    rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have hLift : periodicExtension d t u z = zeroExtension d t u (z + m • d) := by
    have h := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hm
    rw [hCoe] at h
    simpa only [periodicExtension, zeroExtension, Set.indicator_of_mem hm] using h
  have hSum : (∑' n : ℤ, zeroExtension d t u (z + n • d)) =
      zeroExtension d t u (z + m • d) := tsum_eq_single m hOnly
  have hSumNonzero :
      (∑' n : ℤ, if n = 0 then 0 else zeroExtension d t u (z + n • d)) =
        if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
    apply tsum_eq_single m
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [if_neg hn0, hOnly n hn]
  refine ⟨hLift.trans hSum.symm, ?_⟩
  rw [hLift, hSumNonzero]
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hz : zeroExtension d t u z = 0 := by
      simpa using hOnly 0 (Ne.symm hm0)
    simp only [if_neg hm0, hz, sub_zero]

/-- Removing the central copy either removes the whole value or removes zero. -/
theorem periodic_minus_zero_norm_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) :
    ‖periodicExtension d t u z - zeroExtension d t u z‖ ≤
      ‖periodicExtension d t u z‖ := by
  by_cases hz : z ∈ Ioc t (t + d)
  · have hlift := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hz
    simp only [periodicExtension, zeroExtension, Set.indicator_of_mem hz, hlift,
      sub_self, norm_zero, norm_nonneg]
  · simp only [zeroExtension, Set.indicator_of_notMem hz, sub_zero, le_refl]

/-- A chosen half-open copy supplies both the lift value and every other copy's zero. -/
private theorem periodic_copy_at_mem
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) (m : ℤ)
    (hm : z + m • d ∈ Ioc t (t + d)) :
    periodicExtension d t u z = zeroExtension d t u (z + m • d) ∧
      ∀ n : ℤ, n ≠ m → zeroExtension d t u (z + n • d) = 0 := by
  obtain ⟨j, hj, hUnique⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  have hmj : m = j := hUnique m hm
  have hOnly (n : ℤ) (hn : n ≠ m) :
      zeroExtension d t u (z + n • d) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    exact hn ((hUnique n hmem).trans hmj.symm)
  refine ⟨?_, hOnly⟩
  have hCoe : ((z + m • d : ℝ) : AddCircle d) = (z : AddCircle d) := by
    rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have h := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hm
  rw [hCoe] at h
  simpa only [periodicExtension, zeroExtension, Set.indicator_of_mem hm] using h

/-- Absolute values also have exactly one copy; this is the Tonelli input. -/
private theorem weighted_mask_enorm_tsum
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) (c : ℂ) :
    (∑' m : ℤ, ‖if m = 0 then 0 else c * zeroExtension d t u (z + m • d)‖ₑ) =
      ‖c * (periodicExtension d t u z - zeroExtension d t u z)‖ₑ := by
  classical
  obtain ⟨m, hm, _⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  obtain ⟨hlift, hOnly⟩ := periodic_copy_at_mem d t u z m hm
  have hDiff : periodicExtension d t u z - zeroExtension d t u z =
      if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
    rw [hlift]
    by_cases hm0 : m = 0
    · subst m
      simp
    · have hz : zeroExtension d t u z = 0 := by
        simpa using hOnly 0 (Ne.symm hm0)
      simp only [if_neg hm0, hz, sub_zero]
  rw [tsum_eq_single m, hDiff]
  · split_ifs <;> simp
  · intro n hnm
    by_cases hn0 : n = 0
    · simp only [if_pos hn0, enorm_zero]
    · simp only [if_neg hn0, hOnly n hnm, mul_zero, enorm_zero]

abbrev windowMeasure (d t : ℝ) : Measure ℝ :=
  volume.restrict (Ioc t (t + d))

def weightedDifferenceCorrelation
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (w p.2 : ℂ) * conj (u p.1) *
    (periodicExtension d t u (p.1 - p.2) - zeroExtension d t u (p.1 - p.2))

private def weightedLatticeCopy (d t : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  if m = 0 then 0 else
    (w p.2 : ℂ) * conj (u p.1) *
      zeroExtension d t u (p.1 - p.2 + m • d)

private def weightedImageCopy (d : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  if m = 0 then 0 else
    (w (p.1 - p.2 + m • d) : ℂ) * conj (u p.1) * u p.2

def weightedImageKernel (d : ℝ) (w : ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑' m : ℤ, if m = 0 then 0 else w (x - y + m • d)

private theorem weightedLatticeCopy_tsum
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, weightedLatticeCopy d t w u m p) = weightedDifferenceCorrelation d t w u p := by
  simp only [weightedLatticeCopy, weightedDifferenceCorrelation]
  rw [(periodic_copy_and_zero_cancellation d t u (p.1 - p.2)).2]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by split_ifs <;> simp

private theorem weightedLatticeCopy_enorm_tsum
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, ‖weightedLatticeCopy d t w u m p‖ₑ) =
      ‖weightedDifferenceCorrelation d t w u p‖ₑ := by
  exact weighted_mask_enorm_tsum d t u (p.1 - p.2)
    ((w p.2 : ℂ) * conj (u p.1))

/-- Every copy is an indicator of the same actual difference correlation.
No independent integrability premise for a copy is needed. -/
private theorem weightedLatticeCopy_eq_indicator
    (d t : ℝ) (w : ℝ → ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (m : ℤ) (hm : m ≠ 0) :
    weightedLatticeCopy d t w u m =
      {p : ℝ × ℝ | p.1 - p.2 + m • d ∈ Ioc t (t + d)}.indicator
        (weightedDifferenceCorrelation d t w u) := by
  classical
  funext p
  by_cases hp : p.1 - p.2 + m • d ∈ Ioc t (t + d)
  · have hpSet : p ∈ {q : ℝ × ℝ | q.1 - q.2 + m • d ∈ Ioc t (t + d)} := hp
    obtain ⟨hlift, hOnly⟩ := periodic_copy_at_mem d t u (p.1 - p.2) m hp
    have hzero : zeroExtension d t u (p.1 - p.2) = 0 := by
      simpa using hOnly 0 (Ne.symm hm)
    simp only [weightedLatticeCopy, if_neg hm, Set.indicator_of_mem hpSet,
      weightedDifferenceCorrelation, hlift, hzero, sub_zero]
  · have hpSet : p ∉ {q : ℝ × ℝ | q.1 - q.2 + m • d ∈ Ioc t (t + d)} := hp
    simp only [weightedLatticeCopy, if_neg hm, zeroExtension,
      Set.indicator_of_notMem hp, Set.indicator_of_notMem hpSet, mul_zero]

private theorem weightedLatticeCopy_integrable
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume)) (m : ℤ) :
    Integrable (weightedLatticeCopy d t w u m) ((windowMeasure d t).prod volume) := by
  classical
  by_cases hm : m = 0
  · subst m
    change Integrable (fun _ : ℝ × ℝ => (0 : ℂ)) ((windowMeasure d t).prod volume)
    exact integrable_zero (ℝ × ℝ) ℂ ((windowMeasure d t).prod volume)
  · rw [weightedLatticeCopy_eq_indicator d t w u m hm]
    apply hF.indicator
    exact measurableSet_Ioc.preimage (by fun_prop)

/-- The integrable weighted correlation pays the entire countable Tonelli sum. -/
private theorem weightedLatticeCopy_lintegral_norm_sum_ne_top
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume)) :
    (∑' m : ℤ, ∫⁻ p, ‖weightedLatticeCopy d t w u m p‖ₑ
      ∂((windowMeasure d t).prod volume)) ≠ ∞ := by
  rw [← lintegral_tsum (fun m =>
    (weightedLatticeCopy_integrable d t w u hF m).aestronglyMeasurable.enorm)]
  simpa only [weightedLatticeCopy_enorm_tsum] using hF.hasFiniteIntegral.ne

private theorem weightedIntegral_difference_eq_tsum_copies
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume)) :
    (∫ p, weightedDifferenceCorrelation d t w u p ∂((windowMeasure d t).prod volume)) =
      ∑' m : ℤ, ∫ p, weightedLatticeCopy d t w u m p
        ∂((windowMeasure d t).prod volume) := by
  have h := integral_tsum
    (fun m => (weightedLatticeCopy_integrable d t w u hF m).aestronglyMeasurable)
    (weightedLatticeCopy_lintegral_norm_sum_ne_top d t w u hF)
  simpa only [weightedLatticeCopy_tsum] using h

def copyReflection (d : ℝ) (m : ℤ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1, p.1 + m • d - p.2)
  invFun p := (p.1, p.1 + m • d - p.2)
  left_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp <;> ring
  right_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp <;> ring
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    fun_prop

theorem copyReflection_measurePreserving (d t : ℝ) (m : ℤ) :
    MeasurePreserving (copyReflection d m)
      ((windowMeasure d t).prod volume) ((windowMeasure d t).prod volume) := by
  change MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    ((windowMeasure d t).prod volume) ((windowMeasure d t).prod volume)
  exact (MeasurePreserving.id (windowMeasure d t)).skew_product
    (g := fun x y : ℝ => x + m • d - y) (by fun_prop)
    (Filter.Eventually.of_forall fun x =>
      (Measure.measurePreserving_sub_left volume (x + m • d)).map_eq)

theorem windowMeasure_prod_windowMeasure (d t : ℝ) :
    (windowMeasure d t).prod (windowMeasure d t) =
      ((windowMeasure d t).prod volume).restrict (univ ×ˢ Ioc t (t + d)) := by
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := windowMeasure d t) (ν := volume)
      univ (Ioc t (t + d)))

private theorem weightedCopy_reflection_eq_indicator_image
    (d t : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (m : ℤ) :
    weightedLatticeCopy d t w u m ∘ copyReflection d m =
      (univ ×ˢ Ioc t (t + d)).indicator (weightedImageCopy d w u m) := by
  classical
  funext p
  change (if m = 0 then 0 else
    (w (p.1 + m • d - p.2) : ℂ) * conj (u p.1) *
      zeroExtension d t u (p.1 - (p.1 + m • d - p.2) + m • d)) = _
  have hs : p.1 + m • d - p.2 = p.1 - p.2 + m • d := by ring
  have hy : p.1 - (p.1 + m • d - p.2) + m • d = p.2 := by ring
  rw [hy, hs]
  by_cases hm : m = 0
  · have hzero : weightedImageCopy d w u m = 0 := by
      funext q
      simp [weightedImageCopy, hm]
    rw [hzero]
    simp [hm]
  · by_cases hp : p.2 ∈ Ioc t (t + d)
    · have hpProd : p ∈ univ ×ˢ Ioc t (t + d) := ⟨Set.mem_univ _, hp⟩
      simp only [if_neg hm, zeroExtension, Set.indicator_of_mem hp,
        Set.indicator_of_mem hpProd, weightedImageCopy]
    · have hpProd : p ∉ univ ×ˢ Ioc t (t + d) := fun h => hp h.2
      simp only [if_neg hm, zeroExtension, Set.indicator_of_notMem hp,
        mul_zero, Set.indicator_of_notMem hpProd]

private theorem weightedImageCopy_integrable
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume)) (m : ℤ) :
    Integrable (weightedImageCopy d w u m) ((windowMeasure d t).prod (windowMeasure d t)) := by
  have hcomp := (copyReflection_measurePreserving d t m).integrable_comp_of_integrable
    (weightedLatticeCopy_integrable d t w u hF m)
  rw [weightedCopy_reflection_eq_indicator_image d t w u m] at hcomp
  rw [windowMeasure_prod_windowMeasure]
  exact (integrable_indicator_iff (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc)).mp hcomp

/-- Both the complex integral and the nonnegative absolute integral are transported
by the same reflection; the second equality pays the image-side Tonelli exchange. -/
private theorem weightedLatticeCopy_integrals_eq_imageCopy
    (d t : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (m : ℤ) :
    ((∫ p, weightedLatticeCopy d t w u m p ∂((windowMeasure d t).prod volume)) =
      ∫ p, weightedImageCopy d w u m p ∂((windowMeasure d t).prod (windowMeasure d t))) ∧
    ((∫⁻ p, ‖weightedLatticeCopy d t w u m p‖ₑ ∂((windowMeasure d t).prod volume)) =
      ∫⁻ p, ‖weightedImageCopy d w u m p‖ₑ
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  have hMP := copyReflection_measurePreserving d t m
  have hEq := weightedCopy_reflection_eq_indicator_image d t w u m
  have hEqNorm :
      (fun p => ‖weightedLatticeCopy d t w u m (copyReflection d m p)‖ₑ) =
        (univ ×ˢ Ioc t (t + d)).indicator (fun p => ‖weightedImageCopy d w u m p‖ₑ) := by
    funext p
    change ‖(weightedLatticeCopy d t w u m ∘ copyReflection d m) p‖ₑ = _
    rw [hEq]
    exact enorm_indicator_eq_indicator_enorm _ _
  constructor
  · calc
      _ = ∫ p, weightedLatticeCopy d t w u m (copyReflection d m p)
          ∂((windowMeasure d t).prod volume) :=
        (hMP.integral_comp' (weightedLatticeCopy d t w u m)).symm
      _ = ∫ p, (univ ×ˢ Ioc t (t + d)).indicator (weightedImageCopy d w u m) p
          ∂((windowMeasure d t).prod volume) := congrArg (fun F => ∫ p, F p
            ∂((windowMeasure d t).prod volume)) hEq
      _ = _ := by
        rw [integral_indicator (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc),
          ← windowMeasure_prod_windowMeasure]
  · calc
      _ = ∫⁻ p, ‖weightedLatticeCopy d t w u m (copyReflection d m p)‖ₑ
          ∂((windowMeasure d t).prod volume) :=
        (hMP.lintegral_comp_emb (copyReflection d m).measurableEmbedding
          (fun p => ‖weightedLatticeCopy d t w u m p‖ₑ)).symm
      _ = ∫⁻ p, (univ ×ˢ Ioc t (t + d)).indicator (fun p => ‖weightedImageCopy d w u m p‖ₑ) p
          ∂((windowMeasure d t).prod volume) := congrArg (fun F => ∫⁻ p, F p
            ∂((windowMeasure d t).prod volume)) hEqNorm
      _ = _ := by
        rw [lintegral_indicator (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc),
          ← windowMeasure_prod_windowMeasure]

private theorem weightedImageCopy_tsum (d : ℝ) (w : ℝ → ℝ) (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, weightedImageCopy d w u m p) =
      conj (u p.1) * (weightedImageKernel d w p.1 p.2 : ℂ) * u p.2 := by
  classical
  simp only [weightedImageKernel, Complex.ofReal_tsum]
  rw [← tsum_mul_left, ← tsum_mul_right]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp only [weightedImageCopy, if_pos hm, Complex.ofReal_zero, mul_zero, zero_mul]
  · simp only [weightedImageCopy, if_neg hm]
    ring

/-- The actual lattice/Fubini composition. The only upstream payment is the
joint integrability of the weighted actual difference correlation. It is not an assumed image-pairing conclusion. -/
theorem weightedLattice_image_integrable_and_identity
    (d t : ℝ) (w : ℝ → ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (weightedDifferenceCorrelation d t w u)
      ((windowMeasure d t).prod volume)) :
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (weightedImageKernel d w p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    ((∫ p, weightedDifferenceCorrelation d t w u p ∂((windowMeasure d t).prod volume)) =
      ∫ p, conj (u p.1) * (weightedImageKernel d w p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  have hI := weightedImageCopy_integrable d t w u hF
  have hsum : (∑' m : ℤ, ∫⁻ p, ‖weightedImageCopy d w u m p‖ₑ
      ∂((windowMeasure d t).prod (windowMeasure d t))) ≠ ∞ := by
    have hEq : (fun m : ℤ => ∫⁻ p, ‖weightedImageCopy d w u m p‖ₑ
        ∂((windowMeasure d t).prod (windowMeasure d t))) =
        (fun m : ℤ => ∫⁻ p, ‖weightedLatticeCopy d t w u m p‖ₑ
          ∂((windowMeasure d t).prod volume)) := by
      funext m
      exact (weightedLatticeCopy_integrals_eq_imageCopy d t w u m).2.symm
    rw [hEq]
    exact weightedLatticeCopy_lintegral_norm_sum_ne_top d t w u hF
  have hSumInt : Integrable (fun p => ∑' m : ℤ, weightedImageCopy d w u m p)
      ((windowMeasure d t).prod (windowMeasure d t)) := by
    refine ⟨AEStronglyMeasurable.tsum (fun m => (hI m).aestronglyMeasurable), ?_⟩
    apply lt_of_le_of_lt (lintegral_mono (fun p => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun m => (hI m).aestronglyMeasurable.enorm)]
    exact hsum.lt_top
  refine ⟨by simpa only [weightedImageCopy_tsum] using hSumInt, ?_⟩
  calc
    _ = ∑' m : ℤ, ∫ p, weightedLatticeCopy d t w u m p
        ∂((windowMeasure d t).prod volume) :=
      weightedIntegral_difference_eq_tsum_copies d t w u hF
    _ = ∑' m : ℤ, ∫ p, weightedImageCopy d w u m p
        ∂((windowMeasure d t).prod (windowMeasure d t)) :=
      tsum_congr fun m => (weightedLatticeCopy_integrals_eq_imageCopy d t w u m).1
    _ = ∫ p, ∑' m : ℤ, weightedImageCopy d w u m p
        ∂((windowMeasure d t).prod (windowMeasure d t)) :=
      (integral_tsum (fun m => (hI m).aestronglyMeasurable) hsum).symm
    _ = _ := by simp only [weightedImageCopy_tsum]

def windowEnergy (d t : ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ x, ‖u x‖ ^ 2 ∂windowMeasure d t

/-- Every real shift is the pullback of a Haar translation on the actual circle.
No global measurability of the representative u is required. -/
theorem periodic_shift_memLp
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    MemLp (fun x => periodicExtension d t u (x - s)) 2
      (windowMeasure d t) := by
  have hcircle : MemLp (AddCircle.liftIoc d t u) 2 := by
    exact hu.memLp_liftIoc
  have hshift : MeasurePreserving
      (fun x : ℝ => (x : AddCircle d) - (s : AddCircle d))
      (windowMeasure d t) volume :=
    (measurePreserving_sub_right (volume : Measure (AddCircle d))
      (s : AddCircle d)).comp (AddCircle.measurePreserving_mk d t)
  simpa only [periodicExtension, Function.comp_def, AddCircle.coe_sub] using
    hcircle.comp_measurePreserving hshift

/-- The circle volume has total mass d, rather than normalized mass one.
Consequently the shift preserves exactly the unnormalized Lebesgue energy. -/
private theorem periodic_shift_energy_eq
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    (∫ x, ‖periodicExtension d t u (x - s)‖ ^ 2 ∂windowMeasure d t) =
      windowEnergy d t u := by
  calc
    _ = ∫ c : AddCircle d,
        ‖AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2 := by
      simpa only [windowMeasure, periodicExtension, AddCircle.coe_sub] using
        AddCircle.integral_preimage d t
          (fun c : AddCircle d =>
            ‖AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2)
    _ = ∫ c : AddCircle d, ‖AddCircle.liftIoc d t u c‖ ^ 2 :=
      integral_sub_right_eq_self (μ := (volume : Measure (AddCircle d)))
        (fun c : AddCircle d => ‖AddCircle.liftIoc d t u c‖ ^ 2) (s : AddCircle d)
    _ = windowEnergy d t u := by
      rw [← AddCircle.integral_preimage d t]
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]

/-- First pay the actual correlation's integrability, then its energy bound. -/
theorem periodic_correlation_integrable_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    Integrable (fun x => ‖u x‖ * ‖periodicExtension d t u (x - s)‖)
      (windowMeasure d t) ∧
    (∫ x, ‖u x‖ * ‖periodicExtension d t u (x - s)‖ ∂windowMeasure d t) ≤
      windowEnergy d t u := by
  have hp := periodic_shift_memLp d t u hu s
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hp2 := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hmajor := (hu2.add hp2).div_const 2
  have hpoint (x : ℝ) :
      ‖u x‖ * ‖periodicExtension d t u (x - s)‖ ≤
        (‖u x‖ ^ 2 + ‖periodicExtension d t u (x - s)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖u x‖ - ‖periodicExtension d t u (x - s)‖)]
  have hc : Integrable
      (fun x => ‖u x‖ * ‖periodicExtension d t u (x - s)‖)
      (windowMeasure d t) := by
    apply hmajor.mono' (hu.aestronglyMeasurable.norm.mul hp.aestronglyMeasurable.norm)
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hpoint x
  refine ⟨hc, ?_⟩
  calc
    _ ≤ ∫ x,
        (‖u x‖ ^ 2 + ‖periodicExtension d t u (x - s)‖ ^ 2) / 2
          ∂windowMeasure d t := integral_mono hc hmajor hpoint
    _ = (windowEnergy d t u + windowEnergy d t u) / 2 := by
      simp only [integral_div, integral_add hu2 hp2,
        periodic_shift_energy_eq, windowEnergy]
    _ = windowEnergy d t u := by ring

theorem zero_extension_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    MemLp (zeroExtension d t u) 2 volume := by
  exact (memLp_indicator_iff_restrict (μ := volume)
    measurableSet_Ioc.nullMeasurableSet).mpr hu

private theorem zero_extension_energy_eq (d t : ℝ) (u : ℝ → ℂ) :
    (∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2) = windowEnergy d t u := by
  calc
    _ = ∫ x : ℝ, (Ioc t (t + d)).indicator (fun z => ‖u z‖ ^ 2) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc t (t + d)
        · simp only [zeroExtension, Set.indicator_of_mem hx]
        · simp only [zeroExtension, Set.indicator_of_notMem hx, norm_zero, zero_pow
            (by decide : (2 : ℕ) ≠ 0)]
    _ = windowEnergy d t u := integral_indicator measurableSet_Ioc

private theorem zero_shift_energy_eq (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    (∫ x : ℝ, ‖zeroExtension d t u (x - s)‖ ^ 2) = windowEnergy d t u := by
  calc
    _ = ∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2 := integral_sub_right_eq_self _ _
    _ = windowEnergy d t u := zero_extension_energy_eq d t u

private theorem zero_shift_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    MemLp (fun x => zeroExtension d t u (x - s)) 2 (windowMeasure d t) := by
  have hzero := (zero_extension_memLp d t u hu).comp_measurePreserving
    (measurePreserving_sub_right (volume : Measure ℝ) s)
  exact hzero.restrict (Ioc t (t + d))

/-- Joint AE measurability follows from the actual measurable quotient map and
its measure-preserving real-shift fibres, not from iterated AE statements. -/
theorem periodic_shift_joint_aestronglyMeasurable
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => periodicExtension d t u (p.2 - p.1))
      (volume.prod (windowMeasure d t)) := by
  have hq : QuasiMeasurePreserving
      (fun p : ℝ × ℝ => (p.2 : AddCircle d) - (p.1 : AddCircle d))
      (volume.prod (windowMeasure d t)) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      ((measurePreserving_sub_right (volume : Measure (AddCircle d))
        (s : AddCircle d)).comp
          (AddCircle.measurePreserving_mk d t)).quasiMeasurePreserving
  have hcircle : MemLp (AddCircle.liftIoc d t u) 2 := hu.memLp_liftIoc
  simpa only [Function.comp_def, periodicExtension, AddCircle.coe_sub] using
    hcircle.aestronglyMeasurable.comp_quasiMeasurePreserving hq

theorem zero_shift_joint_aestronglyMeasurable
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => zeroExtension d t u (p.2 - p.1))
      (volume.prod (windowMeasure d t)) := by
  have hq : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2 - p.1)
      (volume.prod (windowMeasure d t)) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving.mono_left
        Measure.absolutelyContinuous_restrict
  exact (zero_extension_memLp d t u hu).aestronglyMeasurable.comp_quasiMeasurePreserving hq

def zeroCorrelation (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, conj (zeroExtension d t u x) * zeroExtension d t u (x - s)

def periodicCorrelation (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x, conj (u x) * periodicExtension d t u (x - s) ∂windowMeasure d t

def zeroTranslationEnergy (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ, Complex.normSq (zeroExtension d t u x - zeroExtension d t u (x - s))

def periodicTranslationEnergy (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x, Complex.normSq (u x - periodicExtension d t u (x - s)) ∂windowMeasure d t

theorem l2_complex_correlation_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => conj (f x) * g x) μ := by
  have hnorm : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
    hf.norm.integrable_mul hg.norm
  apply hnorm.mono'
    ((Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖conj (f x) * g x‖ ≤ ‖f x‖ * ‖g x‖
    simp only [norm_mul, Complex.norm_conj, le_refl]

private theorem l2_normSq_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Integrable (fun x => Complex.normSq (f x)) μ := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf

private theorem l2_normSq_difference_expansion
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, Complex.normSq (f x - g x) ∂μ) =
      (∫ x, Complex.normSq (f x) ∂μ) + (∫ x, Complex.normSq (g x) ∂μ) -
        2 * (∫ x, conj (f x) * g x ∂μ).re := by
  have hF := l2_normSq_integrable hf
  have hG := l2_normSq_integrable hg
  have hC := l2_complex_correlation_integrable hf hg
  have hpoint (x : α) : Complex.normSq (f x - g x) =
      Complex.normSq (f x) + Complex.normSq (g x) - 2 * (conj (f x) * g x).re := by
    simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hFG : Integrable (fun x => Complex.normSq (f x) + Complex.normSq (g x)) μ :=
    hF.add hG
  have h2Cr : Integrable (fun x => 2 * (conj (f x) * g x).re) μ := hC.re.const_mul 2
  simp_rw [hpoint]
  have hCre : (∫ x, (conj (f x) * g x).re ∂μ) = (∫ x, conj (f x) * g x ∂μ).re :=
    integral_re hC
  rw [integral_sub hFG h2Cr, integral_add hF hG, integral_const_mul, hCre]

private theorem l2_normSq_difference_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, Complex.normSq (f x - g x) ∂μ) ≤
      2 * ((∫ x, ‖f x‖ ^ 2 ∂μ) + (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have hF := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hG := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hD := l2_normSq_integrable (hf.sub hg)
  have hpoint (x : α) : Complex.normSq (f x - g x) ≤
      2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    rw [Complex.normSq_eq_norm_sq]
    have htriangle := norm_sub_le (f x) (g x)
    have hsquare : ‖f x - g x‖ ^ 2 ≤ (‖f x‖ + ‖g x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
  calc
    _ ≤ ∫ x, 2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) ∂μ :=
      integral_mono hD ((hF.add hG).const_mul 2) hpoint
    _ = _ := by rw [integral_const_mul, integral_add hF hG]

theorem zeroCorrelation_eq_window (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    zeroCorrelation d t u s =
      ∫ x, conj (u x) * zeroExtension d t u (x - s) ∂windowMeasure d t := by
  have hfun : (fun x => conj (zeroExtension d t u x) * zeroExtension d t u (x - s)) =
      (Ioc t (t + d)).indicator
        (fun x => conj (u x) * zeroExtension d t u (x - s)) := by
    funext x
    by_cases hx : x ∈ Ioc t (t + d) <;> simp [zeroExtension, hx]
  unfold zeroCorrelation
  rw [hfun]
  exact integral_indicator measurableSet_Ioc

theorem zeroTranslationEnergy_expansion
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    zeroTranslationEnergy d t u s =
      2 * windowEnergy d t u - 2 * (zeroCorrelation d t u s).re := by
  have hz := zero_extension_memLp d t u hu
  have hzs := hz.comp_measurePreserving (measurePreserving_sub_right volume s)
  have h := l2_normSq_difference_expansion hz hzs
  simpa only [Complex.normSq_eq_norm_sq, zero_extension_energy_eq,
    zero_shift_energy_eq, zeroTranslationEnergy, zeroCorrelation, Function.comp_def, two_mul] using h

theorem periodicTranslationEnergy_expansion
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    periodicTranslationEnergy d t u s =
      2 * windowEnergy d t u - 2 * (periodicCorrelation d t u s).re := by
  have h := l2_normSq_difference_expansion hu (periodic_shift_memLp d t u hu s)
  simpa only [Complex.normSq_eq_norm_sq, periodic_shift_energy_eq,
    windowEnergy, periodicTranslationEnergy, periodicCorrelation, two_mul] using h

theorem zeroCorrelation_neg (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    zeroCorrelation d t u (-s) = conj (zeroCorrelation d t u s) := by
  let f := zeroExtension d t u
  let F : ℝ → ℂ := fun x => conj (conj (f x) * f (x - s))
  calc
    _ = ∫ x : ℝ, F (x + s) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [zeroCorrelation, F, f, sub_neg_eq_add, mul_comm]
    _ = ∫ x : ℝ, F x := integral_add_right_eq_self F s
    _ = _ := integral_conj

private theorem periodicCorrelation_eq_circle
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    periodicCorrelation d t u s =
      ∫ c : AddCircle d, conj (AddCircle.liftIoc d t u c) *
        AddCircle.liftIoc d t u (c - (s : AddCircle d)) := by
  calc
    _ = ∫ x, conj (AddCircle.liftIoc d t u (x : AddCircle d)) *
        AddCircle.liftIoc d t u ((x : AddCircle d) - (s : AddCircle d))
          ∂windowMeasure d t := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      simp only [periodicCorrelation, periodicExtension, AddCircle.coe_sub,
        AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]
    _ = _ := by
      simpa only [windowMeasure] using AddCircle.integral_preimage d t
        (fun c : AddCircle d => conj (AddCircle.liftIoc d t u c) *
          AddCircle.liftIoc d t u (c - (s : AddCircle d)))

theorem periodicCorrelation_neg
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    periodicCorrelation d t u (-s) = conj (periodicCorrelation d t u s) := by
  rw [periodicCorrelation_eq_circle, periodicCorrelation_eq_circle]
  let U := AddCircle.liftIoc d t u
  let F : AddCircle d → ℂ := fun c => conj (conj (U c) * U (c - (s : AddCircle d)))
  calc
    _ = ∫ c : AddCircle d, F (c + (s : AddCircle d)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun c => by
        simp [F, U, AddCircle.coe_neg, sub_neg_eq_add, mul_comm]
    _ = ∫ c : AddCircle d, F c :=
      integral_add_right_eq_self (μ := (volume : Measure (AddCircle d))) F (s : AddCircle d)
    _ = _ := integral_conj

theorem correlation_difference_slice
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    (∫ x, conj (u x) *
      (periodicExtension d t u (x - s) - zeroExtension d t u (x - s))
        ∂windowMeasure d t) = periodicCorrelation d t u s - zeroCorrelation d t u s := by
  have hp := l2_complex_correlation_integrable hu (periodic_shift_memLp d t u hu s)
  have hz := l2_complex_correlation_integrable hu (zero_shift_memLp d t u hu s)
  simp_rw [mul_sub]
  rw [zeroCorrelation_eq_window]
  exact integral_sub hp hz

theorem zeroTranslationEnergy_aestronglyMeasurable
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable (zeroTranslationEnergy d t u) volume := by
  have hz := zero_extension_memLp d t u hu
  have hq : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2 - p.1)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving
  have hshift := hz.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have hjoint := (hz.aestronglyMeasurable.comp_snd.sub hshift).norm.pow 2
  change AEStronglyMeasurable (fun s => ∫ x : ℝ,
    Complex.normSq (zeroExtension d t u x - zeroExtension d t u (x - s))) volume
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def,
    Pi.sub_apply, Pi.pow_apply] using hjoint.integral_prod_right'

theorem periodicTranslationEnergy_aestronglyMeasurable
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable (periodicTranslationEnergy d t u) volume := by
  have hjoint := (hu.aestronglyMeasurable.comp_snd.sub
    (periodic_shift_joint_aestronglyMeasurable d t u hu)).norm.pow 2
  change AEStronglyMeasurable (fun s => ∫ x,
    Complex.normSq (u x - periodicExtension d t u (x - s)) ∂windowMeasure d t) volume
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def,
    Pi.sub_apply, Pi.pow_apply] using hjoint.integral_prod_right'

theorem zeroTranslationEnergy_nonneg_le
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    0 ≤ zeroTranslationEnergy d t u s ∧
      zeroTranslationEnergy d t u s ≤ 4 * windowEnergy d t u := by
  have hz := zero_extension_memLp d t u hu
  have hzs := hz.comp_measurePreserving (measurePreserving_sub_right volume s)
  refine ⟨integral_nonneg fun x => Complex.normSq_nonneg _, ?_⟩
  have h := l2_normSq_difference_bound hz hzs
  change zeroTranslationEnergy d t u s ≤
    2 * ((∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2) +
      ∫ x : ℝ, ‖zeroExtension d t u (x - s)‖ ^ 2) at h
  rw [zero_extension_energy_eq, zero_shift_energy_eq] at h
  nlinarith

theorem periodicTranslationEnergy_nonneg_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    0 ≤ periodicTranslationEnergy d t u s ∧
      periodicTranslationEnergy d t u s ≤ 4 * windowEnergy d t u := by
  refine ⟨integral_nonneg fun x => Complex.normSq_nonneg _, ?_⟩
  have h := l2_normSq_difference_bound hu (periodic_shift_memLp d t u hu s)
  change periodicTranslationEnergy d t u s ≤
    2 * (windowEnergy d t u + ∫ x,
      ‖periodicExtension d t u (x - s)‖ ^ 2 ∂windowMeasure d t) at h
  rw [periodic_shift_energy_eq] at h
  nlinarith

end D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
