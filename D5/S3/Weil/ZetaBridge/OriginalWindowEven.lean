/- GID: D5/S3/Weil/ZetaBridge/OriginalWindowEven
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalWindowEven
   mirror-E: none(waiver:analytic-hilbert-fourier-identification-without-executable-mirror)
   anchors: []
   utility: none
   digest: Original complex AE-even Ioc window sector, representative independence, and parity of the symmetric finite prime image. -/

import D5.S3.Weil.ZetaBridge.PhysicalCosineTailProjection
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalWindowEven

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix PhysicalCosineTailProjection
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition (primeWeight)

abbrev LineL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Exact equality with the existing owner, including its Ioc convention. -/
private lemma owner_zero (a : ℝ) (f : ℝ → ℂ) :
    D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) f =
      zeroExtension a f := by
  simp only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension,
    zeroExtension, window, show -a + 2 * a = a by ring]

private lemma zero_memLp (a : ℝ) (u : WindowL2 a) :
    MemLp (zeroExtension a u) 2 (volume : Measure ℝ) := by
  have hu : MemLp (u : ℝ → ℂ) 2
      (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring, windowMeasure, window] using Lp.memLp u
  simpa only [owner_zero] using
    D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zero_extension_memLp (2 * a) (-a) u hu

private def zeroClass (a : ℝ) (u : WindowL2 a) : LineL2 :=
  (zero_memLp a u).toLp (zeroExtension a u)

private lemma zeroClass_ae (a : ℝ) (u : WindowL2 a) :
    zeroClass a u =ᵐ[volume] zeroExtension a u := (zero_memLp a u).coeFn_toLp

/-- Extension of the AE class by the actual indicator, with no chosen trace. -/
def zeroIsometry (a : ℝ) : WindowL2 a →ₗᵢ[ℂ] LineL2 where
  toFun := zeroClass a
  map_add' u v := by
    apply Lp.ext
    have hwindow : MeasurableSet (window a) := by
      simpa only [window] using (measurableSet_Ioc : MeasurableSet (Ioc (-a) a))
    have h := (ae_eq_restrict_iff_indicator_ae_eq
      (s := window a) (μ := (volume : Measure ℝ)) hwindow).mp
        (Lp.coeFn_add u v)
    filter_upwards [zeroClass_ae a (u + v), zeroClass_ae a u, zeroClass_ae a v,
      Lp.coeFn_add (zeroClass a u) (zeroClass a v), h] with x huv hu hv hadd hi
    rw [huv, hadd, Pi.add_apply, hu, hv]
    by_cases hx : x ∈ Ioc (-a) a
    · simpa only [zeroExtension, window, Set.indicator_of_mem hx, Pi.add_apply] using hi
    · simp only [zeroExtension, window, Set.indicator_of_notMem hx, add_zero]
  map_smul' c u := by
    apply Lp.ext
    have hwindow : MeasurableSet (window a) := by
      simpa only [window] using (measurableSet_Ioc : MeasurableSet (Ioc (-a) a))
    have h := (ae_eq_restrict_iff_indicator_ae_eq
      (s := window a) (μ := (volume : Measure ℝ)) hwindow).mp
        (Lp.coeFn_smul c u)
    filter_upwards [zeroClass_ae a (c • u), zeroClass_ae a u,
      Lp.coeFn_smul c (zeroClass a u), h] with x hcu hu hsm hi
    simp only [RingHom.id_apply]
    rw [hcu, hsm, Pi.smul_apply, hu]
    by_cases hx : x ∈ Ioc (-a) a
    · simpa only [zeroExtension, window, Set.indicator_of_mem hx, Pi.smul_apply] using hi
    · simp only [zeroExtension, window, Set.indicator_of_notMem hx, smul_zero]
  norm_map' u := by
    change ‖(zero_memLp a u).toLp (zeroExtension a u)‖ = ‖u‖
    rw [Lp.norm_toLp]
    change (eLpNorm ((Ioc (-a) a).indicator (u : ℝ → ℂ)) 2 volume).toReal = ‖u‖
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet]
    rfl

lemma zeroIsometry_ae (a : ℝ) (u : WindowL2 a) :
    zeroIsometry a u =ᵐ[volume] zeroExtension a u := zeroClass_ae a u

/-- Whole-line reflection is complex linear, not conjugate linear. -/
def lineReflection : LineL2 →ₗᵢ[ℂ] LineL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ Neg.neg (Measure.measurePreserving_neg (volume : Measure ℝ))

private lemma reflection_ae (f : LineL2) :
    lineReflection f =ᵐ[volume] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- The full original AE-even sector, defined before and without Fourier modes. -/
def originalEven (a : ℝ) : Submodule ℂ (WindowL2 a) :=
  ((lineReflection.toContinuousLinearMap.comp (zeroIsometry a).toContinuousLinearMap) -
    (zeroIsometry a).toContinuousLinearMap).ker

theorem originalEven_isClosed (a : ℝ) : IsClosed (originalEven a : Set (WindowL2 a)) :=
  ContinuousLinearMap.isClosed_ker _

instance originalEven_complete (a : ℝ) : CompleteSpace (originalEven a) :=
  (originalEven_isClosed a).isComplete.completeSpace_coe

theorem mem_originalEven_iff (a : ℝ) (u : WindowL2 a) :
    u ∈ originalEven a ↔
      (fun x : ℝ => zeroExtension a u (-x)) =ᵐ[volume] zeroExtension a u := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (zeroIsometry_ae a u)
  have hR : lineReflection (zeroIsometry a u) =ᵐ[volume]
      (fun x : ℝ => zeroExtension a u (-x)) := (reflection_ae _).trans hneg
  change lineReflection (zeroIsometry a u) - zeroIsometry a u = 0 ↔ _
  rw [sub_eq_zero, Lp.ext_iff]
  exact ⟨fun h => hR.symm.trans (h.trans (zeroIsometry_ae a u)),
    fun h => hR.trans (h.trans (zeroIsometry_ae a u).symm)⟩

/-- AE-class independence on the original interval, including arbitrary endpoint values. -/
theorem originalEven_representative (a : ℝ) (u : WindowL2 a) (f : ℝ → ℂ)
    (huf : (u : ℝ → ℂ) =ᵐ[windowMeasure a] f) :
    u ∈ originalEven a ↔
      (fun x : ℝ => zeroExtension a f (-x)) =ᵐ[volume] zeroExtension a f := by
  have hz : zeroExtension a u =ᵐ[volume] zeroExtension a f :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).mp huf
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hz
  rw [mem_originalEven_iff]
  exact ⟨fun h => hn.symm.trans (h.trans hz), fun h => hn.trans (h.trans hz.symm)⟩

/-- Reflection of Ioc is Ico; its two exceptional endpoints are null. -/
lemma window_reflection_ae (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, (-x ∈ window a ↔ x ∈ window a) := by
  have h₁ : ∀ᵐ x : ℝ ∂volume, x ≠ a := Measure.ae_ne volume a
  have h₂ : ∀ᵐ x : ℝ ∂volume, x ≠ -a := Measure.ae_ne volume (-a)
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  simp only [window, mem_Ioc]
  constructor
  · rintro ⟨hleft, hright⟩
    have hlow : -a ≤ x := by linarith
    have hstrict : -a < x := lt_of_le_of_ne hlow hx₂.symm
    exact ⟨hstrict, by linarith⟩
  · rintro ⟨hleft, hright⟩
    have hstrict : x < a := lt_of_le_of_ne hright hx₁
    exact ⟨by linarith, by linarith⟩

lemma zeroExtension_even_of_even (a : ℝ) (f : ℝ → ℂ)
    (hf : ∀ x, f (-x) = f x) :
    (fun x : ℝ => zeroExtension a f (-x)) =ᵐ[volume] zeroExtension a f := by
  filter_upwards [window_reflection_ae a] with x hx
  by_cases h : x ∈ window a
  · simp only [zeroExtension, Set.indicator_of_mem h,
      Set.indicator_of_mem (hx.mpr h), hf]
  · simp only [zeroExtension, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hn => h (hx.mp hn))]

theorem mode_mem_originalEven (a : ℝ) (n : ℕ) : modeL2 a n ∈ originalEven a := by
  apply (originalEven_representative a (modeL2 a n) (fun x => (mode a n x : ℂ))
    (mode_memLp a n).coeFn_toLp).mpr
  exact zeroExtension_even_of_even a _ (fun x => by rw [mode_even])

theorem head_mem_originalEven (a : ℝ) (N : ℕ) (v : ℕ → ℂ) :
    headL2 a N v ∈ originalEven a := by
  unfold headL2
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.smul_mem _ _ (mode_mem_originalEven a n)

/-- For arbitrary original AE-even input, reflection interchanges the signs of
each physical compressed shift. The outer and inner zero extensions are kept. -/
lemma compression_reflection_ae (a s : ℝ) (f : ℝ → ℂ)
    (hf : (fun x : ℝ => zeroExtension a f (-x)) =ᵐ[volume] zeroExtension a f) :
    (fun x : ℝ => compression a s f (-x)) =ᵐ[volume] compression a (-s) f := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [window_reflection_ae a, ht] with x hx ht
  have ht' : zeroExtension a f (-x + s) = zeroExtension a f (x + -s) := by
    simpa only [Function.comp_def, neg_add_rev, neg_neg, add_comm] using ht
  by_cases h : x ∈ window a
  · simp only [compression, zeroExtension, Set.indicator_of_mem h,
      Set.indicator_of_mem (hx.mpr h)]
    exact ht'
  · simp only [compression, zeroExtension, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hn => h (hx.mp hn))]

lemma symmetric_compression_even (a s : ℝ) (f : ℝ → ℂ)
    (hf : (fun x : ℝ => zeroExtension a f (-x)) =ᵐ[volume] zeroExtension a f) :
    (fun x : ℝ => compression a s f (-x) + compression a (-s) f (-x)) =ᵐ[volume]
      (fun x => compression a s f x + compression a (-s) f x) := by
  filter_upwards [compression_reflection_ae a s f hf,
    compression_reflection_ae a (-s) f hf] with x hp hm
  simpa only [neg_neg, hp, hm, add_comm]

lemma primeAction_supported (a : ℝ) (K : ℕ) (f : ℝ → ℂ) :
    zeroExtension a (primeAction a K f) = primeAction a K f := by
  funext x
  by_cases hx : x ∈ window a
  · simp [zeroExtension, hx]
  · simp [zeroExtension, primeAction, compression, hx]

/-- No primality filter is introduced: every von Mangoldt prime-power term
in the exact Icc is present, with both shifts and arbitrary complex input. -/
lemma primeAction_even (a : ℝ) (K : ℕ) (f : ℝ → ℂ)
    (hf : (fun x : ℝ => zeroExtension a f (-x)) =ᵐ[volume] zeroExtension a f) :
    (fun x : ℝ => primeAction a K f (-x)) =ᵐ[volume] primeAction a K f := by
  have h : ∀ r : ℕ, (fun x : ℝ => compression a (Real.log (r : ℝ)) f (-x) +
      compression a (-Real.log (r : ℝ)) f (-x)) =ᵐ[volume]
      (fun x => compression a (Real.log (r : ℝ)) f x +
        compression a (-Real.log (r : ℝ)) f x) :=
    fun r => symmetric_compression_even a _ f hf
  filter_upwards [ae_all_iff.mpr h] with x hx
  unfold primeAction
  exact Finset.sum_congr rfl fun r _ => congrArg ((primeWeight r : ℂ) * ·) (hx r)

theorem primeHead_mem_originalEven (a : ℝ) (N : ℕ) (v : ℕ → ℂ) :
    primeHeadL2 a N v ∈ originalEven a := by
  apply (originalEven_representative a _ _ (primeHeadL2_ae_action a N v)).mpr
  simp only [primeAction_supported]
  exact primeAction_even a (primeCutoff a) _
    (zeroExtension_even_of_even a _ (profile_even a (Finset.range (N + 1)) v))

end OriginalWindowEven
