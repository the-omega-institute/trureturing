/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Each off-line zeta zero gives a prime-tail mass bound on fixed-ratio windows. -/

import Mathlib.MeasureTheory.Integral.Prod

/-! Fixed-ratio windows for the negative mass of the actual prime-only Chebyshev tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

/-- A common forward probability average transfers signed mass to positive-part
mass on an interval containing all of the translates. -/
private theorem average_integral_le_positive_mass {f : ℝ → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {a b h l r : ℝ} (hν : ν (Icc 0 h) = 1)
    (hla : l ≤ a) (hab : a ≤ b) (hbr : b + h ≤ r)
    (hf : ContinuousOn f (Icc l r)) :
    (∫ t in a..b, ∫ s, f (t + s) ∂ν) ≤ ∫ t in l..r, max (f t) 0 := by
  have hsupp : ∀ᵐ s ∂ν, s ∈ Icc 0 h :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  have hrestrict : ν.restrict (Icc 0 h) = ν := Measure.restrict_eq_self_of_ae_mem hsupp
  have hadd (t s : ℝ) (ht : t ∈ Icc a b) (hs : s ∈ Icc 0 h) : t + s ∈ Icc l r :=
    ⟨(hla.trans ht.1).trans (le_add_of_nonneg_right hs.1),
      (add_le_add ht.2 hs.2).trans hbr⟩
  have hprod : Integrable (Function.uncurry (fun t s : ℝ => f (t + s)))
      ((volume.restrict (uIoc a b)).prod ν) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => f (p.1 + p.2))
        (Icc a b ×ˢ Icc 0 h) :=
      hf.comp (by fun_prop) (fun p hp => hadd p.1 p.2 hp.1 hp.2)
    have hi := (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (μ := volume.prod ν)).mono_set
      (show uIoc a b ×ˢ Icc 0 h ⊆ Icc a b ×ˢ Icc 0 h from
        prod_mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self) Subset.rfl)
    rw [IntegrableOn, ← Measure.prod_restrict, hrestrict] at hi
    exact hi
  let mass := ∫ t in l..r, max (f t) 0
  have hpos : ContinuousOn (fun t => max (f t) 0) (Icc l r) :=
    hf.sup continuousOn_const
  have hshift : ∀ᵐ s ∂ν, (∫ t in a..b, f (t + s)) ≤ mass := by
    filter_upwards [hsupp] with s hs
    have hleft : l ≤ a + s := hla.trans (le_add_of_nonneg_right hs.1)
    have horder : a + s ≤ b + s := add_le_add_left hab s
    have hright : b + s ≤ r := (add_le_add_right hs.2 b).trans hbr
    have hsubset : Icc (a + s) (b + s) ⊆ Icc l r := Icc_subset_Icc hleft hright
    rw [intervalIntegral.integral_comp_add_right]
    calc
      _ ≤ ∫ t in a + s..b + s, max (f t) 0 :=
        intervalIntegral.integral_mono_on horder ((hf.mono hsubset).intervalIntegrable_of_Icc horder)
          ((hpos.mono hsubset).intervalIntegrable_of_Icc horder) (fun t _ => le_max_left _ _)
      _ ≤ mass := intervalIntegral.integral_mono_interval hleft horder hright
        (ae_of_all _ fun _ => le_max_right _ _) (hpos.intervalIntegrable_of_Icc (hleft.trans (horder.trans hright)))
  rw [intervalIntegral_integral_swap hprod]
  have houter : Integrable (fun s => ∫ t in a..b, f (t + s)) ν := by
    simpa only [uIoc_of_le hab, intervalIntegral.integral_of_le hab, Function.uncurry] using
      hprod.integral_prod_right
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae houter (integrable_const mass) hshift

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
