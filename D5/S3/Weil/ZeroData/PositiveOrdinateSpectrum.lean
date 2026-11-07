/- GID: D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/PositiveOrdinateSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH the positive zeta zeros form a multiplicity-faithful ordinate spectrum. -/

import D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt
import D5.S3.Analytic.Oscillation.OrdinateCounting

/-! The positive zeta ordinate spectrum and its exact multiplicity-weighted count. -/

set_option autoImplicit false

namespace D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum

open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero)

/-- RH makes the imaginary part injective on distinct positive zeta zeros. -/
noncomputable def zetaSpectrum (hRH : RiemannHypothesis) : Spectrum where
  index := PositiveZetaZero
  gamma := fun j => j.val.im
  mult := fun j => Zeta23.zetaZeroConfig.mult j.val
  gamma_pos := fun j => j.property.2
  gamma_injective := by
    intro j k hjk
    apply Subtype.ext
    apply Complex.ext
    · exact (Zeta23.RH_implies_on_line hRH j.property.1).trans
        (Zeta23.RH_implies_on_line hRH k.property.1).symm
    · exact hjk
  mult_pos := fun j => Zeta23.zetaZeroConfig.one_le_mult j.val j.property.1
  finite_le := by
    intro T
    have hfinite := (Zeta23.zetaZeroConfig.finite_window 0 T).preimage
      (show Set.InjOn (fun j : PositiveZetaZero => j.val)
        ((fun j : PositiveZetaZero => j.val) ⁻¹'
          (Zeta23.zetaZeroConfig.carrier ∩ {rho | 0 < rho.im ∧ rho.im ≤ T})) from
        fun _ _ _ _ h => Subtype.ext h)
    exact hfinite.subset (fun j hj => ⟨j.property.1, j.property.2, hj⟩)

/-- The spectrum cutoff count is exactly the canonical positive-window count. -/
theorem zetaSpectrum_N (hRH : RiemannHypothesis) (T : ℝ) :
    (zetaSpectrum hRH).N T = Zeta23.zetaZeroConfig.N 0 T := by
  classical
  rw [Spectrum.N, Zeta23.ZeroConfig.N, Zeta23.ZeroConfig.window,
    finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zetaZeroConfig.finite_window 0 T)]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Spectrum.cut, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj
    simpa only [Set.Finite.mem_toFinset] using
      (show j.val ∈ Zeta23.zetaZeroConfig.carrier ∩
        {rho | 0 < rho.im ∧ rho.im ≤ T} from ⟨j.property.1, j.property.2, hj⟩)
  · intro j _ k _ hjk
    exact Subtype.ext hjk
  · intro rho hrho
    have hr : rho ∈ Zeta23.zetaZeroConfig.carrier ∩
        {rho | 0 < rho.im ∧ rho.im ≤ T} := by
      simpa only [Set.Finite.mem_toFinset] using hrho
    refine ⟨⟨rho, hr.1, hr.2.1⟩, ?_, rfl⟩
    change (⟨rho, hr.1, hr.2.1⟩ : PositiveZetaZero) ∈
      ((zetaSpectrum hRH).finite_le T).toFinset
    exact (((zetaSpectrum hRH).finite_le T).mem_toFinset).mpr hr.2.2
  · intro j _
    rfl

/-- The unconditional Riemann-von Mangoldt count supplies the spectrum asymptotic. -/
theorem zetaSpectrum_countAsymptotic (hRH : RiemannHypothesis) :
    CountAsymptotic (zetaSpectrum hRH) := by
  simpa only [CountAsymptotic, zetaSpectrum_N] using
    CumulativeRiemannVonMangoldt.cumulative_count_asymptotic

end D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
