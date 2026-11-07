/- GID: D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ZetaSpectrumLocalCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical unit-window zero counts control the positive zeta spectrum. -/

import D5.S3.Analytic.Oscillation.GaussianSpectrum
import D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum

/-! Transport of canonical zero-window counts to positive ordinates. -/

namespace D5.S3.Weil.ZeroData.ZetaSpectrumLocalCount

open D5.S3.Analytic.Oscillation.GaussianSpectrum
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum

/-- The unconditional unit-window estimate controls the positive zeta spectrum. -/
theorem zetaSpectrum_localCount (hRH : RiemannHypothesis) :
    LocalCount (zetaSpectrum hRH) := by
  obtain ⟨A, hA, hcount⟩ :=
    UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt.local_count
  refine ⟨A, hA, ?_⟩
  intro t ht
  rw [zetaSpectrum_N, zetaSpectrum_N]
  have hadd : Zeta23.zetaZeroConfig.N 0 (t + 1) =
      Zeta23.zetaZeroConfig.N 0 t + Zeta23.zetaZeroConfig.N t (t + 1) := by
    exact Zeta23.Ncount_add ht (by linarith)
  rw [hadd, Nat.cast_add, add_sub_cancel_left]
  simpa only [abs_of_nonneg ht] using hcount t

end D5.S3.Weil.ZeroData.ZetaSpectrumLocalCount
