/- GID: D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local positivity equals positive spectral completion modulo invisible support. -/

import Mathlib.Tactic

/-! Library-search audit trail (2026-09-03):
   * Exact and spelling-variant D5 searches covered locally positive spectra,
     positive-definite distribution extension, positive tempered measures,
     inverse Fourier completion, and corrections with external support. No
     theorem states the requested three-way equivalence.
   * `PaleyWienerGauge` owns equality on window-supported tests and
     `ExternalSupportInvisibility` owns one support-invisibility implication;
     neither constructs a positive spectral extension or proves this
     equivalence. Their receipts therefore do not duplicate this atom.
   * The atom remains residual-open with no coverage or Scribe receipt. Digest
     searches also record the positive-definite extension theorem as a missing
     Mathlib bridge rather than an existing owner.
   * Generalized D5 and pinned-Mathlib searches for Bochner-Schwartz, Krein
     extension, positive-definite extension, and Fourier transforms of positive
     tempered measures found no exact theorem. The standard interval extension
     theorem is consequently exposed below as the source's stated
     finite-order/tempered hypothesis, in the one direction actually needed.
   * All local and remote in-flight lane logs were searched for the same
     extension/completion structure. The finite inverse-Poisson criterion on
     `lane/math/dep0903-1` concerns bounded exponential sums and is not an
     equivalent theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.TestFunctions.LocalPositiveSpectrumCompletion

/-- Positivity of the source on all tests visible in the fixed local window. -/
def WellPosed
    {Distribution Test : Type*} [AddCommGroup Distribution]
    (read : Distribution →+ (Test -> Real)) (source : Distribution) : Prop :=
  forall test, 0 <= read source test

/-- A positive spectrum whose inverse Fourier transform agrees with the source
modulo a distribution invisible in the fixed window. -/
def HasPositiveExtension
    {Distribution Spectrum : Type*}
    [AddCommGroup Distribution] [AddCommGroup Spectrum]
    (fourier : Distribution ≃+ Spectrum) (positiveTempered : Spectrum -> Prop)
    (windowKernel : AddSubgroup Distribution) (source : Distribution) : Prop :=
  exists spectrum,
    positiveTempered spectrum /\ fourier.symm spectrum - source ∈ windowKernel

/-- A correction supported in the invisible region which makes the completed
source have positive Fourier spectrum. -/
def HasPositiveCorrection
    {Distribution Spectrum : Type*}
    [AddCommGroup Distribution] [AddCommGroup Spectrum]
    (fourier : Distribution ≃+ Spectrum) (positiveTempered : Spectrum -> Prop)
    (windowKernel : AddSubgroup Distribution) (source : Distribution) : Prop :=
  exists correction,
    correction ∈ windowKernel /\ positiveTempered (fourier (source + correction))

/-- **Local positive-spectrum completion.** Assume the standard finite-order
tempered extension theorem in its constructive direction. Then local positive
definiteness, existence of a positive tempered spectral extension, and
existence of an externally supported correction are equivalent. Both
directions between extension and correction retain explicit witnesses. -/
theorem local_positive_spectrum_completion
    {Distribution Spectrum Test : Type*}
    [AddCommGroup Distribution] [AddCommGroup Spectrum]
    (fourier : Distribution ≃+ Spectrum)
    (read : Distribution →+ (Test -> Real))
    (spectralEnergy : Spectrum -> Test -> Real)
    (positiveTempered : Spectrum -> Prop)
    (windowKernel : AddSubgroup Distribution)
    (source : Distribution)
    (inverseFourierPairing : forall spectrum test,
      read (fourier.symm spectrum) test = spectralEnergy spectrum test)
    (positiveEnergy : forall spectrum,
      positiveTempered spectrum -> forall test, 0 <= spectralEnergy spectrum test)
    (externalInvisible : forall correction,
      correction ∈ windowKernel -> forall test, read correction test = 0)
    (positiveDefiniteExtension :
      WellPosed read source ->
        HasPositiveExtension fourier positiveTempered windowKernel source) :
    (WellPosed read source <->
        HasPositiveExtension fourier positiveTempered windowKernel source) /\
      (HasPositiveExtension fourier positiveTempered windowKernel source <->
        HasPositiveCorrection fourier positiveTempered windowKernel source) := by
  constructor
  · constructor
    · exact positiveDefiniteExtension
    · rintro ⟨spectrum, spectrumPositive, invisibleDifference⟩ test
      have differenceReadsZero :=
        externalInvisible (fourier.symm spectrum - source) invisibleDifference test
      have equalReadings : read (fourier.symm spectrum) test = read source test := by
        have : read (fourier.symm spectrum) test - read source test = 0 := by
          simpa using differenceReadsZero
        exact sub_eq_zero.mp this
      rw [← equalReadings, inverseFourierPairing]
      exact positiveEnergy spectrum spectrumPositive test
  · constructor
    · rintro ⟨spectrum, spectrumPositive, invisibleDifference⟩
      let correction := fourier.symm spectrum - source
      refine ⟨correction, invisibleDifference, ?_⟩
      have sourcePlusCorrection : source + correction = fourier.symm spectrum := by
        dsimp only [correction]
        abel
      rw [sourcePlusCorrection, fourier.apply_symm_apply]
      exact spectrumPositive
    · rintro ⟨correction, correctionInvisible, completionPositive⟩
      refine ⟨fourier (source + correction), completionPositive, ?_⟩
      simpa using correctionInvisible

#print axioms local_positive_spectrum_completion

end D5.S3.Weil.TestFunctions.LocalPositiveSpectrumCompletion
