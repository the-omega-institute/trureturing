/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSitePhysicalObservation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSitePhysicalObservation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetReflection]
   utility: none
   digest: The selected real observations are the entries of the gain-scaled physical Gram. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetReflection
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation

/-! The real six-site raw chart has the same readout as the complex
adjacent marginal, with the gain as an independent coordinate. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSitePhysicalObservation

open PeriodicMPSSixSiteJetCoordinates PeriodicMPSSixSiteMarginal
open PeriodicMPSFiveSitePhysicalObservation (complexParameter entries rawTrace normalizeEntries)
open PeriodicMPSSixSiteCompactSource (graphPoint normalizedGram observation observation_of_projector)
open scoped ComplexConjugate

open private amplitude entry readout from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetCoordinates
open private map_coordinates from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteJetReflection
open private gaussianToComplex gaussianToComplex_star entries_smul
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSitePhysicalObservation

noncomputable section

/-- The six trace invariants in the chart with mixed trace one. -/
def traceParameter (u : Fin 9 → ℝ) : Fin 6 → ℂ :=
  let q := complexParameter u
  ![q 0, q 0 * q 2, q 0 * q 2 ^ 2, q 1, q 3, 1]

/-- The fourteen necklace amplitudes in the six-site chart. -/
def rayAmplitude (u : Fin 9 → ℝ) : Fin 14 → ℂ :=
  PeriodicMPSSixSiteCompactSource.amplitude (traceParameter u)

private theorem gaussian_amplitude (u : Fin 9 → ℝ) :
    gaussianToComplex ∘ amplitude u = rayAmplitude u := by
  simp only [amplitude, map_coordinates, map_mul, map_pow, map_one] <;> rfl

private theorem gaussian_entry (u : Fin 9 → ℝ) (i j : Fin 4) :
    gaussianToComplex (entry (u 8) (amplitude u) i j) = u 8 • gram (rayAmplitude u) i j := by
  have he (a : Fin 4) (b : Fin 16) :
      gaussianToComplex (flatten (amplitude u) a b) = flatten (rayAmplitude u) a b :=
    congrFun (gaussian_amplitude u) (necklaceTable a b)
  simp only [entry, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, map_mul, map_sum,
    gaussianToComplex_star, he, Complex.star_def, Complex.real_smul]
  rfl

/-- The real raw polynomial reads the gain-scaled physical Gram matrix. -/
theorem raw_eq_entries (u : Fin 9 → ℝ) :
    raw u = entries (u 8 • gram (rayAmplitude u)) := by
  funext j
  fin_cases j <;> first
  | exact congrArg Complex.re (gaussian_entry u _ _)
  | exact congrArg Complex.im (gaussian_entry u _ _)

private theorem gram_middle_diag (p : Fin 14 → ℂ) : gram p 2 2 = gram p 1 1 := by
  simp [gram, flatten, necklaceTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ] <;> ring

theorem raw_trace_eq (u : Fin 9 → ℝ) :
    rawTrace (raw u) = u 8 * (gram (rayAmplitude u)).trace.re := by
  rw [raw_eq_entries, entries_smul]
  have ht (p : Fin 14 → ℂ) :
      (gram p).trace.re = (gram p 0 0).re + 2 * (gram p 1 1).re + (gram p 3 3).re := by
    rw [Matrix.trace, Fin.sum_univ_four]
    simp only [Matrix.diag_apply, gram_middle_diag, Complex.add_re]
    ring
  rw [ht]
  change u 8 * (gram (rayAmplitude u) 0 0).re +
    2 * (u 8 * (gram (rayAmplitude u) 1 1).re) + u 8 * (gram (rayAmplitude u) 3 3).re = _
  ring

/-- A chart point with a defined amplitude ray belongs to the ordinary source. -/
theorem graphPoint_mem_source (u : Fin 9 → ℝ) (hp : rayAmplitude u ≠ 0) :
    graphPoint (traceParameter u) ∈ PeriodicMPSSixSiteCompactSource.source := by
  let q := complexParameter u
  have hq : (traceParameter u 1) ^ 2 = traceParameter u 0 * traceParameter u 2 := by
    change (q 0 * q 2) ^ 2 = q 0 * (q 0 * q 2 ^ 2)
    ring
  exact PeriodicMPSSixSiteCompactSource.ordinary_mem_source ⟨traceParameter u, hq, hp⟩

/-- Dividing by the raw trace gives the normalized compact-chart observation. -/
theorem normalize_raw_eq_observation (u : Fin 9 → ℝ) (hg : u 8 ≠ 0)
    (hp : rayAmplitude u ≠ 0) :
    normalizeEntries (raw u) =
      fun j => entries (observation (graphPoint (traceParameter u))) j.castSucc := by
  have hm := (PeriodicMPSSixSiteCompactSource.gram_mass_pos (rayAmplitude u) hp).ne'
  rw [observation_of_projector (x := graphPoint (traceParameter u)) hp rfl,
    normalizedGram, entries_smul]
  funext j
  unfold normalizeEntries
  rw [raw_trace_eq, raw_eq_entries, entries_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hg, hm] <;> ring

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSitePhysicalObservation
