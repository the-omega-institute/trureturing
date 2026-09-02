/- GID: D5/S1/Deficit/Beatty/GoldenSpectralCoordinate
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/GoldenSpectralCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden scaling hits one half, with a real-spectrum structural-line iff. -/

import Mathlib

/- Library-search audit trail (2026-09-02):
   * Exact D5 and pinned-Mathlib searches for `goldenNaturalScale`,
     `goldenSpectralParameter`, and both theorem names found no declaration.
   * A D5 body-shape search found the classical critical-line analogue
     `gamma_im_eq_zero_iff_zero_on_critical_line`, but it is restricted to
     stored zeta-zero data and does not define or prove this golden coordinate.
   * Pinned Mathlib supplies `Real.one_lt_goldenRatio`, complex component
     multiplication, and cancellation by a nonzero factor; no whole target
     theorem was found. These component laws are used below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.GoldenSpectralCoordinate

/- The next three constants are transcribed verbatim from
   `D5/X_Frontier/Hearts.lean`. This module deliberately does not import that
   frozen frontier module. -/

/-- The expanding golden eigenvalue. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The structural pole contributed by golden-cube rescaling. -/
noncomputable def structuralPole : ℝ := 1 / phi ^ 3

/-- The structural zero and pulled-back critical line. -/
noncomputable def structuralZero : ℝ := 1 / (2 * phi ^ 2)

/-- Golden-square rescaling of a complex spectral variable. -/
noncomputable def goldenNaturalScale (s : ℂ) : ℂ :=
  (((phi ^ 2 : ℝ) : ℂ) * s)

/-- The centered spectral coordinate after golden-square rescaling. -/
noncomputable def goldenSpectralParameter (s : ℂ) : ℂ :=
  -Complex.I * (goldenNaturalScale s - (1 : ℂ) / 2)

private theorem one_lt_phi : (1 : ℝ) < phi := by
  change (1 : ℝ) < Real.goldenRatio
  exact Real.one_lt_goldenRatio

private theorem phi_pos : (0 : ℝ) < phi :=
  lt_trans one_pos one_lt_phi

private theorem phi_sq_mul_structuralZero :
    phi ^ 2 * structuralZero = 1 / 2 := by
  have hphi : phi ≠ 0 := ne_of_gt phi_pos
  unfold structuralZero
  field_simp

/-- Golden-square rescaling sends the structural zero to one half. -/
theorem golden_natural_scale_hits_half :
    goldenNaturalScale (structuralZero : ℂ) = (1 : ℂ) / 2 := by
  unfold goldenNaturalScale
  rw [← Complex.ofReal_mul, phi_sq_mul_structuralZero]
  push_cast
  ring

/-- The golden spectral coordinate is real exactly on the structural line. -/
theorem golden_spectral_im_eq_zero_iff (s : ℂ) :
    (goldenSpectralParameter s).im = 0 ↔ s.re = structuralZero := by
  have hp2 : (0 : ℝ) < phi ^ 2 := pow_pos phi_pos 2
  have him :
      (goldenSpectralParameter s).im = -(phi ^ 2 * s.re - 1 / 2) := by
    simp [goldenSpectralParameter, goldenNaturalScale, Complex.mul_im,
      Complex.mul_re, -Complex.ofReal_pow]
  rw [him]
  constructor
  · intro h
    have h2 : phi ^ 2 * s.re = 1 / 2 := by linarith
    have h3 : phi ^ 2 * s.re = phi ^ 2 * structuralZero := by
      rw [h2, phi_sq_mul_structuralZero]
    exact mul_left_cancel₀ (ne_of_gt hp2) h3
  · intro h
    rw [h, phi_sq_mul_structuralZero]
    ring

-- The empty hypothesis product and source domain are independently inhabited.
example : Unit := ()
example : Nonempty ℂ := ⟨0⟩

#print axioms golden_natural_scale_hits_half
#print axioms golden_spectral_im_eq_zero_iff

end D5.S1.Deficit.Beatty.GoldenSpectralCoordinate
