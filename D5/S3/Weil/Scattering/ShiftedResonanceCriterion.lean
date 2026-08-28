/- GID: D5/S3/Weil/Scattering/ShiftedResonanceCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/ShiftedResonanceCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the horizontal line of shifted zero resonances. -/

import D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.Scattering.ShiftedResonanceCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum

/-- The shifted resonance construction transports each enumerated zero to the
upper-half-plane point with horizontal coordinate minus its ordinate and
height shifted by its displacement from the critical abscissa. -/
theorem horizontal_resonance_line_iff_critical_line (Z : ZeroData) (omega : ℝ)
    (homega : (1 / 2 : ℝ) ≤ omega) :
    let resonance : ℕ → ℂ := fun n =>
      -((Z.zero n).im : ℂ) + Complex.I *
        ((omega + (Z.zero n).re - criticalAbscissa : ℝ) : ℂ)
    (∀ n, (Z.zero n).re = criticalAbscissa) ↔
      Set.range resonance ∩ {z : ℂ | 0 < z.im} ⊆
        {z : ℂ | z.im = omega} := by
  dsimp
  let resonance : ℕ → ℂ := fun n =>
    -((Z.zero n).im : ℂ) + Complex.I *
      ((omega + (Z.zero n).re - criticalAbscissa : ℝ) : ℂ)
  change (∀ n, (Z.zero n).re = criticalAbscissa) ↔
    Set.range resonance ∩ {z : ℂ | 0 < z.im} ⊆
      {z : ℂ | z.im = omega}
  have him (n : ℕ) : (resonance n).im =
      omega + (Z.zero n).re - criticalAbscissa := by
    simp [resonance]
  have hpos (n : ℕ) : 0 < (resonance n).im := by
    rw [him]
    have hn := (Z.zero_isNontrivial n).2.1
    rw [criticalAbscissa]
    linarith [homega]
  constructor
  · intro h z hz
    rcases hz.1 with ⟨n, rfl⟩
    change (resonance n).im = omega
    rw [him, h n, criticalAbscissa]
    ring
  · intro h n
    have hz : resonance n ∈ Set.range resonance ∩ {z : ℂ | 0 < z.im} :=
      ⟨⟨n, rfl⟩, hpos n⟩
    have hline := h hz
    have hline' : (resonance n).im = omega := hline
    have himline := hline'
    rw [him] at himline
    rw [criticalAbscissa] at himline ⊢
    linarith

end D5.S3.Weil.Scattering.ShiftedResonanceCriterion
