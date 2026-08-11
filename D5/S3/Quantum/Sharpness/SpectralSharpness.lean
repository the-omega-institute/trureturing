/- GID: D5/S3/Quantum/Sharpness/SpectralSharpness
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SpectralSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The spectral sharpness of a spectrum — the total variation between the spectrum and its reversal, equivalently half the ℓ¹ distance — vanishes exactly when the spectrum is uniform. For an antitone unit-sum spectrum on n points (in particular any sorted probability spectrum) the sharpness is zero iff every entry equals 1/n. A vanishing sharpness forces the spectrum to be palindromic, which under antitonicity collapses to a constant, and the unit sum pins that constant to 1/n. -/

import Mathlib

namespace D5.S3.Quantum.Sharpness.SpectralSharpness

open Finset

/-- The **spectral sharpness** of a spectrum `r : Fin n → ℝ`: the total variation between the
spectrum and its reversal `i ↦ r (Fin.rev i)` — equivalently, half the `ℓ¹` distance. It measures
how far the spectrum is from being palindromic (equal to its own reversal). -/
noncomputable def spectralSharpness {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |r i - r (Fin.rev i)|

/-- **Zero spectral sharpness characterises the uniform spectrum.** For an antitone unit-sum
spectrum `r : Fin n → ℝ` (`Antitone r` with `∑ i, r i = 1`; in particular any sorted probability
spectrum, though nonnegativity is not needed), the spectral sharpness vanishes exactly when the
spectrum is uniform, i.e. `r i = 1 / n` for every `i`.

A vanishing sharpness makes each `|r i - r (Fin.rev i)|` zero, so `r` equals its reversal
(palindromic). In particular `r 0 = r (Fin.last _)`, and antitonicity squeezes every entry between
these two equal values, forcing `r` constant; the unit sum then pins the constant to `1 / n`. The
converse is immediate: a uniform spectrum equals its own reversal, so every summand vanishes.

This is the faithful-freedom-radius clause of the maximal-sharpness law: it records only the
`sharpness = 0 ⇔ uniform` characterisation, not the variational supremum, the median-cut witness,
the qubit reduction, the full-rank saturation criterion, or the data-processing monotonicity of the
same law. -/
theorem spectral_sharpness_zero_iff_uniform {n : ℕ} (r : Fin n → ℝ)
    (hmono : Antitone r) (hsum : ∑ i, r i = 1) :
    spectralSharpness r = 0 ↔ ∀ i, r i = 1 / n := by
  unfold spectralSharpness
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)] at h
    have hpal : ∀ i, r i = r (Fin.rev i) := by
      intro i
      have hi := h i (mem_univ i)
      have := abs_eq_zero.mp hi
      linarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hsum
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h0last : r 0 = r (Fin.last m) := by
      have := hpal 0
      rwa [Fin.rev_zero] at this
    have hconst : ∀ i, r i = r 0 := by
      intro i
      have hle1 : r i ≤ r 0 := hmono (Fin.zero_le i)
      have hle2 : r (Fin.last m) ≤ r i := hmono (Fin.le_last i)
      rw [← h0last] at hle2
      linarith
    intro i
    rw [hconst i]
    have hsc : ∑ _j : Fin (m + 1), r 0 = 1 := by
      rw [← hsum]; exact Finset.sum_congr rfl (fun j _ => (hconst j).symm)
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsc
    field_simp
    linarith [hsc]
  · intro h
    right
    apply Finset.sum_eq_zero
    intro i _
    rw [h i, h (Fin.rev i)]
    simp

end D5.S3.Quantum.Sharpness.SpectralSharpness
