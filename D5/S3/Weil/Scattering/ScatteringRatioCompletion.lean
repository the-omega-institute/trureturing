/- GID: D5/S3/Weil/Scattering/ScatteringRatioCompletion
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/ScatteringRatioCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality of scattering ratios and right-shift normalization determine a nowhere-vanishing meromorphic quotient. -/

import Mathlib

namespace D5.S3.Weil.Scattering.ScatteringRatioCompletion

open Filter

/-!
The source ratio is evaluated on a regular (nowhere-vanishing) function carrier.  The
nonvanishing hypotheses are the pointwise form of working away from poles and zeros;
they let the quotient be manipulated without introducing an artificial choice of values.
-/

theorem scattering_ratio_completion (F G : ℂ → ℂ)
    (hF : ∀ z, F z ≠ 0) (hG : ∀ z, G z ≠ 0)
    (hreading : ∀ s : ℂ,
      F (2 * s - 1) / F (2 * s) = G (2 * s - 1) / G (2 * s))
    (hshift : ∀ z : ℂ,
      Tendsto (fun n : ℕ => F (z + n) / G (z + n)) atTop (nhds 1)) :
    F = G := by
  have hperiod : ∀ z : ℂ, F z / G z = F (z + 1) / G (z + 1) := by
    intro z
    have h := hreading ((z + 1) / 2)
    have hzF : F z ≠ 0 := hF z
    have hzF1 : F (z + 1) ≠ 0 := hF (z + 1)
    have hzG : G z ≠ 0 := hG z
    have hzG1 : G (z + 1) ≠ 0 := hG (z + 1)
    have harg₁ : 2 * ((z + 1) / 2) - 1 = z := by ring
    have harg₂ : 2 * ((z + 1) / 2) = z + 1 := by ring
    rw [harg₁, harg₂] at h
    field_simp [hzF, hzF1, hzG, hzG1] at h ⊢
    exact h
  have hiter : ∀ z : ℂ, ∀ n : ℕ,
      F z / G z = F (z + (n : ℂ)) / G (z + (n : ℂ)) := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          F z / G z = F (z + (n : ℂ)) / G (z + (n : ℂ)) := ih
          _ = F (z + ((n + 1 : ℕ) : ℂ)) / G (z + ((n + 1 : ℕ) : ℂ)) := by
            have hc : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by
              norm_num [Nat.cast_add]
            rw [hc]
            simpa [add_assoc] using hperiod (z + (n : ℂ))
  apply funext
  intro z
  have hconst : Tendsto (fun _ : ℕ => F z / G z) atTop (nhds (F z / G z)) :=
    tendsto_const_nhds
  have hnorm : Tendsto (fun n : ℕ => F (z + n) / G (z + n)) atTop (nhds 1) :=
    hshift z
  have hsame : (fun n : ℕ => F (z + n) / G (z + n)) =ᶠ[atTop]
      (fun _ : ℕ => F z / G z) := by
    filter_upwards [] with n
    exact (hiter z n).symm
  have hquot : F z / G z = 1 := by
    exact tendsto_nhds_unique (hconst.congr' hsame.symm) hnorm
  exact (div_eq_one_iff_eq (hG z)).mp hquot

end D5.S3.Weil.Scattering.ScatteringRatioCompletion
