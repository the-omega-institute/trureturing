/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refutation of universal reciprocal Gamma coefficient positivity using a strictly interior negative second coefficient. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Interior
open D5.S3.Analytic.ReciprocalGammaTuran.Defs
open D5.S3.Analytic.ReciprocalGammaTuran.Interior
namespace D5.S3.Analytic.ReciprocalGammaTuran.Result
/-- The universal coefficient positivity clause is false. -/
theorem result : ¬ claim := by
  obtain ⟨μ, α, β, hμα, hμβ, hα, hβ, hμ, hneg⟩ := interior_failure
  intro h
  have hp := h (fun _ => 1) admissible_one μ α β hα hβ hμ hμα.le hμβ.le 2
  exact (not_lt_of_ge hp.le) hneg
end D5.S3.Analytic.ReciprocalGammaTuran.Result
