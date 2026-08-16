/- GID: D5/S3/Constants/Transcription/PhiSecondTranscription
   generality: I
   mirror-B: D5/B/S3/Constants/Transcription/PhiSecondTranscription
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Substituting the exact T0 value yields the stated second-order constant. -/

/- Library-search audit trail (2026-08-16):
   * Exact coefficient searches for `27, 13` and `5, 7` found no complete result in
     pinned Mathlib or D5.
   * `D5.S3.Constants.SturmianDirichletValue.sturmianDirichletValue` is the exact
     repository source for T0 and is reused here.
   * Pinned Mathlib supplies `Real.sq_sqrt`, which closes the remaining radical identity.
-/

import D5.S3.Constants.SturmianDirichletValue

namespace D5.S3.Constants.Transcription.PhiSecondTranscription

open D5.S3.Constants.SturmianDirichletValue

/-- Substitution of the exact Sturmian-Dirichlet value into the source's second-order
transcription gives its closed golden-radical form. -/
theorem phi_second_transcription_exact :
    (1 - Real.sqrt 5) * sturmianDirichletValue +
        (15 * Real.sqrt 5 - 33) / 8 =
      (5 * Real.sqrt 5 - 7) / 24 := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  simp only [sturmianDirichletValue]
  nlinarith

#print axioms phi_second_transcription_exact

end D5.S3.Constants.Transcription.PhiSecondTranscription
