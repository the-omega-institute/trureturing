/- GID: D5/S3/Observer/ProbabilisticClosure/KernelTranscriptInvariance
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/KernelTranscriptInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal kernel laws give equal randomized transcript laws. -/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureComp

/- Library-search audit trail (2026-08-24):
   * Repository searches for `Kernel`, `transcript`, `postprocess`,
     `Measure.pi`, and law-indistinguishability shapes found no exact theorem.
   * Pinned Mathlib supplies the canonical finite product law `Measure.pi`,
     measure-kernel composition, and `Measure.comp_assoc`. Equality congruence
     over these canonical constructions is the complete proof below.
   * `Kernel.parallelComp` was also found, but `Measure.pi` directly represents
     every finite iid sample size, including zero, without a sibling sampling
     primitive. `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace D5.S3.Observer.ProbabilisticClosure.KernelTranscriptInvariance

/-- Equality of the output laws of a statistical channel at two states is
preserved by every finite iid sample, Markov postprocessor, and randomized
decision kernel. -/
theorem statistical_kernel_transcript_law_invariant
    {X Observation Transcript Decision : Type*}
    [MeasurableSpace X] [MeasurableSpace Observation]
    [MeasurableSpace Transcript] [MeasurableSpace Decision]
    (K : Kernel X Observation) [IsMarkovKernel K]
    (x y : X) (sameLaw : K x = K y)
    (n : Nat) (postprocess : Kernel (Fin n -> Observation) Transcript)
    [IsMarkovKernel postprocess] (decide : Kernel Transcript Decision)
    [IsMarkovKernel decide] :
    decide ∘ₘ (postprocess ∘ₘ Measure.pi (fun _ : Fin n => K x)) =
      decide ∘ₘ (postprocess ∘ₘ Measure.pi (fun _ : Fin n => K y)) := by
  have sameSampleLaw :
      Measure.pi (fun _ : Fin n => K x) =
        Measure.pi (fun _ : Fin n => K y) :=
    congrArg (fun law : Measure Observation =>
      Measure.pi (fun _ : Fin n => law)) sameLaw
  exact congrArg (fun law : Measure (Fin n -> Observation) =>
    decide ∘ₘ (postprocess ∘ₘ law)) sameSampleLaw

#print axioms statistical_kernel_transcript_law_invariant

end D5.S3.Observer.ProbabilisticClosure.KernelTranscriptInvariance
