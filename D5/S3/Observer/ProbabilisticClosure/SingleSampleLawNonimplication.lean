/- GID: D5/S3/Observer/ProbabilisticClosure/SingleSampleLawNonimplication
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/SingleSampleLawNonimplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One supported coupled equality need not identify either laws or states. -/

import Mathlib.Probability.Distributions.Uniform

/- Library-search audit trail (2026-08-24):
   * The current-tree `KernelTranscriptInvariance` theorem proves preservation
     from equal laws, but no deposited theorem supplies the converse
     countermodel required here.
   * Pinned Mathlib exact hits `PMF.map_comp`, `PMF.map_const`, and `PMF.map_id`
     prove the two marginal laws of the explicit coupling and are applied
     directly below.
   * `PMF.support_map`, `PMF.support_pure`, and
     `PMF.support_uniformOfFintype` prove that the equal-output sample has
     nonzero mass while the two marginal laws differ.
   * Searches found no exact theorem packaging all six public countermodel
     clauses. `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.SingleSampleLawNonimplication

/-- There is a finite stochastic channel and a coupling of its laws at two
distinct states with a supported equal-output sample, although the laws remain
unequal. Thus one coupled equality identifies neither law nor state. -/
theorem single_coupled_sample_does_not_determine_law_or_state :
    exists (K : Bool -> PMF Bool) (coupling : PMF (Prod Bool Bool))
      (sample : Prod Bool Bool),
      coupling.map Prod.fst = K false /\
        coupling.map Prod.snd = K true /\
        Ne (coupling sample) 0 /\
        sample.1 = sample.2 /\
        Ne (K false) (K true) /\
        Ne false true := by
  let rightLaw : PMF Bool := PMF.uniformOfFintype Bool
  let coupling : PMF (Prod Bool Bool) := rightLaw.map (fun b => (false, b))
  let K : Bool -> PMF Bool :=
    fun state => if state then rightLaw else PMF.pure false
  refine ⟨K, coupling, (false, false), ?_, ?_, ?_, rfl, ?_, Bool.false_ne_true⟩
  · change (rightLaw.map (fun b => (false, b))).map Prod.fst = PMF.pure false
    rw [PMF.map_comp]
    change rightLaw.map (Function.const Bool false) = PMF.pure false
    exact PMF.map_const rightLaw false
  · change (rightLaw.map (fun b => (false, b))).map Prod.snd = rightLaw
    rw [PMF.map_comp]
    change rightLaw.map id = rightLaw
    exact PMF.map_id rightLaw
  · rw [← PMF.mem_support_iff]
    simp [coupling, rightLaw]
  · intro h_law
    have h_support := congrArg PMF.support h_law
    have h_at_true := Set.ext_iff.mp h_support true
    simp [K, rightLaw] at h_at_true

#print axioms single_coupled_sample_does_not_determine_law_or_state

end D5.S3.Observer.ProbabilisticClosure.SingleSampleLawNonimplication
