/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteLawTransport
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteLawTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete tree observations and actual-read probabilities are independent of the containing window. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SpinWindowMarginals
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.RemoteReadSection

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

theorem observation_eq_of_agree (j φ : Bool) (T : ReadTree) (S R : Spins)
    (h : ∀ i ∈ lawWindow T, S i = R i) : observation j φ T S = observation j φ T R := by
  have hr := T.source_run_eq_of_agree φ S R (fun i hi => h i (Finset.mem_union_left _ hi))
  have hq : targetIndex j φ ∈ lawWindow T := by
    cases j <;> cases φ <;> simp [lawWindow, targetIndex]
  simp only [observation, hr, actual_endpoint, h _ hq]

/-- No completion or seed claim is needed for finite coordinate-window consistency. -/
theorem fullMass_enlarge (β : Bias) (V : Finset ℤ) (j : Bool) (T : ReadTree)
    (hV : lawWindow T ⊆ V) (z : Observation) :
    fullMass β V j T z = fullMass β (lawWindow T) j T z := by
  have he (φ : Bool) : SpinWindow.prob β V {S | observation j φ T S = z} =
      SpinWindow.prob β (lawWindow T) {S | observation j φ T S = z} := by
    apply SpinWindow.prob_enlarge β _ _ hV
    intro S R h
    exact congrArg (fun a => a = z) (observation_eq_of_agree j φ T S R h) |>.to_iff
  unfold fullMass
  simp_rw [he]

theorem remoteMass_enlarge (β : Bias) (V : Finset ℤ) (j : Bool) (R : ℕ) (T : ReadTree)
    (hV : lawWindow T ⊆ V) :
    remoteMass β V j R T = remoteMass β (lawWindow T) j R T := by
  have he (φ : Bool) : SpinWindow.prob β V (remoteEvent T j R φ) =
      SpinWindow.prob β (lawWindow T) (remoteEvent T j R φ) := by
    apply SpinWindow.prob_enlarge β _ _ hV
    intro S Q h
    have hr := T.source_run_eq_of_agree φ S Q (fun i hi => h i (Finset.mem_union_left _ hi))
    simp only [remoteEvent, Set.mem_setOf_eq, hr]
  unfold remoteMass
  simp_rw [he]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
