/- GID: D5/S3/Weil/Fredholm/NewmanDeterminantThreshold
   generality: G
   mirror-B: D5/B/S3/Weil/Fredholm/NewmanDeterminantThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized Fredholm, total-positivity, and Stieltjes completion criteria have one nondegenerate threshold. -/

import Mathlib.Topology.Instances.Real.Lemmas

/- Library-search and statement audit (2026-09-03):
   * Searches for Newman determinant thresholds, PF-infinity coefficient
     sequences, reciprocal-zero Stieltjes moments, trace-class determinants,
     and more general completion-threshold bridges found no covering theorem
     in D5 or pinned Mathlib.
   * Nearby `PositiveFredholmProduct` proves convergence of a positive
     square-folded product, but pinned Mathlib has no countable trace-class
     operator API with which to encode the source's determinant criterion.
   * The source's three criteria are not unconditionally equivalent: a
     PF-infinity generating function can have an exponential factor (for
     example `exp x`) and therefore need not be a pure determinant
     `det (I + x U)`. The pointwise equivalences below are consequently an
     explicit normalized, no-exponential-factor bridge rather than a theorem
     asserted without hypotheses.
   * Since Lean defines `sInf ∅ = 0` on the reals, feasibility and a lower
     bound are explicit. Mathlib's `isGLB_csInf` then certifies that each
     displayed threshold is a genuine greatest lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Fredholm.NewmanDeterminantThreshold

noncomputable section

/-- Times at which a completion criterion holds. -/
def completionTimes (criterion : Real → Prop) : Set Real :=
  {time | criterion time}

/-- The lower threshold of a completion criterion. Its public theorems carry
nonemptiness and bounded-below assumptions, avoiding the empty-set convention
for `sInf`. -/
noncomputable def completionThreshold (criterion : Real → Prop) : Real :=
  sInf (completionTimes criterion)

/-- The extra analytic input omitted by the source statement: after removing
the exponential factor and fixing the common normalization, Fredholm
representability, PF-infinity, and the Stieltjes moment condition agree at
each time. -/
structure NormalizedNewmanBridge
    (fredholmCompletion pfInfinityCompletion stieltjesCompletion :
      Real → Prop) : Prop where
  fredholm_iff_pfInfinity : ∀ time,
    fredholmCompletion time ↔ pfInfinityCompletion time
  fredholm_iff_stieltjes : ∀ time,
    fredholmCompletion time ↔ stieltjesCompletion time

/-- Under the explicit normalized bridge and nondegenerate infimum
hypotheses, the Fredholm, PF-infinity, and Stieltjes feasible-time sets have
the same genuine lower threshold. -/
theorem newman_determinant_threshold
    (fredholmCompletion pfInfinityCompletion stieltjesCompletion :
      Real → Prop)
    (bridge : NormalizedNewmanBridge fredholmCompletion
      pfInfinityCompletion stieltjesCompletion)
    (feasible : (completionTimes fredholmCompletion).Nonempty)
    (boundedBelow : BddBelow (completionTimes fredholmCompletion)) :
    completionTimes fredholmCompletion =
        completionTimes pfInfinityCompletion ∧
      completionTimes fredholmCompletion =
        completionTimes stieltjesCompletion ∧
      completionThreshold fredholmCompletion =
        completionThreshold pfInfinityCompletion ∧
      completionThreshold fredholmCompletion =
        completionThreshold stieltjesCompletion ∧
      IsGLB (completionTimes fredholmCompletion)
        (completionThreshold fredholmCompletion) ∧
      IsGLB (completionTimes pfInfinityCompletion)
        (completionThreshold pfInfinityCompletion) ∧
      IsGLB (completionTimes stieltjesCompletion)
        (completionThreshold stieltjesCompletion) := by
  have hFredholmPf : completionTimes fredholmCompletion =
      completionTimes pfInfinityCompletion := by
    apply Set.ext
    intro time
    exact bridge.fredholm_iff_pfInfinity time
  have hFredholmStieltjes : completionTimes fredholmCompletion =
      completionTimes stieltjesCompletion := by
    apply Set.ext
    intro time
    exact bridge.fredholm_iff_stieltjes time
  have hThresholdPf : completionThreshold fredholmCompletion =
      completionThreshold pfInfinityCompletion := by
    exact congrArg sInf hFredholmPf
  have hThresholdStieltjes : completionThreshold fredholmCompletion =
      completionThreshold stieltjesCompletion := by
    exact congrArg sInf hFredholmStieltjes
  have hFredholmGlb : IsGLB (completionTimes fredholmCompletion)
      (completionThreshold fredholmCompletion) := by
    exact isGLB_csInf feasible boundedBelow
  have hPfGlb : IsGLB (completionTimes pfInfinityCompletion)
      (completionThreshold pfInfinityCompletion) := by
    rw [← hFredholmPf, ← hThresholdPf]
    exact hFredholmGlb
  have hStieltjesGlb : IsGLB (completionTimes stieltjesCompletion)
      (completionThreshold stieltjesCompletion) := by
    rw [← hFredholmStieltjes, ← hThresholdStieltjes]
    exact hFredholmGlb
  exact ⟨hFredholmPf, hFredholmStieltjes, hThresholdPf,
    hThresholdStieltjes, hFredholmGlb, hPfGlb, hStieltjesGlb⟩

/-- Each direction of the normalized bridge gives an explicit transport of
a feasible-time witness, rather than merely an equality of infima. -/
theorem normalized_newman_bridge_transports_witnesses
    (fredholmCompletion pfInfinityCompletion stieltjesCompletion :
      Real → Prop)
    (bridge : NormalizedNewmanBridge fredholmCompletion
      pfInfinityCompletion stieltjesCompletion) (time : Real) :
    (fredholmCompletion time →
        pfInfinityCompletion time ∧ stieltjesCompletion time) ∧
      (pfInfinityCompletion time → fredholmCompletion time) ∧
      (stieltjesCompletion time → fredholmCompletion time) := by
  exact ⟨fun h => ⟨(bridge.fredholm_iff_pfInfinity time).mp h,
      (bridge.fredholm_iff_stieltjes time).mp h⟩,
    (bridge.fredholm_iff_pfInfinity time).mpr,
    (bridge.fredholm_iff_stieltjes time).mpr⟩

#print axioms newman_determinant_threshold
#print axioms normalized_newman_bridge_transports_witnesses

end


end D5.S3.Weil.Fredholm.NewmanDeterminantThreshold
