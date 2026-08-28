/- GID: D5/S3/Observer/WindowAlgebra/DynamicalObservableKernel
   generality: G
   mirror-B: D5/B/S3/Observer/WindowAlgebra/DynamicalObservableKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The generated real observable algebra has exactly the complete-itinerary kernel. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-27):
   * Exact repository hit `ItineraryCompletion.completeItinerary` supplies the
     canonical future-readout word and is imported rather than redeclared.
   * The nearby `ObservableAlgebraClosureDuality` theorem is complex-valued;
     it is not an exact hit for the source's real function algebra.
   * Pinned Mathlib searches found no exact real dynamical-algebra kernel
     theorem. `Algebra.adjoin_induction` and `Algebra.subset_adjoin` supply the
     canonical generated-algebra induction and generator inclusion. -/

namespace D5.S3.Observer.WindowAlgebra.DynamicalObservableKernel

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Agreement under every real observable generated from an iterated readout
is exactly equality of the complete future readout. -/
theorem dynamical_observable_kernel
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    let observableAlgebra : Subalgebra ℝ (Y -> ℝ) :=
      Algebra.adjoin ℝ
        {f : Y -> ℝ | ∃ n : Nat, ∃ h : Set.range readout -> ℝ,
          f = h ∘ Set.rangeFactorization readout ∘ (update^[n])}
    (fun x y => ∀ f, f ∈ observableAlgebra -> f x = f y) =
      Setoid.ker (completeItinerary update readout) := by
  classical
  dsimp only
  funext x y
  apply propext
  constructor
  · intro hagree
    change completeItinerary update readout x =
      completeItinerary update readout y
    funext n
    by_contra hne
    let detector : Set.range readout -> ℝ := fun z =>
      if z.1 = readout ((update^[n]) x) then 1 else 0
    let generator : Y -> ℝ :=
      detector ∘ Set.rangeFactorization readout ∘ (update^[n])
    have hgenerator : generator ∈ Algebra.adjoin ℝ
        {f : Y -> ℝ | ∃ k : Nat, ∃ h : Set.range readout -> ℝ,
          f = h ∘ Set.rangeFactorization readout ∘ (update^[k])} :=
      Algebra.subset_adjoin ⟨n, detector, rfl⟩
    have hequal := hagree generator hgenerator
    simp [generator, detector] at hequal
    by_cases sameReadout :
        readout ((update^[n]) y) = readout ((update^[n]) x)
    · exact hne sameReadout.symm
    · simp [sameReadout] at hequal
  · intro hitinerary f hf
    change completeItinerary update readout x =
      completeItinerary update readout y at hitinerary
    induction hf using Algebra.adjoin_induction with
    | mem generator hgenerator =>
        rcases hgenerator with ⟨n, h, rfl⟩
        have hn := congrFun hitinerary n
        apply congrArg h
        apply Subtype.ext
        exact hn
    | algebraMap r => rfl
    | add first second _ _ hfirst hsecond =>
        simpa only [Pi.add_apply] using congrArg₂ (· + ·) hfirst hsecond
    | mul first second _ _ hfirst hsecond =>
        simpa only [Pi.mul_apply] using congrArg₂ (· * ·) hfirst hsecond

#print axioms dynamical_observable_kernel

end D5.S3.Observer.WindowAlgebra.DynamicalObservableKernel
