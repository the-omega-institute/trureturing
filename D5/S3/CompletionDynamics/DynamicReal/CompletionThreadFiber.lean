/- GID: D5/S3/CompletionDynamics/DynamicReal/CompletionThreadFiber
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/DynamicReal/CompletionThreadFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant completed readout has a nontrivial thread fiber, while
     adjoining the blow-up origin restores injectivity and proves that no
     completed-value decoder can reconstruct every thread. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenThreadBlowup

/-!
This owner isolates the quotient phenomenon behind completion-thread
non-reconstruction.  It deliberately states a classical information-loss result;
no quantum no-cloning theorem is invoked.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.DynamicReal.CompletionThreadFiber

open scoped goldenRatio

/-- A minimal observer-thread carrier whose hidden coordinate is the first
blow-up coefficient. -/
structure GoldenThreadObserver where
  origin : ℝ
  deriving DecidableEq

/-- Zeroth-order completion forgets the origin and returns the common golden
fixed point. -/
def completionValue (_observer : GoldenThreadObserver) : ℝ :=
  Real.goldenRatio

/-- First blow-up readout retains the observer origin. -/
def blowupValue (observer : GoldenThreadObserver) : ℝ :=
  observer.origin

/-- The joint completion-plus-blow-up readout. -/
def completedJetReadout (observer : GoldenThreadObserver) : ℝ × ℝ :=
  (completionValue observer, blowupValue observer)

/-- Every pair of threads lies in the same zeroth-order completion fiber. -/
theorem completion_value_constant (o₁ o₂ : GoldenThreadObserver) :
    completionValue o₁ = completionValue o₂ := by
  rfl

/-- Zeroth-order completion is not injective. -/
theorem completion_value_not_injective :
    ¬ Function.Injective completionValue := by
  intro hInjective
  let o₀ : GoldenThreadObserver := ⟨0⟩
  let o₁ : GoldenThreadObserver := ⟨1⟩
  have hEq : completionValue o₀ = completionValue o₁ := rfl
  have hObservers : o₀ = o₁ := hInjective hEq
  have hOrigins : (0 : ℝ) = 1 := by
    exact congrArg GoldenThreadObserver.origin hObservers
  norm_num at hOrigins

/-- The first blow-up readout is injective on this normalized thread family. -/
theorem blowup_value_injective :
    Function.Injective blowupValue := by
  intro o₁ o₂ h
  cases o₁ with
  | mk c₁ =>
      cases o₂ with
      | mk c₂ =>
          simp [blowupValue] at h
          simp [h]

/-- Adjoining the first jet to the completion value restores injectivity. -/
theorem completed_jet_readout_injective :
    Function.Injective completedJetReadout := by
  intro o₁ o₂ h
  apply blowup_value_injective
  exact congrArg Prod.snd h

/-- No function of the completed value alone can recover every origin
coefficient. -/
theorem no_completion_value_decoder :
    ¬ ∃ decode : ℝ → ℝ,
      ∀ observer : GoldenThreadObserver,
        decode (completionValue observer) = observer.origin := by
  rintro ⟨decode, hDecode⟩
  have h₀ := hDecode (GoldenThreadObserver.mk 0)
  have h₁ := hDecode (GoldenThreadObserver.mk 1)
  simp [completionValue] at h₀ h₁
  linarith

/-- Any putative reconstruction of the full normalized observer from the
completed value would induce a forbidden origin decoder. -/
theorem no_completion_thread_reconstructor :
    ¬ ∃ reconstruct : ℝ → GoldenThreadObserver,
      ∀ observer : GoldenThreadObserver,
        reconstruct (completionValue observer) = observer := by
  rintro ⟨reconstruct, hReconstruct⟩
  apply no_completion_value_decoder
  refine ⟨fun value => (reconstruct value).origin, ?_⟩
  intro observer
  exact congrArg GoldenThreadObserver.origin (hReconstruct observer)

/-- The common completion fiber is infinite, witnessed by the embedding of all
real origin coefficients. -/
theorem completion_fiber_contains_all_origins (c : ℝ) :
    completionValue ⟨c⟩ = Real.goldenRatio := by
  rfl

/-- Reverse probe: the joint readout immediately recovers its first-jet
coordinate. -/
example (observer : GoldenThreadObserver) :
    (completedJetReadout observer).2 = observer.origin := by
  rfl

#print axioms completion_value_constant
#print axioms completion_value_not_injective
#print axioms blowup_value_injective
#print axioms completed_jet_readout_injective
#print axioms no_completion_value_decoder
#print axioms no_completion_thread_reconstructor
#print axioms completion_fiber_contains_all_origins

end D5.S3.CompletionDynamics.DynamicReal.CompletionThreadFiber
