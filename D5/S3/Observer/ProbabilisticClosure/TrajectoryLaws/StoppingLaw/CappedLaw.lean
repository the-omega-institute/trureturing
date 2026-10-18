/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/CappedLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/CappedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete stopping-law equality is equivalent to equality on the faithful capped observation type. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteTreeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- Nonreturn observations retain their actual paid depth and have return indicator false. -/
def CappedObservation (k : ℕ) :=
  {z : Observation // z.paid ≤ k ∧ z.returned = z.output.isSome}

/-- Equality on all observations adds no hypothesis beyond the original capped complete law. -/
theorem hasStoppingLaw_iff_capped (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
    (T : ReadTree) (hh : T.height ≤ k) :
    HasStoppingLaw β V j k T ↔
      ∀ z : CappedObservation k, fullMass β V j T z.val = stoppingMass β k z.val := by
  constructor
  · intro h z; exact h z.val
  · intro h z
    by_cases hz : z.paid ≤ k ∧ z.returned = z.output.isSome
    · exact h ⟨z, hz⟩
    have he (φ : Bool) : {S : Spins | observation j φ T S = z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro S hS
      apply hz
      have hc := T.paid_cap hh (visible φ S)
      have hr : (observation j φ T S).returned = (observation j φ T S).output.isSome := rfl
      have hp : (observation j φ T S).paid ≤ k := hc
      change observation j φ T S = z at hS
      rw [hS] at hr hp
      exact ⟨hp, hr⟩
    have hactual : fullMass β V j T z = 0 := by simp [fullMass, he]
    have hsupport (w : Observation) (hw : stoppingMass β k w ≠ 0) :
        w.paid ≤ k ∧ w.returned = w.output.isSome := by
      rcases w with ⟨h, o, d, n⟩
      cases d with
      | false => simp [stoppingMass] at hw
      | true =>
        cases h with
        | a s =>
          cases o with
          | none => simp [stoppingMass] at hw
          | some out =>
            cases out with
            | b t => simp [stoppingMass] at hw
            | a t =>
              cases t with
              | true => simp [stoppingMass] at hw
              | false =>
                have hn : n = k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨by simpa using hn.le, rfl⟩
        | b s =>
          cases o with
          | none => simp [stoppingMass] at hw
          | some out =>
            cases out with
            | b t => simp [stoppingMass] at hw
            | a t =>
              cases t with
              | false =>
                have hn : n = k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨by simpa using hn.le, rfl⟩
              | true =>
                have hn : 1 ≤ n ∧ n ≤ k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨hn.2, rfl⟩
    have htable : stoppingMass β k z = 0 := by
      by_contra hne
      exact hz (hsupport z hne)
    rw [hactual, htable]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
