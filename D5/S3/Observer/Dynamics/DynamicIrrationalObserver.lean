/- GID: D5/S3/Observer/Dynamics/DynamicIrrationalObserver
   generality: I
   mirror-B: D5/B/S3/Observer/Dynamics/DynamicIrrationalObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Contractive real observers have an infinite jet and a concrete golden witness. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/- Library-search audit trail (2026-09-01):
   * Repository searches for dynamic irrational observers, higher/full jets,
     jet readouts, thread expansions, and observer structures found no existing
     definition with a variable contraction and an infinite jet indexed from
     two. `CompletionThreadFiber.GoldenThreadObserver` has only one hidden real
     coordinate and a finite `(q0, q1)` readout, so it is not an exact hit.
   * The existing `goldenProjectiveMultiplier` is exactly the source's
     `-phi^(-2)`, and `abs_golden_projective_multiplier_lt_one` supplies its
     strict contraction proof. These are reused rather than reproved.
   * Pinned Mathlib supplies `HasSum` and `hasSum_zero` for the infinite-series
     interpretation and the concrete realization. Searches of all pinned Lean
     packages found no packaged observer definition or readout theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Dynamics.DynamicIrrationalObserver

open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative

/-- The data of a dynamic irrational observer. The higher jet is a genuinely
infinite family whose direct indices start at two. The name follows the source;
the stated source constraints require contractivity but do not separately
assume irrationality of the completion value. -/
structure Observer where
  completion : ℝ
  ratio : ℝ
  linearCoefficient : ℝ
  higherJet : (k : ℕ) → 2 ≤ k → ℝ
  ratio_abs_lt_one : |ratio| < 1

/-- The `k`th higher-jet contribution to the thread at time `n`. -/
def higherTerm (observer : Observer) (n : ℕ)
    (k : {m : ℕ // 2 ≤ m}) : ℝ :=
  observer.higherJet k.1 k.2 * observer.ratio ^ (k.1 * n)

/-- A thread realizes an observer when its tail is the convergent sum of all
higher-jet terms. This predicate makes convergence explicit instead of
silently assigning a value to a non-summable formal series. -/
def HasThread (observer : Observer) (thread : ℕ → ℝ) : Prop :=
  ∀ n, HasSum (higherTerm observer n)
    (thread n - observer.completion -
      observer.linearCoefficient * observer.ratio ^ n)

/-- The readout sequence consists of the completion value, the linear
coefficient, and then the higher jet indexed directly from two. -/
def readout (observer : Observer) (k : ℕ) : ℝ :=
  if hk0 : k = 0 then observer.completion
  else if hk1 : k = 1 then observer.linearCoefficient
  else observer.higherJet k (by omega)

@[simp]
theorem readout_zero (observer : Observer) :
    readout observer 0 = observer.completion := by
  simp [readout]

@[simp]
theorem readout_one (observer : Observer) :
    readout observer 1 = observer.linearCoefficient := by
  simp [readout]

@[simp]
theorem readout_of_two_le (observer : Observer) (k : ℕ)
    (hk : 2 ≤ k) :
    readout observer k = observer.higherJet k hk := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp [readout, hk0, hk1]

/-- The source's golden first observation class fixes the completion and the
contractive ratio, while leaving all jet coefficients free. -/
def IsGoldenFirstObservationClass (observer : Observer) : Prop :=
  observer.completion = Real.goldenRatio ∧
    observer.ratio = goldenProjectiveMultiplier

/-- A concrete golden observer with linear coefficient one and zero higher
jet. Its associated thread is `phi + lambda^n`. -/
def goldenLinearObserver : Observer where
  completion := Real.goldenRatio
  ratio := goldenProjectiveMultiplier
  linearCoefficient := 1
  higherJet := fun _ _ ↦ 0
  ratio_abs_lt_one := abs_golden_projective_multiplier_lt_one

theorem golden_linear_observer_hasThread :
    HasThread goldenLinearObserver
      (fun n ↦ Real.goldenRatio + goldenProjectiveMultiplier ^ n) := by
  intro n
  have hTerm : higherTerm goldenLinearObserver n =
      fun _ : {m : ℕ // 2 ≤ m} ↦ (0 : ℝ) := by
    funext k
    simp [higherTerm, goldenLinearObserver]
  rw [hTerm]
  have hValue :
      (Real.goldenRatio + goldenProjectiveMultiplier ^ n) -
          goldenLinearObserver.completion -
        goldenLinearObserver.linearCoefficient * goldenLinearObserver.ratio ^ n = 0 := by
    simp [goldenLinearObserver]
  rw [hValue]
  exact hasSum_zero

/-- The definition is nonempty and analytically realizable: the golden first
class has a concrete thread and the prescribed readouts at every order. -/
theorem exists_golden_dynamic_irrational_observer :
    ∃ observer : Observer,
      IsGoldenFirstObservationClass observer ∧
        HasThread observer
          (fun n ↦ Real.goldenRatio + goldenProjectiveMultiplier ^ n) ∧
        readout observer 0 = Real.goldenRatio ∧
        readout observer 1 = 1 ∧
        ∀ k : ℕ, (hk : 2 ≤ k) → readout observer k = 0 := by
  refine ⟨goldenLinearObserver, ⟨rfl, rfl⟩,
    golden_linear_observer_hasThread, rfl, rfl, ?_⟩
  intro k hk
  simp [goldenLinearObserver, hk]

#print axioms readout_of_two_le
#print axioms golden_linear_observer_hasThread
#print axioms exists_golden_dynamic_irrational_observer

end D5.S3.Observer.Dynamics.DynamicIrrationalObserver
