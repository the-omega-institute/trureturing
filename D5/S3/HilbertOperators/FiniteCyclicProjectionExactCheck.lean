import D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
open Filter
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open D5.S3.HilbertOperators.FiniteCyclicProjectionStrong
variable {k : Type u} [RCLike k]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace k H] [CompleteSpace H]
example (Us : List (ClosedSubmodule k H)) (x : H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ‖(cycle Us ^ n) x - (sInf {U | U ∈ Us}).toSubmodule.starProjection x‖ < ε := by
  simpa only [dist_eq_norm] using Metric.tendsto_atTop.mp (tendsto_cycle_pow Us x)
example : cycle ([] : List (ClosedSubmodule k H)) = 1 := rfl
example : sInf {U : ClosedSubmodule k H | U ∈ ([] : List (ClosedSubmodule k H))} = ⊤ := by simp
example (U : ClosedSubmodule k H) (x : H) : cycle [U] x = U.toSubmodule.starProjection x := by
  simp [cycle]
example (U V : ClosedSubmodule k H) (x : H) :
    cycle [U,V] x = V.toSubmodule.starProjection (U.toSubmodule.starProjection x) := by
  simp [cycle]
example (U : ClosedSubmodule k H) (x : H) : cycle [U,U] x = U.toSubmodule.starProjection x := by
  simp [cycle]
example (x : H) : cycle ([⊤,⊥] : List (ClosedSubmodule k H)) x = 0 := by
  simp [cycle]
#print axioms D5.S3.HilbertOperators.FiniteCyclicProjectionStrong.tendsto_cycle_pow
#print axioms D5.S3.HilbertOperators.AlternatingProjectionStrong.tendsto_pow_of_regular
