/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full balanced-base inverse images split with their actual binary prefix fibres. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedCoboundary
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedMinimal
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift

/-! Full binary bipermutative lifts of the balanced base split with the actual prefix fibre. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLift

open BipermutativeLift Balanced

abbrev shiftLift {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool} (g : ℤ)
    (x : LiftPoint h balancedSubshift) : LiftPoint h balancedSubshift :=
  integerShift balancedSubshift g x

/-- The entire inverse image, over the same fixed base for every k and code,
with the original finite source-prefix fibre. -/
noncomputable def splitting {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) :
    LiftPoint h balancedSubshift ≃ₜ (BalancedPoint × Prefix Bool k) :=
  (fullLiftHomeomorph bh balancedSubshift).trans
    (Balanced.trivializingHomeomorph (prefixPerm bh))

theorem splitting_conjugacy {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (x : LiftPoint h balancedSubshift) :
    splitting bh (liftShift balancedSubshift x) =
      (shiftBalanced 1 (splitting bh x).1, (splitting bh x).2) := by
  change Balanced.trivializingHomeomorph (prefixPerm bh)
      (fullLiftHomeomorph bh balancedSubshift (liftShift balancedSubshift x)) = _
  rw [full_lift_conjugacy]
  exact Balanced.trivializing_conjugacy (prefixPerm bh)
    (fullLiftHomeomorph bh balancedSubshift x).1
    (fullLiftHomeomorph bh balancedSubshift x).2

/-- Every integer iterate preserves the actual fibre coordinate. -/
theorem splitting_fibre_invariant {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (g : ℤ) (x : LiftPoint h balancedSubshift) :
    (splitting bh (shiftLift g x)).2 = (splitting bh x).2 := by
  apply invariant_of_unitStep (fun z => (splitting bh z).2) _ g x
  intro z
  have he := congrArg (fun p : BalancedPoint × Prefix Bool k => p.2)
    (splitting_conjugacy bh z)
  exact he

/-- These nonempty invariant fibres are clopen in the entire lift. -/
theorem splitting_fibre_clopen {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (q : Prefix Bool k) :
    IsClopen {x : LiftPoint h balancedSubshift | (splitting bh x).2 = q} := by
  exact (isClopen_discrete ({q} : Set (Prefix Bool k))).preimage
    (continuous_snd.comp (splitting bh).continuous)

/-- Every allowed binary bipermutative code has a nonminimal entire inverse image. -/
theorem full_lift_not_minimal {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) : ¬ AddAction.IsMinimal ℤ (LiftPoint h balancedSubshift) := by
  intro hminimal
  letI := hminimal
  obtain ⟨y⟩ := (inferInstance : Nonempty BalancedPoint)
  let q₀ : Prefix Bool k := fun _ => false
  let q₁ : Prefix Bool k := fun _ => true
  let x₀ := (splitting bh).symm (y, q₀)
  let x₁ := (splitting bh).symm (y, q₁)
  let C : Set (LiftPoint h balancedSubshift) := {x | (splitting bh x).2 = q₀}
  have hC : IsClosed C := (splitting_fibre_clopen bh q₀).isClosed
  have hsub : AddAction.orbit ℤ x₀ ⊆ C := by
    rintro z ⟨g, rfl⟩
    change (splitting bh (shiftLift g x₀)).2 = q₀
    rw [splitting_fibre_invariant]
    exact congrArg Prod.snd ((splitting bh).apply_symm_apply (y, q₀))
  have hdense := AddAction.dense_orbit ℤ x₀
  have hx₁ : x₁ ∈ C := by
    apply hC.closure_subset_iff.mpr hsub
    rw [hdense.closure_eq]
    trivial
  have he : q₁ = q₀ := by
    change (splitting bh x₁).2 = q₀ at hx₁
    simpa [x₁] using hx₁
  have he₀ := congrFun he (0 : Fin (k + 1))
  simp [q₀, q₁] at he₀

end D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedLift
