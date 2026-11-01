/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform product splitting of every complete binary bipermutative lift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialCoboundary
import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialMinimal
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift
import D5.S1.Dynamics.Symbolic.PermutativeLifts.FiniteActionTrivialization

/-! The full factorial-base lift splits by a continuous finite-action coboundary. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

noncomputable def permutationTransfer {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) : FactorialPoint → Equiv.Perm Q :=
  transfer π (Nat.card (Equiv.Perm Q) + 1)

theorem continuous_permutationTransfer {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) :
    @Continuous FactorialPoint (Equiv.Perm Q) _ ⊥ (permutationTransfer π) := by
  letI : TopologicalSpace (Equiv.Perm Q) := ⊥
  exact continuous_transfer π _

theorem permutationTransfer_shift {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) (y : FactorialPoint) :
    permutationTransfer π (shiftFactorial 1 y) = π (y.1 0) * permutationTransfer π y := by
  apply transfer_shift
  exact fun a => word_holonomy_eq_one π (by omega) (by omega) a

/-- The original finite fibre is retained throughout the conjugacy. -/
noncomputable def trivializingHomeomorph {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q) :
    (FactorialPoint × Q) ≃ₜ (FactorialPoint × Q) where
  toFun z := (z.1, (permutationTransfer π z.1).symm z.2)
  invFun z := (z.1, permutationTransfer π z.1 z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun :=
    (finiteFibreHomeomorph (permutationTransfer π) (continuous_permutationTransfer π)).continuous
  continuous_invFun :=
    (finiteFibreHomeomorph (permutationTransfer π) (continuous_permutationTransfer π)).symm.continuous

theorem trivializing_conjugacy {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q)
    (y : FactorialPoint) (q : Q) :
    trivializingHomeomorph π (shiftFactorial 1 y, π (y.1 0) q) =
      (shiftFactorial 1 y, (trivializingHomeomorph π (y, q)).2) :=
  finiteFibreHomeomorph_conjugacy (permutationTransfer π) (continuous_permutationTransfer π)
    (shiftFactorial 1) (fun y => π (y.1 0)) (permutationTransfer_shift π) y q

namespace UniversalLift

open BipermutativeLift
open SymbolicDynamics.FullShift

def shiftLift {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool} (g : ℤ)
    (x : LiftPoint h factorialSubshift) : LiftPoint h factorialSubshift :=
  integerShift factorialSubshift g x

private theorem shiftLift_add {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (g j : ℤ) (x : LiftPoint h factorialSubshift) :
    shiftLift (g + j) x = shiftLift g (shiftLift j x) :=
  integerShift_add factorialSubshift g j x

instance liftShiftAction {k : ℕ} (h : (Fin (k + 2) → Bool) → Bool) :
    AddAction ℤ (LiftPoint h factorialSubshift) := integerShiftAction h factorialSubshift

/-- Every length at least two is represented by `k+2`; the fibre is exactly
the set of binary prefixes of length `k+1`. -/
noncomputable def splitting {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) :
    LiftPoint h factorialSubshift ≃ₜ (FactorialPoint × Prefix Bool k) :=
  (fullLiftHomeomorph bh factorialSubshift).trans
    (trivializingHomeomorph (prefixPerm bh))

theorem splitting_conjugacy {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (x : LiftPoint h factorialSubshift) :
    splitting bh (liftShift factorialSubshift x) =
      (shiftFactorial 1 (splitting bh x).1, (splitting bh x).2) := by
  change trivializingHomeomorph (prefixPerm bh)
      (fullLiftHomeomorph bh factorialSubshift (liftShift factorialSubshift x)) = _
  rw [full_lift_conjugacy]
  exact trivializing_conjugacy (prefixPerm bh)
    (fullLiftHomeomorph bh factorialSubshift x).1
    (fullLiftHomeomorph bh factorialSubshift x).2

private theorem splitting_fibre_invariant {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) (g : ℤ) (x : LiftPoint h factorialSubshift) :
    (splitting bh (shiftLift g x)).2 = (splitting bh x).2 := by
  have hstep (z : LiftPoint h factorialSubshift) :
      (splitting bh (shiftLift 1 z)).2 = (splitting bh z).2 := by
    have he := congrArg (fun p : FactorialPoint × Prefix Bool k => p.2)
      (splitting_conjugacy bh z)
    exact he
  exact invariant_of_unitStep (fun z => (splitting bh z).2) hstep g x

/-- For every allowed code length and every bipermutative binary code, its
entire inverse image over this same infinite minimal base is nonminimal. -/
theorem full_lift_not_minimal {k : ℕ} {h : (Fin (k + 2) → Bool) → Bool}
    (bh : Bipermutative h) : ¬ AddAction.IsMinimal ℤ (LiftPoint h factorialSubshift) := by
  intro hminimal
  letI := hminimal
  obtain ⟨y⟩ := (inferInstance : Nonempty FactorialPoint)
  let q₀ : Prefix Bool k := fun _ => false
  let q₁ : Prefix Bool k := fun _ => true
  let x₀ := (splitting bh).symm (y, q₀)
  let x₁ := (splitting bh).symm (y, q₁)
  let C : Set (LiftPoint h factorialSubshift) := {x | (splitting bh x).2 = q₀}
  have hC : IsClosed C := isClosed_singleton.preimage
    (continuous_snd.comp (splitting bh).continuous)
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

end UniversalLift
end D5.S1.Dynamics.Symbolic.PermutativeLifts
