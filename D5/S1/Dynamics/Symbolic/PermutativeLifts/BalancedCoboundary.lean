/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedCoboundary
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous finite-action coboundaries from recognizable equal-height balanced tilings. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedSubshift
import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialCoboundary
import D5.S1.Dynamics.Symbolic.PermutativeLifts.FiniteActionTrivialization

/-! The recognizable balanced towers give continuous transfers for every finite permutation action. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

/-- Prefix holonomy in the actual unique balanced block containing zero. -/
noncomputable def transfer {G : Type*} [Monoid G] (π : Bool → G) (n : ℕ)
    (y : BalancedPoint) : G := stateTransfer π (balancedWord n) ((decode n y).1 0)

theorem continuous_transfer {G : Type*} [Monoid G] [TopologicalSpace G]
    (π : Bool → G) (n : ℕ) : Continuous (transfer π n) := by
  exact (continuous_of_discreteTopology : Continuous (stateTransfer π (balancedWord n))).comp
    ((continuous_apply 0).comp (continuous_subtype_val.comp (continuous_decode n)))

theorem transfer_shift {G : Type*} [Monoid G] (π : Bool → G) (n : ℕ)
    (hW : ∀ a, wordHolonomy π (balancedWord n a) = 1) (y : BalancedPoint) :
    transfer π n (shiftBalanced 1 y) = π (y.1 0) * transfer π n y := by
  unfold transfer
  rw [decode_shift]
  have hnext := stateTransfer_next π (balancedWord n) hW ((decode n y).2 0)
  have hread : readTile (balancedWord n) ((decode n y).1 0) = y.1 0 :=
    congrFun (read_decode n y) 0
  simpa [shiftTiling_apply, hread] using hnext

/-- A single base supports the transfer for every finite permutation action. -/
noncomputable def permutationTransfer {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) : BalancedPoint → Equiv.Perm Q :=
  transfer π (Nat.card (Equiv.Perm Q) + 1)

theorem continuous_permutationTransfer {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) :
    @Continuous BalancedPoint (Equiv.Perm Q) _ ⊥ (permutationTransfer π) := by
  letI : TopologicalSpace (Equiv.Perm Q) := ⊥
  exact continuous_transfer π _

theorem permutationTransfer_shift {Q : Type*} [Finite Q]
    (π : Bool → Equiv.Perm Q) (y : BalancedPoint) :
    permutationTransfer π (shiftBalanced 1 y) = π (y.1 0) * permutationTransfer π y := by
  apply transfer_shift
  exact fun a => balancedWord_holonomy_eq_one π (Nat.card (Equiv.Perm Q)) (by omega) a

noncomputable def trivializingHomeomorph {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q) :
    (BalancedPoint × Q) ≃ₜ (BalancedPoint × Q) :=
  finiteFibreHomeomorph (permutationTransfer π) (continuous_permutationTransfer π)

theorem trivializing_conjugacy {Q : Type*} [Finite Q]
    [TopologicalSpace Q] [DiscreteTopology Q] (π : Bool → Equiv.Perm Q)
    (y : BalancedPoint) (q : Q) :
    trivializingHomeomorph π (shiftBalanced 1 y, π (y.1 0) q) =
      (shiftBalanced 1 y, (trivializingHomeomorph π (y, q)).2) :=
  finiteFibreHomeomorph_conjugacy (permutationTransfer π) (continuous_permutationTransfer π)
    (shiftBalanced 1) (fun y => π (y.1 0)) (permutationTransfer_shift π) y q

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
