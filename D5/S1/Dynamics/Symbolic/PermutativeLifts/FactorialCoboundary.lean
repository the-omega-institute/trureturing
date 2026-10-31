/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FactorialCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous finite-action coboundaries from the actual recognizable factorial tilings. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialSubshift
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

private theorem holonomy_take_succ {G : Type*} [Monoid G] (π : Bool → G)
    (w : List Bool) {p : ℕ} (hp : p < w.length) :
    wordHolonomy π (w.take (p + 1)) = π w[p] * wordHolonomy π (w.take p) := by
  rw [List.take_succ_eq_append_getElem hp, wordHolonomy_append]
  simp

private def stateTransfer {G : Type*} [Monoid G] (π : Bool → G)
    (W : Bool → List Bool) (s : TileState W) : G :=
  wordHolonomy π ((W s.1).take s.2.val)

private theorem stateTransfer_next {G : Type*} [Monoid G] (π : Bool → G)
    (W : Bool → List Bool) (hW : ∀ a, wordHolonomy π (W a) = 1)
    {s t : TileState W} (hst : TileNext W s t) :
    stateTransfer π W t = π (readTile W s) * stateTransfer π W s := by
  rcases hst with ⟨htype, hoff⟩ | ⟨hlast, hstart⟩
  · unfold stateTransfer
    rw [← htype, hoff, holonomy_take_succ π (W s.1) s.2.isLt]
    rfl
  · have hstep := holonomy_take_succ π (W s.1) s.2.isLt
    rw [hlast, List.take_length, hW] at hstep
    simpa [stateTransfer, hstart, readTile] using hstep

/-- The transfer reads a finite prefix of the unique block containing zero. -/
noncomputable def transfer {G : Type*} [Monoid G] (π : Bool → G) (n : ℕ)
    (y : FactorialPoint) : G := stateTransfer π (word n) ((decode n y).1 0)

theorem continuous_transfer {G : Type*} [Monoid G] [TopologicalSpace G]
    (π : Bool → G) (n : ℕ) : Continuous (transfer π n) := by
  exact (continuous_of_discreteTopology : Continuous (stateTransfer π (word n))).comp
    ((continuous_apply 0).comp (continuous_subtype_val.comp (continuous_decode n)))

theorem transfer_shift {G : Type*} [Monoid G] (π : Bool → G) (n : ℕ)
    (hW : ∀ a, wordHolonomy π (word n a) = 1) (y : FactorialPoint) :
    transfer π n (shiftFactorial 1 y) = π (y.1 0) * transfer π n y := by
  unfold transfer
  rw [decode_shift]
  have hnext := stateTransfer_next π (word n) hW ((decode n y).2 0)
  have hread : readTile (word n) ((decode n y).1 0) = y.1 0 :=
    congrFun (read_decode n y) 0
  simpa [shiftTiling_apply, hread] using hnext

/-- One fixed base trivializes every finite permutation-valued letter cocycle.
Only the level and its transfer depend on the chosen finite action. -/
theorem exists_continuous_permutation_transfer {Q : Type*} [Finite Q]
    [TopologicalSpace (Equiv.Perm Q)]
    (π : Bool → Equiv.Perm Q) :
    ∃ β : FactorialPoint → Equiv.Perm Q,
      Continuous β ∧ ∀ y, β (shiftFactorial 1 y) = π (y.1 0) * β y := by
  let n := Nat.card (Equiv.Perm Q) + 1
  refine ⟨transfer π n, continuous_transfer π n, ?_⟩
  intro y
  apply transfer_shift
  exact fun a => word_holonomy_eq_one π (by dsimp [n]; omega) (by dsimp [n]; omega) a

end D5.S1.Dynamics.Symbolic.PermutativeLifts
