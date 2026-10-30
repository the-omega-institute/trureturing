import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.SuccessorPowerAssignments
import Reg.Support.DependentFamily

/-! Source-bound auditing retains the complete finite carrier and permutation family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Reg.D5.S3.FiniteGroups.SuccessorPowerAssignments

open _root_.D5.S3.FiniteGroups.SuccessorPowerAssignments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Carriers are parameters and permutations are states; dictionaries stay in the source law. -/
abbrev signature : Signature where
  Params := Type u
  State Q := Equiv.Perm Q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} := realize signature.{u}
  (fun _ _ β => Nat.card (SquareAssignments (K := ℂ) β))
  (fun e => nomatch e)

/-- The complete carrier, Fintype, DecidableEq and permutation telescope is retained. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Q : Type u} [hQ : Fintype Q] [hD : DecidableEq Q] (β : Equiv.Perm Q),
    R.readout () Q β = ∏ c : β.cycleFactorsFinset, (2 ^ c.val.support.card - 1)

/-- The actual law reconstructs the exact cycle-cardinality statement. -/
theorem actual_law : arena.{u}.Law actual := by
  intro Q hQ hD β
  exact square_assignments_cycle_card β

noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q := ULift.{u} (Fin 2)
  have he := h (Q := Q) (1 : Equiv.Perm Q)
  change (0 : ℕ) = ∏ c : (1 : Equiv.Perm Q).cycleFactorsFinset,
    (2 ^ c.val.support.card - 1) at he
  rw [← square_assignments_cycle_card (1 : Equiv.Perm Q)] at he
  letI : Finite (SquareAssignments (K := ℂ) (1 : Equiv.Perm Q)) :=
    square_assignments_finite _
  letI : Nonempty (SquareAssignments (K := ℂ) (1 : Equiv.Perm Q)) :=
    ⟨⟨fun _ => 1, by intro q; simp⟩⟩
  exact (Nat.ne_of_gt (Nat.card_pos (α := SquareAssignments (K := ℂ)
    (1 : Equiv.Perm Q)))) he.symm

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let Q := ULift.{u} (Fin 2)
  let a : Q := ⟨0⟩
  let b : Q := ⟨1⟩
  have hab : a ≠ b := by decide
  refine ⟨Q, 1, Equiv.swap a b, ?_⟩
  change Nat.card (SquareAssignments (K := ℂ) (1 : Equiv.Perm Q)) ≠
    Nat.card (SquareAssignments (K := ℂ) (Equiv.swap a b))
  rw [square_assignments_cycle_card, square_assignments_cycle_card]
  change (∏ c : (1 : Equiv.Perm Q).cycleFactorsFinset,
    (2 ^ c.val.support.card - 1)) ≠
      ∏ c : (Equiv.swap a b).cycleFactorsFinset, (2 ^ c.val.support.card - 1)
  have hprod (σ : Equiv.Perm Q) :
      (∏ c : σ.cycleFactorsFinset, (2 ^ c.val.support.card - 1 : ℕ)) =
        ∏ c ∈ σ.cycleFactorsFinset, (2 ^ c.support.card - 1 : ℕ) :=
    Finset.prod_coe_sort σ.cycleFactorsFinset
      (fun c : Equiv.Perm Q => (2 ^ c.support.card - 1 : ℕ))
  rw [hprod 1, hprod (Equiv.swap a b)]
  rw [Equiv.Perm.cycleFactorsFinset_one,
    (Equiv.Perm.isCycle_swap hab).cycleFactorsFinset_eq_singleton]
  norm_num [Equiv.Perm.card_support_swap hab]

noncomputable def sourceRegistration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.FiniteGroups.SuccessorPowerAssignments.square_assignments_cycle_card.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.SuccessorPowerAssignments.cycle_card_unit
  realizationName := `Reg.D5.S3.FiniteGroups.SuccessorPowerAssignments.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.SuccessorPowerAssignments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.SuccessorPowerAssignments
