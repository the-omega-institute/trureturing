import D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability
import Reg.Support.DependentFamily
import Mathlib.Data.Fintype.EquivFin

namespace Reg.D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability

open _root_.D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

/-- The original key type, dependent values, protected keys and initial state. -/
abbrev Parameters := Σ (ι : Type u), Σ (α : ι → Type v), Σ (_ : Set ι), (∀ i, α i)

def signature : Signature where
  Params := Parameters.{u, v}
  State p := ∀ i : p.1, p.2.1 i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Set p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p y => {i | p.2.2.2 i ≠ y i})
    (fun e => nomatch e)

/-- Removing the finite-difference information is an intervention on this role. -/
def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => (∅ : Set p.1)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {ι : Type u} {α : ι → Type v} (fixedKeys : Set ι) (x y : ∀ i, α i),
    Relation.ReflTransGen (CoordinateStep fixedKeys) x y ↔
      (∀ i ∈ fixedKeys, x i = y i) ∧ (r.readout () ⟨ι, α, fixedKeys, x⟩ y).Finite

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let a : ULift.{u} ℕ → ULift.{v} Bool := fun _ => ⟨false⟩
  let b : ULift.{u} ℕ → ULift.{v} Bool := fun _ => ⟨true⟩
  have path := (h (ι := ULift.{u} ℕ) (α := fun _ => ULift.{v} Bool) ∅ a b).mpr
    ⟨by simp, Set.finite_empty⟩
  have finite := (coordinate_reachable_iff_finite_difference ∅ a b).mp path |>.2
  exact Set.infinite_univ (by simpa [a, b] using finite)

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun {ι} {α} fixedKeys x y =>
    @coordinate_reachable_iff_finite_difference ι α fixedKeys x y,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro role
    let a : ULift.{u} ℕ → ULift.{v} Bool := fun _ => ⟨false⟩
    let b : ULift.{u} ℕ → ULift.{v} Bool := fun _ => ⟨true⟩
    refine ⟨⟨ULift.{u} ℕ, (fun _ => ULift.{v} Bool), ∅, a⟩, a, b, ?_⟩
    change {i | a i ≠ a i} ≠ {i | a i ≠ b i}
    intro same
    have atZero := congrArg (fun s : Set (ULift.{u} ℕ) => ULift.up 0 ∈ s) same
    simp [a, b] at atZero

register_information_theorem coordinate_reachable_iff_finite_difference in arena
  readout via (realize signature.{u, v}
    (fun _ p y => {i | p.2.2.2 i ≠ y i}) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability
