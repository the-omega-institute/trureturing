import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.CollisionPrefix

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Walks.CollisionPrefix

namespace Prefix

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun n => Walk (Fin n) (n * n - 1)) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ _ w => Function.Surjective w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_ : 2 ≤ n) (w : Walk (Fin n) (n * n - 1)),
    Function.Injective (edge w) →
      R.readout () n w ∧ ∃ a b : Fin n,
        Finset.univ.image (edge w) = Finset.univ.erase (a, b) ∧
        ((b = w 0 ∧ w (Fin.last (n * n - 1)) = a) ∨
          (a = b ∧ a ≠ w 0 ∧ w (Fin.last (n * n - 1)) = w 0))

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  let w : Walk (Fin 2) 3 := ![0, 0, 1, 1]
  have hi : Function.Injective (edge w) := by decide
  exact (h (n := 2) (by decide) w hi).1

noncomputable def family : Registration arena (type_of% (@prefix_structure)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefix_structure, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨2, ![0, 0, 1, 1], (fun _ => 0), ?_⟩
    change Function.Surjective (![0, 0, 1, 1] : Walk (Fin 2) 3) ≠
      Function.Surjective (fun _ : Fin 4 => (0 : Fin 2))
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_structure) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.Graph.Walks.CollisionPrefix.prefix_structure.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CollisionPrefix.Prefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => Function.Surjective w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Prefix

namespace ActualCollision

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ n : ℕ, Fin n) (fun p => Walk (Fin p.1) ((p.1 * p.1 - 1) + 1)) (fun _ => Prop)

noncomputable def actual : Realization signature := realize signature
  (fun _ _ w => Function.Surjective (initialWalk w)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_ : 2 ≤ n) (v : Fin n)
    (w : Walk (Fin n) ((n * n - 1) + 1)), Collision v w →
      R.readout () ⟨n, v⟩ w ∧ ∃ a b : Fin n,
        Finset.univ.image (edge (initialWalk w)) = Finset.univ.erase (a, b) ∧
        ((b = v ∧ initialWalk w (Fin.last (n * n - 1)) = a) ∨
          (a = b ∧ a ≠ v ∧ initialWalk w (Fin.last (n * n - 1)) = v))

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  let w : Walk (Fin 2) 4 := ![0, 0, 1, 1, 1]
  have hi : Collision 0 w := by unfold Collision; decide
  exact (h (n := 2) (by decide) 0 w hi).1

noncomputable def family : Registration arena (type_of% (@collision_prefix_structure)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_prefix_structure, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := by
    intro role
    refine ⟨⟨2, 0⟩, ![0, 0, 1, 1, 1], (fun _ => 0), ?_⟩
    change Function.Surjective (initialWalk (![0, 0, 1, 1, 1] : Walk (Fin 2) 4)) ≠
      Function.Surjective (initialWalk (fun _ : Fin 5 => (0 : Fin 2)))
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@collision_prefix_structure) (Realization signature) Type Unit := {
  unitName := `D5.S3.Combinatorics.Graph.Walks.CollisionPrefix.collision_prefix_structure.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CollisionPrefix.ActualCollision.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => Function.Surjective (initialWalk w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end ActualCollision



end Reg.D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
