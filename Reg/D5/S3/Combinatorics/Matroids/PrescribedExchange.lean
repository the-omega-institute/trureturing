import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.PrescribedExchange

/-! Source-bound observation of the first exchanged-base predicate. -/

namespace Reg.D5.S3.Combinatorics.Matroids.PrescribedExchange

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.PrescribedExchange
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := Matroid E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := Set E → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M.IsBase) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {E : Type u} [Finite E] (M : Matroid E) {A B X Y : Set E},
    M.IsBase A → M.IsBase B → X ⊆ A \ B → Y ⊆ B \ A →
    ∃ U V : Set E, U ⊆ A \ B ∧ V ⊆ B \ A ∧ X ⊆ U ∧ Y ⊆ V ∧
      U.ncard = V.ncard ∧ U.ncard ≤ (M.eRk (X ∪ Y)).toNat ∧
      r.readout () E M ((A \ U) ∪ V) ∧ M.IsBase ((B \ V) ∪ U)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨U, V, _, _, _, _, _, _, hf, _⟩ :=
    h (E := ULift.{u} Unit) (loopyOn ∅) (A := ∅) (B := ∅) (X := ∅) (Y := ∅)
      (by simp) (by simp) (by simp) (by simp)
  exact hf

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, loopyOn {ULift.up ()}, freeOn {ULift.up ()}, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  change (loopyOn {ULift.up ()}).IsBase {ULift.up ()} =
    (freeOn {ULift.up ()}).IsBase {ULift.up ()} at hh
  have hp : (freeOn ({ULift.up ()} : Set (ULift.{u} Unit))).IsBase {ULift.up ()} := by simp
  have hl := Eq.mpr hh hp
  simpa only [loopyOn_isBase_iff, singleton_ne_empty] using hl

def source_registration : Registration arena.{u}
    (type_of% (@exists_prescribed_exchange.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prescribed_exchange, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_prescribed_exchange.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.PrescribedExchange.exists_prescribed_exchange.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.PrescribedExchange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.PrescribedExchange
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Matroids.PrescribedExchange
