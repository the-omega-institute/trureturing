import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteRelativeConeCollapse

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open _root_.D5.S3.Geometry.FiniteRelativeConeCollapse

namespace Reg.D5.S3.Geometry.FiniteRelativeConeCollapse
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
  target : PreAbstractSimplicialComplex V
attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := PreAbstractSimplicialComplex p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p K => Nonempty (Sequence K p.target)) Empty.elim
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) Empty.elim

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    {K L : PreAbstractSimplicialComplex V} {v : V},
    L ≤ K → ({v} : Finset V) ∈ L →
    (∀ s ∈ K, insert v s ∈ K) → (∀ s ∈ L, insert v s ∈ L) →
    R.readout () ⟨V, fv, dv, L⟩ K

private theorem bridge : (type_of% (@exists_sequence.{u})) ↔ arena.{u}.Law actual :=
  Iff.rfl

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let v : V := ⟨()⟩
  exact @h V inferInstance inferInstance ⊤ ⊤ v le_rfl
    (Finset.singleton_nonempty v) (fun s _ => Finset.insert_nonempty v s)
    (fun s _ => Finset.insert_nonempty v s)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let V := ULift.{u} Unit
  let p : Parameters.{u} := ⟨V, inferInstance, inferInstance, ⊤⟩
  refine ⟨p, ⊥, ⊤, ?_⟩
  intro heq
  change Nonempty (Sequence (⊥ : PreAbstractSimplicialComplex V) ⊤) =
    Nonempty (Sequence (⊤ : PreAbstractSimplicialComplex V) ⊤) at heq
  obtain ⟨S⟩ := Eq.mpr heq ⟨Sequence.refl ⊤⟩
  exact S.monotone (Finset.singleton_nonempty (ULift.up ()))

def family : Registration arena.{u} (type_of% (@exists_sequence.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@exists_sequence.{u}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, negative⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_sequence.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeConeCollapse.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeConeCollapse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p K => Nonempty (Sequence K p.target)) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeConeCollapse
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteRelativeConeCollapse
