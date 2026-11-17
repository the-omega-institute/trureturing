import Reg.D5.S3.Geometry.FiniteElementaryCollapse
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse

noncomputable section
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse

namespace Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
universe u_1
open Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion

namespace Monotone
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    {K L : PreAbstractSimplicialComplex V} (S : Sequence K L),
    R.readout () V L K
private theorem bridge : (type_of% (@Sequence.monotone.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  exact @h (ULift.{u_1} Unit) inferInstance inferInstance ⊥ ⊥ (.refl ⊥)
def family : Registration arena.{u_1} (type_of% (@Sequence.monotone.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@Sequence.monotone.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Sequence.monotone.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.Monotone.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.Monotone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K L => K ≤ L) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeSimplicialCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Monotone

namespace Deletion
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (v : V),
    R.readout () V (deletion K v) K
private theorem bridge : (type_of% (@deletion_le.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  exact @h (ULift.{u_1} Unit) inferInstance inferInstance ⊥ ⟨()⟩
def family : Registration arena.{u_1} (type_of% (@deletion_le.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@deletion_le.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deletion_le.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.Deletion.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.Deletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K L => K ≤ L) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeSimplicialCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Deletion

namespace LinkDeletion
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (v : V),
    R.readout () V (link K v) (deletion K v)
private theorem bridge : (type_of% (@link_le_deletion.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  exact @h (ULift.{u_1} Unit) inferInstance inferInstance ⊥ ⟨()⟩
def family : Registration arena.{u_1} (type_of% (@link_le_deletion.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@link_le_deletion.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@link_le_deletion.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.LinkDeletion.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.LinkDeletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K L => K ≤ L) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeSimplicialCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LinkDeletion

namespace BaseCone
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    (v : V) (L : PreAbstractSimplicialComplex V),
    R.readout () V L (cone v L)
private theorem bridge : (type_of% (@base_le_cone.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  exact @h (ULift.{u_1} Unit) inferInstance inferInstance ⟨()⟩ ⊥
def family : Registration arena.{u_1} (type_of% (@base_le_cone.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@base_le_cone.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@base_le_cone.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.BaseCone.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.BaseCone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K L => K ≤ L) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeSimplicialCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end BaseCone

namespace ConeMono
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {V : Type u_1} [fv : Fintype V] [dv : DecidableEq V]
    (v : V) {L M : PreAbstractSimplicialComplex V} (h : L ≤ M),
    R.readout () V (cone v L) (cone v M)
private theorem bridge : (type_of% (@cone_mono.{u_1})) ↔ arena.{u_1}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro h
  exact @h (ULift.{u_1} Unit) inferInstance inferInstance ⟨()⟩ ⊥ ⊥ le_rfl
def family : Registration arena.{u_1} (type_of% (@cone_mono.{u_1})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@cone_mono.{u_1}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family.dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cone_mono.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.ConeMono.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse.ConeMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K L => K ≤ L) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteRelativeSimplicialCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ConeMono
end Reg.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
