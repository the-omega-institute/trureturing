import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition

open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module Matrix

universe u v w z

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega
private def zeroPencil : Pencil ℂ where
  domain := ℂ
  codomain := ℂ
  first := 0
  second := 0

namespace horizontalRank_dual
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Pencil ℂ, R.readout () () p.dual.horizontalRank p.verticalRank
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_dual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_dual, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_dual) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.horizontalRank_dual.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.horizontalRank_dual.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end horizontalRank_dual

namespace verticalRank_dual
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Pencil ℂ, R.readout () () p.dual.verticalRank p.horizontalRank
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_dual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_dual, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_dual) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.verticalRank_dual.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.verticalRank_dual.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end verticalRank_dual

namespace horizontalRank_matrix
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (p : Pencil ℂ) (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain), R.readout () () p.horizontalRank (hRank (LinearMap.toMatrix bu bv p.first) (LinearMap.toMatrix bu bv p.second))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} (Fin (Module.finrank ℂ ℂ))) (ULift.{v} (Fin (Module.finrank ℂ ℂ))) inferInstance inferInstance inferInstance inferInstance zeroPencil ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm) ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm)
def source_registration : Registration arena.{u,v} (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_matrix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_matrix, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.horizontalRank_matrix) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.horizontalRank_matrix.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.horizontalRank_matrix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end horizontalRank_matrix

namespace verticalRank_matrix
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (p : Pencil ℂ) (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain), R.readout () () p.verticalRank (vRank (LinearMap.toMatrix bu bv p.first) (LinearMap.toMatrix bu bv p.second))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} (Fin (Module.finrank ℂ ℂ))) (ULift.{v} (Fin (Module.finrank ℂ ℂ))) inferInstance inferInstance inferInstance inferInstance zeroPencil ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm) ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm)
def source_registration : Registration arena.{u,v} (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_matrix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_matrix, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.verticalRank_matrix) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.verticalRank_matrix.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.verticalRank_matrix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end verticalRank_matrix

namespace tensorRank_matrix
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v} {c : Type w} {d : Type z} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] (p q : Pencil ℂ) (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain) (bu' : Basis c ℂ q.domain) (bv' : Basis d ℂ q.codomain), R.readout () () (p.tensorRank q) (tensorSum (LinearMap.toMatrix bu bv p.first) (LinearMap.toMatrix bu bv p.second) (LinearMap.toMatrix bu' bv' q.first) (LinearMap.toMatrix bu' bv' q.second)).rank
private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  exact @h (ULift.{u} (Fin (Module.finrank ℂ ℂ))) (ULift.{v} (Fin (Module.finrank ℂ ℂ))) (ULift.{w} (Fin (Module.finrank ℂ ℂ))) (ULift.{z} (Fin (Module.finrank ℂ ℂ))) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance zeroPencil zeroPencil ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm) ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm) ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm) ((Module.finBasis ℂ ℂ).reindex Equiv.ulift.symm)
def source_registration : Registration arena.{u,v,w,z} (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_matrix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_matrix, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_matrix) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_matrix.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_matrix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end tensorRank_matrix

namespace tensorRank_dual_dual_left
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : Pencil ℂ, R.readout () () (p.dual.dual.tensorRank q) (p.tensorRank q)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual_left, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual_left) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_dual_left.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_dual_left.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end tensorRank_dual_dual_left

namespace tensorRank_comm
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : Pencil ℂ, R.readout () () (p.tensorRank q) (q.tensorRank p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_comm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_comm, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_comm) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_comm.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_comm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end tensorRank_comm

namespace tensorRank_dual_dual
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : Pencil ℂ, R.readout () () (p.dual.tensorRank q.dual) (p.tensorRank q)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_dual) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_dual.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_dual.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end tensorRank_dual_dual

namespace tensorRank_dual_left_exchange
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q : Pencil ℂ, R.readout () () (p.dual.tensorRank q) (p.tensorRank q.dual)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h zeroPencil zeroPencil
def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_left_exchange) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_left_exchange, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.Pencil.tensorRank_dual_left_exchange) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_left_exchange.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition.tensorRank_dual_left_exchange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end tensorRank_dual_left_exchange


end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
