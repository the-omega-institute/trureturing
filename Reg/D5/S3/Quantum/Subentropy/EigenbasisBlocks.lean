import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.EigenbasisBlocks
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.OrthogonalRecordEntropy
open _root_.D5.S3.Quantum.Subentropy.Basic
open scoped Kronecker
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open _root_.D5.S3.Quantum.Subentropy.EigenbasisBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Subentropy.EigenbasisBlocks
universe u v
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {B : Type v} [Fintype X] [DecidableEq X]
    [Fintype B] [DecidableEq B] (M : Matrix (X × B) (X × B) ℂ) (hM : M.PosSemidef),
    let hR := (partialTraceRight_posSemidef hM).isHermitian
    let U : Matrix X X ℂ := hR.eigenvectorUnitary
    let K := localConjugate U M
    let Y := fun x : X => K.submatrix (fun b => (x,b)) (fun b => (x,b))
    K.PosSemidef ∧ R.readout () () K.trace M.trace ∧
      (∀ x, (Y x).PosSemidef) ∧
      (∑ x, Y x) = partialTraceLeft M ∧
      (∀ x, (Y x).trace = (hR.eigenvalues x : ℂ)) ∧
      blockPinch K = (fun i j => if i.1 = j.1 then Y i.1 i.2 j.2 else 0)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance 1 Matrix.PosSemidef.one
  exact he.2.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u,v} (type_of% @eigenbasis_blocks.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eigenbasis_blocks, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eigenbasis_blocks.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.EigenbasisBlocks.eigenbasis_blocks.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.EigenbasisBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.EigenbasisBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Subentropy.EigenbasisBlocks
