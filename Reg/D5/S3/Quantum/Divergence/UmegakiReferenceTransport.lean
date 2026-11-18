import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiReferenceTransport
import Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport
open scoped Kronecker
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open _root_.Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction (identityChannel)
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport

universe u

private abbrev Q := ULift.{u} Unit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def eqActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem eqDependence : ObservationalDependence signature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  exact one_ne_zero (hh.mp rfl)

private abbrev embeddingArena : Arena where
  signature := signature
  Law F := ∀ {a R : Type u} [Fintype a] [DecidableEq a] [Fintype R] [DecidableEq R]
      (X : Matrix R R ℂ) (V : Matrix (R × a) (R × a) ℂ),
    F.readout () () (((X ⊗ₖ (1 : Matrix a a ℂ))ᴴ * V).trace) ((Xᴴ * partialTraceRight V).trace)

private theorem embeddingEquivalence :
    (type_of% @trace_embed_pair.{u}) ↔ embeddingArena.{u}.Law eqActual :=
  Iff.rfl

private theorem embeddingRejected : ¬ embeddingArena.{u}.Law rejected := by
  intro h
  exact h (a := Q) (R := Q) 0 0

def embeddingFamily : Registration embeddingArena.{u}
    (type_of% @trace_embed_pair.{u}) where
  actual := eqActual
  bridge := embeddingEquivalence
  variation := ⟨@trace_embed_pair, rejected, embeddingRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    embeddingArena.{u}.Law eqActual rejected embeddingRejected
  dependence := eqDependence

def embeddingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_embed_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.trace_embed_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.embeddingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨embeddingArena.{u}⟩
  objectArena := .source ⟨embeddingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source embeddingArena.{u} ⟨embeddingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms embeddingAudit

private abbrev traceAdjointArena : Arena where
  signature := signature
  Law F := ∀ {a b R : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype R] [DecidableEq R] [Nonempty a] [Nonempty b]
      (N : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ)
      (Z : Matrix (R × a) (R × a) ℂ),
    F.readout () () ((PhiR N Y * Z).trace) ((Y * amp N Z).trace)

private theorem traceAdjointEquivalence :
    (type_of% @PhiR_trace_pair.{u}) ↔ traceAdjointArena.{u}.Law eqActual :=
  Iff.rfl

private theorem traceAdjointRejected : ¬ traceAdjointArena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 0 0

def traceAdjointFamily : Registration traceAdjointArena.{u}
    (type_of% @PhiR_trace_pair.{u}) where
  actual := eqActual
  bridge := traceAdjointEquivalence
  variation := ⟨@PhiR_trace_pair, rejected, traceAdjointRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    traceAdjointArena.{u}.Law eqActual rejected traceAdjointRejected
  dependence := eqDependence

def traceAdjointAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PhiR_trace_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.PhiR_trace_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.traceAdjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceAdjointArena.{u}⟩
  objectArena := .source ⟨traceAdjointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceAdjointArena.{u} ⟨traceAdjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms traceAdjointAudit

private abbrev hilbertSchmidtAdjointArena : Arena where
  signature := signature
  Law F := ∀ {a b R : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype R] [DecidableEq R] [Nonempty a] [Nonempty b]
      (N : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ)
      (Z : Matrix (R × a) (R × a) ℂ),
    F.readout () () (((PhiR N Y)ᴴ * Z).trace) ((Yᴴ * amp N Z).trace)

private theorem hilbertSchmidtAdjointEquivalence :
    (type_of% @PhiR_hs_pair.{u}) ↔ hilbertSchmidtAdjointArena.{u}.Law eqActual :=
  Iff.rfl

private theorem hilbertSchmidtAdjointRejected : ¬ hilbertSchmidtAdjointArena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 0 0

def hilbertSchmidtAdjointFamily : Registration hilbertSchmidtAdjointArena.{u}
    (type_of% @PhiR_hs_pair.{u}) where
  actual := eqActual
  bridge := hilbertSchmidtAdjointEquivalence
  variation := ⟨@PhiR_hs_pair, rejected, hilbertSchmidtAdjointRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hilbertSchmidtAdjointArena.{u}.Law eqActual rejected hilbertSchmidtAdjointRejected
  dependence := eqDependence

def hilbertSchmidtAdjointAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PhiR_hs_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.PhiR_hs_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.hilbertSchmidtAdjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hilbertSchmidtAdjointArena.{u}⟩
  objectArena := .source ⟨hilbertSchmidtAdjointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hilbertSchmidtAdjointArena.{u} ⟨hilbertSchmidtAdjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms hilbertSchmidtAdjointAudit

end Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport
