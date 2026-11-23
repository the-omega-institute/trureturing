import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

universe u v

noncomputable section

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.AffineWickAssignments
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
  (transportCovariance transportMean)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments

namespace Transport

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} {J : Type v} [Fintype J]
    (U : Matrix X J ℂ) (A : Matrix J J ℂ) (μ : J → ℂ) (l : List X),
    r.readout () () (wick (transportCovariance U A) (transportMean U μ) l)
      (assign U l (wick A μ))

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} (Fin 2)) inferInstance (fun _ _ => 1)
    (fun _ _ => 1) (fun _ => 1) [⟨()⟩, ⟨()⟩]

def family : Registration arena.{u,v} (type_of% (@wick_transport.{u,v})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@wick_transport.{u,v}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_transport.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments.Transport.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments.Transport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transport

end Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickAssignments
