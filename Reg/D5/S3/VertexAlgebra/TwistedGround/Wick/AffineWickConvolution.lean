import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

universe u

noncomputable section

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution

namespace CovarianceSum

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Finite X]
    (A C : Matrix X X ℂ) (μ : X → ℂ) (hA : ∀ i j, A i j = A j i)
    (hC : ∀ i j, C i j = C j i) (l : List X),
    r.readout () () (wick (A + C) μ l)
      (((partitions l).map fun p => wick C 0 p.1 * wick A μ p.2).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) inferInstance 0 0 0 (by intros; rfl) (by intros; rfl) []

def family : Registration arena.{u} (type_of% (@wick_add_covariance.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@wick_add_covariance.{u}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_add_covariance.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution.CovarianceSum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution.CovarianceSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution
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

end CovarianceSum

end Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickConvolution
