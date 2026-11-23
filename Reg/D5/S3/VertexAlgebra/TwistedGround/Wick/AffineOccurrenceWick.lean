import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

universe u v

noncomputable section

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient (jetOccupation)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource (affineMoment)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick

namespace Moment

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} {I : Type v} [Fintype I]
    (A : Matrix I I ℂ) (μ : I → ℂ) (hs : ∀ i j, A i j = A j i)
    (f : X → I) (l : List X),
    r.readout () () (affineMoment A μ (jetOccupation (l.map f)))
      (wick (A.submatrix f f) (μ ∘ f) l)

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) (ULift.{v} (Fin 0)) inferInstance
    0 0 (by intros; rfl) (fun i => nomatch i.down) []

def family : Registration arena.{u,v} (type_of% (@affineMoment_eq_wick.{u,v})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@affineMoment_eq_wick.{u,v}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affineMoment_eq_wick.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick.Moment.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick.Moment.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick
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

end Moment

namespace Pullback

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} {I : Type v} [Fintype I] [Fintype X]
    (A : Matrix I I ℂ) (μ : I → ℂ) (hs : ∀ i j, A i j = A j i)
    (f : X → I) (l : List X),
    r.readout () () (affineMoment (A.submatrix f f) (μ ∘ f) (jetOccupation l))
      (affineMoment A μ (jetOccupation (l.map f)))

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} (Fin 0)) (ULift.{v} (Fin 0)) inferInstance inferInstance
    0 0 (by intros; rfl) (fun i => nomatch i.down) []

def family : Registration arena.{u,v} (type_of% (@affineMoment_pullback.{u,v})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@affineMoment_pullback.{u,v}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affineMoment_pullback.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick.Pullback.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick.Pullback.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick
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
  options := #[]

end Pullback

end Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick
