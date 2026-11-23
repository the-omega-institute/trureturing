import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

universe u v

noncomputable section

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.AffineWickBlocks
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks

namespace Congruence

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} (A B : Matrix X X ℂ) (μ : X → ℂ) (l : List X)
    (h : ∀ a ∈ l, ∀ b ∈ l, A a b = B a b),
    r.readout () () (wick A μ l) (wick B μ l)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Unit) 0 0 (fun _ => 1) [⟨()⟩] (by intros; rfl)

def family : Registration arena.{u} (type_of% (@wick_congr_on.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@wick_congr_on.{u}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_congr_on.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.Congruence.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.Congruence.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Congruence

namespace TwoBlocks

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Finite X] (A : Matrix X X ℂ) (p : X → Bool)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i j, p i ≠ p j → A i j = 0)
    (l : List X),
    r.readout () () (wick A 0 l) (wick A 0 (l.filter p) * wick A 0 (l.filter fun a => !p a))

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Bool) inferInstance 0 (fun a => a.down)
    (by intros; rfl) (by intros; rfl) [⟨true⟩, ⟨false⟩]

def family : Registration arena.{u} (type_of% (@wick_block.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@wick_block.{u}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_block.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.TwoBlocks.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.TwoBlocks.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
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

end TwoBlocks

namespace FiniteBlocks

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Finite X] {S : Type v} [DecidableEq S]
    (A : Matrix X X ℂ) (slot : X → S)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i j, slot i ≠ slot j → A i j = 0)
    (blocks : Finset S) (l : List X) (hl : ∀ a ∈ l, slot a ∈ blocks),
    r.readout () () (wick A 0 l)
      (∏ i ∈ blocks, wick A 0 (l.filter fun a => decide (slot a = i)))

private theorem rejectedLaw : ¬ arena.{u,v}.Law complexFalse := by
  intro h
  exact @h (ULift.{u} Bool) inferInstance (ULift.{v} Bool) inferInstance 0
    (fun a => ⟨a.down⟩) (by intros; rfl) (by intros; rfl) Finset.univ
    [⟨true⟩, ⟨false⟩] (fun a _ => Finset.mem_univ _)

def family : Registration arena.{u,v} (type_of% (@wick_blocks.{u,v})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@wick_blocks.{u,v}, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_blocks.{u,v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.FiniteBlocks.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks.FiniteBlocks.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteBlocks

end Reg.D5.S3.VertexAlgebra.TwistedGround.Wick.AffineWickBlocks
