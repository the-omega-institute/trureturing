import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
import Reg.Support.FactorialFockMetric

set_option autoImplicit false
noncomputable section
open scoped Matrix
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality OriginalCurrentMetric SignedOscillatorWick
open D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric

abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {D : LatticeData}
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ) (p q : Oscillator D),
    r.readout () () (FactorialBilinear.form (Index D) (substitution A p) q)
      (FactorialBilinear.form (Index D) p (substitution (fun k => (A k)ᵀ) q))

theorem sourceBridge :
    (type_of% (@substitution_factorial_transpose)) ↔ arena.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.Law complexEqual := @substitution_factorial_transpose

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  let D : LatticeData := ⟨0, 0, by intros; rfl, by intro i; exact Fin.elim0 i⟩
  exact @h D (fun _ => 0) 0 0

def family : Registration arena (type_of% (@substitution_factorial_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@substitution_factorial_transpose) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
