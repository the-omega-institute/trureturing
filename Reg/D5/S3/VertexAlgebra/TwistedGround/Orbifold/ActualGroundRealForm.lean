import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The readout tests existence of the normalized real form on the full lattice telescope.
The zero bilinear form supplies a contrasting observation on the actual Leech ground. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm

attribute [local instance] Classical.propDecidable

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.ActualLeechHyperbolic
open _root_.D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm

abbrev Parameters := {D : LatticeData // IsUnit D.G.det}
abbrev Form (p : Parameters) := LinearMap.BilinForm ℂ (ActualGround p.1 p.2)
abbrev signature := Reg.Support.SingleDependentReadout.signature Parameters Form (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ p B => decide (Nonempty (GroundRealForm p.1 p.2 B))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p : Parameters, R.readout () p (selectedGroundForm p.1 p.2) = true

theorem sourceBridge : (type_of% (@actual_ground_real_form)) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact decide_eq_true (h p)
  · intro h p
    exact of_decide_eq_true (h p)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true (h ⟨leechData, leech_spec.2.1⟩)

private theorem zero_rejected : ¬ Nonempty (GroundRealForm leechData leech_spec.2.1 0) := by
  rintro ⟨form⟩
  let x : ActualGround leechData leech_spec.2.1 := fun _ => 1
  have hx : x ≠ 0 := fun h => one_ne_zero (congrFun h (0 : Half _))
  have h := (form.positive x hx).2
  simp at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨leechData, leech_spec.2.1⟩, selectedGroundForm leechData leech_spec.2.1, 0, ?_⟩
  change decide (Nonempty (GroundRealForm leechData leech_spec.2.1
    (selectedGroundForm leechData leech_spec.2.1))) ≠
    decide (Nonempty (GroundRealForm leechData leech_spec.2.1 0))
  rw [decide_eq_true (actual_ground_real_form ⟨leechData, leech_spec.2.1⟩),
    decide_eq_false zero_rejected]
  decide

def family : Registration arena (type_of% (@actual_ground_real_form)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actual_ground_real_form, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_ground_real_form)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm.actual_ground_real_form
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm
