import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeInvolution

/-! Source-bound audits for positive-rank nonidentity and exact order two. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeInvolution
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeInvolution

noncomputable section

private def probe : LatticeData where
  rank := 1
  G := 0
  symmetric := by intros; rfl
  even_diagonal := by intro i; exact ⟨0, rfl⟩

namespace Nontrivial
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  LatticeData (fun D => Carrier D ≃ₗ[ℂ] Carrier D) (fun _ => Bool)
def actual : Realization signature := by
  classical
  exact realize signature
    (fun _ D e => decide (e ≠ LinearEquiv.refl ℂ (Carrier D))) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData), 0 < D.rank → readout.readout () D (theta D) = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h probe (by decide)
  change false = true at bad
  contradiction
private theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  refine ⟨probe, theta probe, LinearEquiv.refl ℂ (Carrier probe), ?_⟩
  change decide (theta probe ≠ LinearEquiv.refl ℂ (Carrier probe)) ≠
    decide (LinearEquiv.refl ℂ (Carrier probe) ≠ LinearEquiv.refl ℂ (Carrier probe))
  simp [theta_nontrivial_of_rank_pos probe (by decide)]

def familyRegistration : Registration arena
    (type_of% (@theta_nontrivial_of_rank_pos)) where
  actual := actual
  bridge := by
    classical
    simp [arena, actual, realize]
  variation := ⟨by
    classical
    simpa [arena, actual, realize] using theta_nontrivial_of_rank_pos,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@theta_nontrivial_of_rank_pos)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeInvolution.theta_nontrivial_of_rank_pos.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeInvolution.Nontrivial.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeInvolution
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end Nontrivial

namespace ExactOrder
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  LatticeData (fun D => Carrier D ≃ₗ[ℂ] Carrier D) (fun _ => ℕ)
def actual : Realization signature := realize signature
  (fun _ _ e => orderOf e) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData), 0 < D.rank → readout.readout () D (theta D) = 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h probe (by decide)
  change (0 : ℕ) = 2 at bad
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨probe, (1 : Carrier probe ≃ₗ[ℂ] Carrier probe), theta probe, ?_⟩
  change orderOf (1 : Carrier probe ≃ₗ[ℂ] Carrier probe) ≠ orderOf (theta probe)
  rw [orderOf_one, theta_orderOf_eq_two_of_rank_pos probe (by decide)]
  decide

def familyRegistration : Registration arena
    (type_of% (@theta_orderOf_eq_two_of_rank_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_orderOf_eq_two_of_rank_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@theta_orderOf_eq_two_of_rank_pos)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName :=
    `D5.S3.VertexAlgebra.LatticeInvolution.theta_orderOf_eq_two_of_rank_pos.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeInvolution.ExactOrder.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeInvolution
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]
end ExactOrder

end

end Reg.D5.S3.VertexAlgebra.LatticeInvolution
