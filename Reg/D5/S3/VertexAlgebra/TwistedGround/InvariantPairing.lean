import D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source reconstruction and finite variation for the selected ground pairing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := {D : LatticeData // IsUnit D.G.det}

abbrev GroundRepresentations (p : Parameters) :=
  Representation ℂ (Extension p.1 ⧸ K p.1) (ActualGround p.1 p.2)

abbrev signature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature
    Parameters GroundRepresentations GroundRepresentations

def actual : Realization signature :=
  realize signature (fun _ _ rho => rho) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ p _ =>
    Representation.trivial ℂ (Extension p.1 ⧸ K p.1) (ActualGround p.1 p.2))
    (fun empty => nomatch empty)

def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    ∃ B : LinearMap.BilinForm ℂ (ActualGround D hu), B.Nondegenerate ∧
      (∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
        B (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) g u)
          (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) g v) = B u v) ∧
      (∀ (a : Charge D) (u v : ActualGround D hu),
        B (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) (groundLift D a) u) v =
          paritySign (bilinear D a a / 2) *
            B u (observation.readout () ⟨D, hu⟩ (groundRepresentation D hu) (groundLift D a) v))

theorem exact_source_bridge :
    (type_of% (@actual_ground_pairing)) ↔ arena.Law actual := by
  constructor
  · intro source D hu
    obtain ⟨pairing⟩ := source D hu
    exact ⟨pairing.form, pairing.nondegenerate, pairing.invariant, pairing.signed_adjoint⟩
  · intro law D hu
    obtain ⟨B, nondegenerate, invariant, adjoint⟩ := law D hu
    exact ⟨⟨B, nondegenerate, invariant, adjoint⟩⟩

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have determinant : hyperbolic.G.det = -1 := by
    change Matrix.det (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = -1
    norm_num [Matrix.det_fin_two]
  rw [determinant]
  exact isUnit_neg_one

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨B, nondegenerate, _, adjoint⟩ := law hyperbolic hyperbolic_unit
  have sign : paritySign (bilinear hyperbolic (1 : Charge hyperbolic) 1 / 2) = -1 := by
    have norm : bilinear hyperbolic (1 : Charge hyperbolic) 1 = 2 := by
      change (∑ i : Fin 2, ∑ j : Fin 2,
        (1 : ℤ) * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) i j * 1) = 2
      norm_num [Fin.sum_univ_two]
    rw [norm]
    norm_num [paritySign]
  have zero : B = 0 := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change B u v = 0
    have equality := adjoint 1 u v
    change B u v = paritySign (bilinear hyperbolic 1 1 / 2) * B u v at equality
    rw [sign, neg_one_mul] at equality
    linear_combination (1 / 2 : ℂ) * equality
  exact nondegenerate.ne_zero zero

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨hyperbolic, hyperbolic_unit⟩, groundRepresentation hyperbolic hyperbolic_unit,
    Representation.trivial ℂ (Extension hyperbolic ⧸ K hyperbolic)
      (ActualGround hyperbolic hyperbolic_unit), ?_⟩
  change groundRepresentation hyperbolic hyperbolic_unit ≠
    Representation.trivial ℂ (Extension hyperbolic ⧸ K hyperbolic)
      (ActualGround hyperbolic hyperbolic_unit)
  intro equality
  have central := (Classical.choose_spec
    (Classical.choose_spec
      (actual_twisted_ground_representation hyperbolic hyperbolic_unit))).2.2.1
  change groundRepresentation hyperbolic hyperbolic_unit
    (QuotientGroup.mk (⟨1, 0⟩ : Extension hyperbolic)) = -1 at central
  rw [equality] at central
  have contradiction := congrArg
    (fun A : Module.End ℂ (ActualGround hyperbolic hyperbolic_unit) => A (fun _ => 1) 0) central
  norm_num [Representation.trivial] at contradiction

def familyRegistration : Registration arena (type_of% (@actual_ground_pairing)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp actual_ground_pairing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_ground_pairing)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.actual_ground_pairing "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing.familyRegistration
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms exact_source_bridge
#print axioms familyRegistration

end


namespace ExposedHelpers

noncomputable section

theorem central_character_source :
    (type_of% (@central_character)) ↔
      (∀ (D : LatticeData) (hu : IsUnit D.G.det) (s : F₂),
        (groundRepresentation D hu).character
          ((quotientEquiv D).symm (⟨s, 0⟩ : ReducedExtension D)) =
            complexSign s * (Module.finrank ℂ (ActualGround D hu) : ℂ)) := by rfl

theorem average_trace_source :
    (type_of% (@average_trace)) ↔
      (∀ (D : LatticeData) (hu : IsUnit D.G.det),
        LinearMap.trace ℂ (LinearMap.BilinForm ℂ (ActualGround D hu))
          (formAverage D hu) = 1) := by rfl

theorem averaged_invariant_source :
    (type_of% (@averaged_invariant)) ↔
      (∀ (D : LatticeData) (hu : IsUnit D.G.det)
        (B : LinearMap.BilinForm ℂ (ActualGround D hu))
        (g : Extension D ⧸ K D) (u v : ActualGround D hu),
        formAverage D hu B (groundRepresentation D hu g u) (groundRepresentation D hu g v) =
          formAverage D hu B u v) := by rfl

theorem invariant_nondegenerate_source :
    (type_of% (@invariant_nondegenerate)) ↔
      (∀ (D : LatticeData) (hu : IsUnit D.G.det)
        (B : LinearMap.BilinForm ℂ (ActualGround D hu)), B ≠ 0 →
        (∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
          B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v) →
        B.Nondegenerate) := by rfl

theorem ground_signed_adjoint_source :
    (type_of% (@ground_signed_adjoint)) ↔
      (∀ (D : LatticeData) (hu : IsUnit D.G.det)
        (B : LinearMap.BilinForm ℂ (ActualGround D hu)),
        (∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
          B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v) →
        ∀ (a : Charge D) (u v : ActualGround D hu),
          B (groundAction D hu a u) v = paritySign (bilinear D a a / 2) *
            B u (groundAction D hu a v)) := by rfl

end
end ExposedHelpers

end Reg.D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
