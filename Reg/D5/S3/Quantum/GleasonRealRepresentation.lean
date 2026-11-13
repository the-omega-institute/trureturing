import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.GleasonRealRepresentation
import Reg.Support.DependentFamily

/-! Source-bound audit of the real sphere representation through its quadratic readout. -/

namespace Reg.D5.S3.Quantum.GleasonRealRepresentation
open _root_.Gleason
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Matrix (Fin 3) (Fin 3) ℝ
  State _ := EuclideanSpace ℝ (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A x => ⇑x ⬝ᵥ (A *ᵥ ⇑x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ) {W : ℝ},
    IsFrameFunction ℝ f W → (∀ x, ‖x‖ = 1 → 0 ≤ f x) →
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
      ∀ x, ‖x‖ = 1 → f x = R.readout () A x

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, _, hA⟩ := h (fun _ => 0) (W := 0)
    (by intro b; simp) (by intro x hx; exact le_rfl)
  have hbad := hA (EuclideanSpace.single 0 (1 : ℝ)) (by simp)
  change (0 : ℝ) = 1 at hbad
  exact zero_ne_one hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, EuclideanSpace.single 0 (1 : ℝ), ?_⟩
  norm_num [actual, realize, dotProduct, Matrix.one_apply]

def source_registration : Registration arena (type_of% @frameFunction_regular_sphere) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨frameFunction_regular_sphere, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@frameFunction_regular_sphere) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.GleasonRealRepresentation.unit
  realizationName := `Reg.D5.S3.Quantum.GleasonRealRepresentation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A x => ⇑x ⬝ᵥ (A *ᵥ ⇑x))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.GleasonRealRepresentation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.GleasonRealRepresentation
