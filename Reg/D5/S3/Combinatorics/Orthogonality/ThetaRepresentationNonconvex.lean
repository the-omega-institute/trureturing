import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex
import Reg.Support.DependentFamily

/-! Source-bound audit of the real dot-product Cauchy inequality. -/

namespace Reg.D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex

open _root_.D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace DotCauchy

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x y => ¬ x ≤ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {V : Type} [Fintype V] (v w : V → ℝ),
    r.readout () () ((v ⬝ᵥ w) ^ 2) ((v ⬝ᵥ v) * (w ⬝ᵥ w))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (0 : Fin 1 → ℝ) (0 : Fin 1 → ℝ) (dot_cauchy 0 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) (le_refl 0)
  norm_num at hbad

def source_registration : Registration arena (type_of% @dot_cauchy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dot_cauchy, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dot_cauchy) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex.DotCauchy.unit
  realizationName :=
    .str `Reg.D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex.DotCauchy
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex
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
  options := #[] }

#print axioms source_registration
#print axioms registration

end DotCauchy

end
end Reg.D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex
