import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of functional calculus on affine combinations of a projection. -/

namespace Reg.D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
open _root_.D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate the scalar function at the first spectral value. -/
abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f a => f a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (_hQ : Q.IsHermitian) (_hQQ : Q * Q = Q)
    (f : ℝ → ℝ) (a b : ℝ),
    cfc f (a • (1 : Matrix n n ℂ) + b • Q) =
      r.readout () f a • (1 : Matrix n n ℂ) + (f (a + b) - f a) • Q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := Fin 1) 0 Matrix.isHermitian_zero (by simp) (fun _ => 1) 0 0
  rw [projection_cfc 0 Matrix.isHermitian_zero (by simp)] at he
  have hc := congrArg (fun X : Matrix (Fin 1) (Fin 1) ℂ => X 0 0) he
  norm_num [rejected, realize] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨id, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @projection_cfc) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨projection_cfc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@projection_cfc) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f a => f a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
