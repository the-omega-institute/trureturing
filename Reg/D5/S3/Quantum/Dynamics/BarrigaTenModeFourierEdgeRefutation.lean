import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the exponential formula for idempotent matrices. -/

namespace Reg.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
open _root_.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator
local instance (priority := 2000) {n : Type} [Fintype n] [DecidableEq n] :
    NormedAddCommGroup (Matrix n n ℂ) := Matrix.instL2OpNormedAddCommGroup
local instance (priority := 2000) {n : Type} [Fintype n] [DecidableEq n] :
    NormedSpace ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedSpace
local instance (priority := 2000) {n : Type} [Fintype n] [DecidableEq n] :
    NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
local instance (priority := 2000) {n : Type} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra

/-- Observe the scalar exponential in the idempotent formula. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => NormedSpace.exp t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n ℂ),
    Q * Q = Q → ∀ t : ℂ,
      NormedSpace.exp (t • Q) = 1 + (R.readout () () t - 1) • Q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (1 : Matrix (Fin 1) (Fin 1) ℂ) (by simp) 0
  have hentry := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hbad
  norm_num [rejected, realize] at hentry

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Complex.log 2, ?_⟩
  change NormedSpace.exp (0 : ℂ) ≠ NormedSpace.exp (Complex.log 2)
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_zero, Complex.exp_log (by norm_num)]
  norm_num

def source_registration : Registration arena
    (∀ {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n ℂ),
      Q * Q = Q → ∀ t : ℂ,
        NormedSpace.exp (t • Q) = 1 + (NormedSpace.exp t - 1) • Q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨expIdempotent, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

#print _root_.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ t => NormedSpace.exp t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
