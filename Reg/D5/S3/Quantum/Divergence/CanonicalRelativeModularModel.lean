import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Sum the weighted squared norms over the observed finite set of indices. -/
abbrev signature : Signature where
  Params := Σ n : Type u, Σ _d : n → ℝ, n → ℂ
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => ∑ i ∈ s, p.2.1 i * ‖p.2.2 i‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p s => (∑ i ∈ s, p.2.1 i * ‖p.2.2 i‖ ^ 2) + 1)
    (fun e => nomatch e)

/-- The full diagonal identity evaluates the finite sum on all indices. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (d : n → ℝ) (y : n → ℂ),
    (star y ⬝ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ y)).re =
      R.readout () ⟨n, d, y⟩ Finset.univ

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro bad
  have h := bad (n := ULift.{u} Unit) (fun _ => 0) (fun _ => 0)
  norm_num [rejected, realize, dotProduct, Matrix.mulVec] at h

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, (fun _ => 1), (fun _ => 1)⟩, ∅, Finset.univ, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena.{u} (type_of% @diagonal_quadratic_form.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨diagonal_quadratic_form, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI.diagonal_quadratic_form.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.CanonicalRelativeModularModel.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.CanonicalRelativeModularModel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p s => ∑ i ∈ s, p.2.1 i * ‖p.2.2 i‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
