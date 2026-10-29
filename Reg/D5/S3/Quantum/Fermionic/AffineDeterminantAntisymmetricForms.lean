import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the total degree of the affine determinant. -/

namespace Reg.D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms

open _root_.D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The polynomial dimension determines the domain of the total-degree coordinate. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun d => MvPolynomial (Fin (d + 1) × Fin d) ℂ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ f => f.totalDegree) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain all four clauses, observing the degree in the second clause. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ d r, d + 2 ≤ r → ∀ f : MvPolynomial (Fin r × Fin d) ℂ,
      IsAlternating f → f.totalDegree ≤ d → f = 0) ∧
    (∀ d, IsAlternating (affineDet d) ∧ R.readout () d (affineDet d) ≤ d) ∧
    (∀ d (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ),
      IsAlternating f → f.totalDegree ≤ d → ∃ c : ℂ, f = c • affineDet d) ∧
    (∀ d, 2 ≤ d →
      IsNondegenerate d (fun y => eval (fun p => y p.1 p.2) (affineDet d)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h.2.1 0).2
  exact Nat.not_succ_le_zero 0 hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, X (0, 0), ?_⟩
  change (0 : MvPolynomial (Fin 2 × Fin 1) ℂ).totalDegree ≠ (X (0, 0)).totalDegree
  simp only [totalDegree_zero, totalDegree_X, ne_eq, Nat.zero_ne_one, not_false_eq_true]

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f.totalDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
