import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
import Reg.Support.DependentFamily

/-! Source-bound audit of the dimension condition in the perfectness classification. -/

namespace Reg.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra

open _root_.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the dimension condition appearing in the source claim. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A constructive decision of the source dimension condition. -/
def dimensionDecision (d : ℕ) : Decidable (2 ≤ d) :=
  match d with
  | 0 => .isFalse (by omega)
  | 1 => .isFalse (by omega)
  | _ + 2 => .isTrue (by omega)

def actual : Realization signature :=
  realize signature (fun _ _ d => @decide (2 ≤ d) (dimensionDecision d))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- Keep the complete source claim while varying its dimension condition. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (K : Type) [Field K] [CharZero K] (d k : ℕ),
    r.readout () () d = true → 1 ≤ k →
      ((∃ p : MvPolynomial (Fin d) K,
        p ≠ 0 ∧ p.IsHomogeneous (k + 1) ∧ perfect (k := k) p) ↔ k = 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hp, hh, _⟩ := (h ℚ 0 1 rfl (by norm_num)).mpr rfl
  apply hp
  ext a
  have ha : a = 0 := by
    ext i
    exact Fin.elim0 i
  simpa using hh.coeff_eq_zero (d := a) (by rw [ha]; simp)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp only [claim, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro K _ _ d k hd hk
    exact result K d k
      (@of_decide_eq_true (2 ≤ d) (dimensionDecision d) hd) hk,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.source_registration
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
    (realize signature (fun _ _ d => @decide (2 ≤ d) (dimensionDecision d))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
    definition := some {
      owner := `D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
      name := `D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
