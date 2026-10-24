import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
import Reg.Support.DependentFamily

/-! Source-bound audit of the reversed-prefix characterization of right-special rotor factors. -/

namespace Reg.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial

open _root_.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the reversed prefix as its length varies, with the slope fixed. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ σ n => (List.ofFn (fun t : Fin (n - 1) => rotor σ (t + 1))).reverse)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

/-- Preserve every slope, length, word, hypothesis, and both directions of the claim. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ σ : ℝ, Irrational σ → 1 < σ → ∀ n : ℕ, 2 ≤ n →
    ∀ w : List ℕ, w.length = n - 1 →
      (IsRightSpecial (rotor σ) w ↔ w = r.readout () σ n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w := (List.ofFn (fun t : Fin (3 - 1) => rotor (Real.sqrt 2) (t + 1))).reverse
  have hw : w.length = 3 - 1 := by simp [w]
  have hs : IsRightSpecial (rotor (Real.sqrt 2)) w :=
    (result (Real.sqrt 2) irrational_sqrt_two Real.one_lt_sqrt_two 3 (by norm_num) w hw).mpr
      rfl
  have heq := (h (Real.sqrt 2) irrational_sqrt_two Real.one_lt_sqrt_two 3
    (by norm_num) w hw).mp hs
  have hlen := congrArg List.length heq
  norm_num [w, rejected, realize] at hlen

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 1, 3, ?_⟩
  intro heq
  have hlen := congrArg List.length heq
  norm_num [actual, realize] at hlen

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial.unit
  realizationName :=
    `Reg.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ σ n => (List.ofFn (fun t : Fin (n - 1) => rotor σ (t + 1))).reverse)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
    definition := some {
      owner := `D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
      name := `D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
