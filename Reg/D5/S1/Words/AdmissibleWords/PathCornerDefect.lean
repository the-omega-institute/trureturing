import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.PathCornerDefect
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.AdmissibleWords.PathCornerDefect

open Finset
open _root_.D5.S1.Words.AdmissibleWords.PathCornerDefect
open _root_.D5.S1.Words.AdmissibleWords.PathStableSetPolytope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the dimension term read from the length parameter `m`. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The tight count with the dimension term `m + 2` varied; the interior count stays. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (w : Fin (m + 2) → Bool),
    (∀ e : Fin (m + 1), ¬ (w e.castSucc = true ∧ w e.succ = true)) →
    (univ.filter fun i => occupancy w i = 0).card +
        (univ.filter fun e : Fin (m + 1) =>
          occupancy w e.castSucc + occupancy w e.succ = 1).card =
      R.readout () () m + (univ.filter fun d : Fin m => w d.castSucc.succ = true).card

def actual : Realization signature :=
  realize signature (fun _ _ x => x + 2) (fun e => nomatch e)

/-- The constant readout `0` replaces the dimension term. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The empty word of length two has two tight lower bounds, not zero tight inequalities. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 (fun _ => false) (by decide)
  change (univ.filter fun i => occupancy (fun _ : Fin 2 => false) i = 0).card +
      (univ.filter fun e : Fin 1 =>
        occupancy (fun _ : Fin 2 => false) e.castSucc +
          occupancy (fun _ : Fin 2 => false) e.succ = 1).card =
    (0 : ℕ) + (univ.filter fun d : Fin 0 =>
      (fun _ : Fin 2 => false) d.castSucc.succ = true).card at hbad
  simp [occupancy] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℕ) + 2 ≠ 1 + 2
  omega

def registration : Registration arena
    (∀ (m : ℕ) (w : Fin (m + 2) → Bool),
      (∀ e : Fin (m + 1), ¬ (w e.castSucc = true ∧ w e.succ = true)) →
      (univ.filter fun i => occupancy w i = 0).card +
          (univ.filter fun e : Fin (m + 1) =>
            occupancy w e.castSucc + occupancy w e.succ = 1).card =
        (m + 2) + (univ.filter fun d : Fin m => w d.castSucc.succ = true).card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tight_count_eq_add_interior, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the dimension term `m + 2` through its raw source path. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tight_count_eq_add_interior)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x + 2)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.PathCornerDefect.tight_count_eq_add_interior.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.PathCornerDefect.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x + 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.PathCornerDefect
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.PathCornerDefect
