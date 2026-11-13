import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.NumericalSemigroupRealizability
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Additive.NumericalSemigroupRealizability

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := AddSubmonoid ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ M S => AddSubmonoid.closure
    ({M} ∪ (fun s => M - s) '' (↑S : Set ℕ) ∪
      (fun s => M + s) '' (↑S : Set ℕ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : AddSubmonoid ℕ) (_ : (↑T : Set ℕ)ᶜ.Finite),
    ∃ (M : ℕ) (S : Finset ℕ), 0 < M ∧ S.Nonempty ∧
      (∀ s ∈ S, 0 < s) ∧ S.sup id = M ∧ S.gcd id = 1 ∧
      R.readout () M S = T

theorem actual_law : arena.Law actual :=
  _root_.D5.S3.Arith.Additive.NumericalSemigroupRealizability.result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, S, _, _, _, _, _, he⟩ := h ⊤ (by simp)
  have hm : (1 : ℕ) ∈ (⊥ : AddSubmonoid ℕ) := by
    rw [show (⊥ : AddSubmonoid ℕ) = ⊤ from he]
    trivial
  simpa using hm

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, ∅, {1}, ?_⟩
  change AddSubmonoid.closure
    ({0} ∪ (fun s : ℕ => 0 - s) '' (↑(∅ : Finset ℕ) : Set ℕ) ∪
      (fun s : ℕ => 0 + s) '' (↑(∅ : Finset ℕ) : Set ℕ)) ≠
    AddSubmonoid.closure
    ({0} ∪ (fun s : ℕ => 0 - s) '' (↑({1} : Finset ℕ) : Set ℕ) ∪
      (fun s : ℕ => 0 + s) '' (↑({1} : Finset ℕ) : Set ℕ))
  simp

def registration : Registration arena
    (type_of% _root_.D5.S3.Arith.Additive.NumericalSemigroupRealizability.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.NumericalSemigroupRealizability.result)
    (type_of% (realize signature (fun _ M S => AddSubmonoid.closure
      ({M} ∪ (fun s => M - s) '' (↑S : Set ℕ) ∪
        (fun s => M + s) '' (↑S : Set ℕ))) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Additive.NumericalSemigroupRealizability.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.NumericalSemigroupRealizability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ M S => AddSubmonoid.closure
    ({M} ∪ (fun s => M - s) '' (↑S : Set ℕ) ∪
      (fun s => M + s) '' (↑S : Set ℕ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.NumericalSemigroupRealizability
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.Additive.NumericalSemigroupRealizability
