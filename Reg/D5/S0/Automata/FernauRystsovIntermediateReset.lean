import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S0.Automata.FernauRystsovIntermediateReset

/-! Word length is the shared observation in all three reset thresholds. -/

namespace Reg.D5.S0.Automata.FernauRystsovIntermediateReset

open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit
open _root_.D5.S0.Automata.FernauRystsovIntermediateReset (Threshold)

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => List Bool) (fun _ => ℕ)

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ => List.length) (fun e => nomatch e)

private def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def law (R : DependentFamily.Realization signature) : Prop :=
  ∀ (r s m : ℕ), max r s ≤ m → m ≤ r + s →
    let length : List Bool → ℕ := R.readout () ()
    ∃ (A : DFA Bool (Fin (r + 1))) (B : DFA Bool (Fin (s + 1))),
      Threshold length A r ∧ Threshold length B s ∧ Threshold length (A.inter B) m

def arena : DependentFamily.Arena where
  signature := signature
  Law := law

abbrev sourceScope := type_of%
  (@_root_.D5.S0.Automata.FernauRystsovIntermediateReset.result)

private theorem erased_fails : ¬ law erased := by
  intro h
  obtain ⟨A, _, hA, _⟩ := h 1 0 1 (by decide) (by decide)
  obtain ⟨_, hlength, _⟩ := hA
  exact Nat.zero_ne_one hlength

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S0.Automata.FernauRystsovIntermediateReset.result, erased, erased_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity law actual erased erased_fails
  dependence := by
    intro i
    cases i
    exact ⟨(), [], [false], Nat.zero_ne_one⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S0.Automata.FernauRystsovIntermediateReset.result)
    (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S0.Automata.FernauRystsovIntermediateReset.result.__information_unit
  realizationName := `Reg.D5.S0.Automata.FernauRystsovIntermediateReset.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature (fun _ _ => List.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.FernauRystsovIntermediateReset
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Automata.FernauRystsovIntermediateReset
