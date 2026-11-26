import D5.S3.Combinatorics.Geometry.Permutohedra.IrredundantAtomSizes
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound cardinality observations of a generating family of atoms. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.IrredundantAtomSizes

open _root_.Rossi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Finset (Face n)) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ A => A.card) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 3 ≤ n) (x : Face n) (_ : 2 ≤ rank x) (k : ℕ),
    (∃ A : Finset (Face n), R.readout () n A = k ∧ (∀ a ∈ A, IsAtom a) ∧
      A.sup id = x ∧ (∀ B : Finset (Face n), B ⊂ A → B.sup id < x)) ↔
    2 ≤ k ∧ (k : ℤ) ≤ rank x

private def topChain : CutChain 3 where
  cuts := ∅
  proper := by simp
  comparable := by simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨_, h, _, _, _⟩ := (law 3 (by decide) topChain (by decide) 2).mpr (by decide)
  exact (by decide : (0 : ℕ) ≠ 2) h

noncomputable def evidence : Registration arena (type_of% Rossi.exact_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Rossi.exact_spectrum, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨3, ∅, {atom (Equiv.refl (Fin 3))}, by
      change (∅ : Finset (Face 3)).card ≠ ({atom (Equiv.refl (Fin 3))} : Finset _).card
      simp⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      Rossi.exact_spectrum (Realization signature) Unit Unit where
  unitName := `Rossi.exact_spectrum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.IrredundantAtomSizes.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.IrredundantAtomSizes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.IrredundantAtomSizes
