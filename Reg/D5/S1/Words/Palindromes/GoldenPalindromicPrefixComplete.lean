import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete
import Reg.Support.DependentFamily

open _root_.D5.S1.Words
open _root_.D5.S0.Tower.GoldenGapWord
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[reducible] def substSignature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def substActual : Realization substSignature :=
  realize substSignature (fun _ _ w => w.flatMap subst) (fun e => nomatch e)

def substRejected : Realization substSignature :=
  realize substSignature (fun _ _ _ => []) (fun e => nomatch e)

@[reducible] def substArena : Arena where
  signature := substSignature
  Law R := Function.Injective (R.readout () ())

theorem substRejectedLaw : ¬ substArena.Law substRejected := by
  intro h
  have hh := h (a₁ := []) (a₂ := [false]) rfl
  cases hh

def substRegistration : Registration substArena (substArena.Law substActual) where
  actual := substActual
  bridge := Iff.rfl
  variation := ⟨flatMap_subst_injective, substRejected, substRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨substRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, substRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), [], [false], ?_⟩
    change ([] : List Bool) ≠ [true]
    decide


#print axioms substRegistration

def substReadoutSelection : LeanInformationAudit.Contract.ReadoutSelection := {
  path := #["arg"],
  stateBinder := 0,
  functionOperand := true,
  stateOperand := none,
  booleanPredicate := false }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.flatMap_subst_injective)
    (type_of% (realize substSignature substActual.readout substActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S1.Words.flatMap_subst_injective
    "Reg.D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete/substArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete.substRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨substArena⟩,
  objectArena := .source ⟨substArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source substArena ⟨substRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize substSignature substActual.readout substActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete,
    definition := none,
    coordinates := #[],
    readouts := #[substReadoutSelection] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S1.Words.Palindromes.GoldenPalindromicPrefixComplete
