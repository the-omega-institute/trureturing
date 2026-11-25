import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalGramOddPrime

/-! The ambient dimension on the threshold side of rational Gram realization. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalGramOddPrime

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalGramOddPrime (hasUnitGram realizable_iff)
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, (∃ a b c d : Fin n → ℚ, hasUnitGram a b c d) ↔
    7 ≤ R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₆ : 7 ≤ rejected.readout () () 6 := by decide
  have impossible := (realizable_iff 6).mp ((h 6).mpr h₆)
  omega

def family : Registration arena (type_of% @realizable_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realizable_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 6, 7, by
    change (6 : ℕ) ≠ 7
    decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@realizable_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramOddPrime.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramOddPrime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalGramOddPrime
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalGramOddPrime
