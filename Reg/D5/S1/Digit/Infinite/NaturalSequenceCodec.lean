import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.NaturalSequenceCodec
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S1.Digit.Infinite.NaturalSequenceCodec

open _root_.D5.S1.Digit.Infinite.NaturalSequenceCodec
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ → ℕ) (fun _ => ℕ) (fun _ => List Bool)

def actual : Realization signature :=
  realize signature (fun _ p n => encodedPrefix p n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

/-- The entire transport assertion, with its finite block observation exposed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ p : ℕ → ℕ,
    (∀ n : ℕ, Stream'.take (encodedPrefix p n).length (encode p).val = encodedPrefix p n ∧
      2 * n ≤ (R.readout () p n).length) ∧
    (∀ n, recoverPrefix (encode p).val ⟨p, rfl⟩ n = Stream'.take n p) ∧
    (∀ q : ℕ → ℕ, encode p = encode q → p = q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := (h (fun _ => 0)).1 1
  have hn := hf.2
  change 2 * 1 ≤ 0 at hn
  omega

def evidence : Registration arena
    (∀ p : ℕ → ℕ,
      (∀ n : ℕ, Stream'.take (encodedPrefix p n).length (encode p).val = encodedPrefix p n ∧
        2 * n ≤ (encodedPrefix p n).length) ∧
      (∀ n, recoverPrefix (encode p).val ⟨p, rfl⟩ n = Stream'.take n p) ∧
      (∀ q : ℕ → ℕ, encode p = encode q → p = q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨natural_sequence_transport, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨fun _ => 0, (0 : ℕ), (1 : ℕ), ?_⟩
    change ([] : List Bool) ≠ [false, false]
    decide

def transportRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.NaturalSequenceCodec.natural_sequence_transport)
    (type_of% (realize signature (fun _ p n => encodedPrefix p n) (fun e => nomatch e)))
    Unit Unit where
  unitName := `Reg.D5.S1.Digit.Infinite.NaturalSequenceCodec.transportUnit
  realizationName := `Reg.D5.S1.Digit.Infinite.NaturalSequenceCodec.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => encodedPrefix p n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.NaturalSequenceCodec
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Digit.Infinite.NaturalSequenceCodec
