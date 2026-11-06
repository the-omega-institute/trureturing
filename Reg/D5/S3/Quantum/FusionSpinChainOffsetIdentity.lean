import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.FusionSpinChainOffsetIdentity
import Reg.Support.DependentFamily

/-! Source-bound audit for the Fibonacci fusion-chain offset identity. -/

namespace Reg.D5.S3.Quantum.FusionSpinChainOffsetIdentity

open _root_.D5.S3.Quantum.FusionSpinChainOffsetIdentity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℤ, |k| < n →
    R.readout () () (n + k) * R.readout () () (n - k) -
      R.readout () () n ^ 2 = Int.fib (2 * |k|) ^ 2

def actual : Realization signature :=
  realize signature (fun _ _ (n : ℤ) => fusionDim n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 1 (by norm_num)
  change (0 : ℤ) * 0 - 0 ^ 2 = Int.fib (2 * |(1 : ℤ)|) ^ 2 at hh
  norm_num [Int.fib] at hh

def registration : Registration arena
    (∀ (n k : ℤ), |k| < n →
      fusionDim (n + k) * fusionDim (n - k) - fusionDim n ^ 2 =
        Int.fib (2 * |k|) ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(by
      intro n k hk
      change fusionDim (n + k) * fusionDim (n - k) - fusionDim n ^ 2 =
        Int.fib (2 * |k|) ^ 2
      exact exact_offset_identity hk), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (1 : ℤ), (2 : ℤ), ?_⟩
    change fusionDim 1 ≠ fusionDim 2
    norm_num [fusionDim, Int.fib]

noncomputable def audit :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.FusionSpinChainOffsetIdentity.exact_offset_identity)
      (type_of% (realize.{0, 0, 0, 0, 0} signature
        (fun _ _ (n : ℤ) => fusionDim n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `D5.S3.Quantum.FusionSpinChainOffsetIdentity.exact_offset_identity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.FusionSpinChainOffsetIdentity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (n : ℤ) => fusionDim n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.FusionSpinChainOffsetIdentity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms registration

end
end Reg.D5.S3.Quantum.FusionSpinChainOffsetIdentity
