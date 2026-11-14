import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.EqualBinaryRunBridge
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S1.Digit.EqualBinaryRunBridge

open _root_.D5.S1.Digit.EqualBinaryRunBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => List ℕ) (fun _ => List ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ ks => word ks) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n m : ℕ, m ∈ row n ↔
    0 < m ∧ Even m ∧ ∃! ks : List ℕ,
      (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ bits m = R.readout () () ks

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : 2 ∈ row 1 := by
    classical
    apply Finset.mem_filter.mpr
    refine ⟨by decide, ?_⟩
    refine ⟨by decide, ⟨1, rfl⟩, rfl, ?_⟩
    change Matched [[1], [0]]
    simp [Matched]
  obtain ⟨_, _, ks, hk, _⟩ := (h 1 2).mp hm
  have he := hk.2.2
  change ([1, 0] : List ℕ) = [] at he
  contradiction

def evidence : Registration arena
    (∀ n m : ℕ, m ∈ row n ↔
      0 < m ∧ Even m ∧ ∃! ks : List ℕ,
        (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ bits m = word ks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mem_row_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), [], [1], ?_⟩
    change ([] : List ℕ) ≠ [1, 0]
    decide

def membershipRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.EqualBinaryRunBridge.mem_row_iff)
    (type_of% (realize signature (fun _ _ ks => word ks) (fun e => nomatch e)))
    Unit Unit where
  unitName := `Reg.D5.S1.Digit.EqualBinaryRunBridge.membershipUnit
  realizationName := `Reg.D5.S1.Digit.EqualBinaryRunBridge.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ks => word ks) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Digit.EqualBinaryRunBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Digit.EqualBinaryRunBridge
