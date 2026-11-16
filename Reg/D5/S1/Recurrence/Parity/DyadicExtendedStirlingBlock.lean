import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
import Reg.Support.DependentFamily

/-! A source-bound audit of the rational dyadic block law. -/

noncomputable section
namespace Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => T n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The full source law, with the left array observation variable and the right operands fixed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 1 ≤ n → 2 ≤ k →
    R.readout () n k = ((k : ℚ) - 1) ^ g n * T (h n) (k - 1) +
      (k : ℚ) ^ (g n + 1) * T (h n) k

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro hh
  have hh12 := hh 1 2 (by omega) (by omega)
  norm_num [rejected, realize, g, h, T] at hh12

def family : Registration arena (type_of% dyadic_extended_stirling_block) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_extended_stirling_block, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), ?_⟩
    change T 1 2 ≠ T 1 3
    norm_num [T]

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dyadic_extended_stirling_block) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.blockUnit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
