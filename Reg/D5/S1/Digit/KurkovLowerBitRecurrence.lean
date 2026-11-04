import D5.S1.Digit.KurkovLowerBitRecurrence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open D5.S1.Digit.KurkovWeightProductBinomial (a)
open D5.S1.Digit.DyadicRowPolynomialRecurrence (wt)
namespace Reg.D5.S1.Digit.KurkovLowerBitRecurrence
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := a 0 = 1 ∧ a 1 = 2 ∧
    (∀ n : ℕ, 1 < n → a n = (1 + wt n) * a (n / 2)) ∧
    (∀ n : ℕ, 1 < n →
      R.readout () () n = 2 * a (n - 2 ^ Nat.log 2 n) +
        ∑ k ∈ Finset.range (Nat.log 2 n),
          a (n - 2 ^ Nat.log 2 n + 2 ^ k * (1 - n / 2 ^ k % 2)))
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.2.2 2 (by decide)
  have hi := D5.S1.Digit.KurkovLowerBitRecurrence.result.2.2.2 2 (by decide)
  change a 2 + 1 = _ at hh
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨D5.S1.Digit.KurkovLowerBitRecurrence.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [D5.S1.Digit.KurkovLowerBitRecurrence.result.1,
      D5.S1.Digit.KurkovLowerBitRecurrence.result.2.1]
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.KurkovLowerBitRecurrence.result)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ n => a n) (fun e => nomatch e)))
    Unit Unit := {
  unitName := .str (.str `D5.S1.Digit.KurkovLowerBitRecurrence.result "Reg.D5.S1.Digit.KurkovLowerBitRecurrence/Reg.D5.S1.Digit.KurkovLowerBitRecurrence.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S1.Digit.KurkovLowerBitRecurrence.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S1.Digit.KurkovLowerBitRecurrence, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S1.Digit.KurkovLowerBitRecurrence
