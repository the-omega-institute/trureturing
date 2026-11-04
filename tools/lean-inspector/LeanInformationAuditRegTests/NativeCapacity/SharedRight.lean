import LeanInformationAuditRegTests.NativeCapacity.Source
import LeanInformationAuditRegTests.NativeCapacity.Left

open _root_.D5.S0.Conventions
open _root_.D5.S0.Tower.GoldenGapZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open LeanInformationAuditRegTests.NativeCapacity.Source

namespace LeanInformationAuditRegTests.NativeCapacity.SharedRight
noncomputable section
theorem target : ∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
    wdigits (Nat.fib (Q + 3) + j.val) = (Q + 3) :: wdigits j.val := wdigits_fib_add

def registration : Registration arena
    (∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
      wdigits (Nat.fib (Q + 3) + j.val) = (Q + 3) :: wdigits j.val) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wdigits_fib_add, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), ⟨0, by norm_num [Nat.fib]⟩, ⟨1, by norm_num [Nat.fib]⟩, ?_⟩
    change wdigits 3 ≠ wdigits 4
    intro he
    have hd := congrArg (fun l : List ℕ => (l.map Nat.fib).sum) he
    rw [decode_wdigits, decode_wdigits] at hd
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (target) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `NativeCapacity.sharedRight,
  realizationName := `LeanInformationAuditRegTests.NativeCapacity.SharedRight.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `LeanInformationAuditRegTests.NativeCapacity.SharedRight, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end
end LeanInformationAuditRegTests.NativeCapacity.SharedRight
