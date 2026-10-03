import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Tower.GoldenGapZeckendorf
import Reg.Support.DependentFamily

open _root_.D5.S0.Conventions
open _root_.D5.S0.Tower.GoldenGapZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Tower.GoldenGapZeckendorf

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State Q := Fin (Nat.fib (Q + 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
    R.readout () Q j = (Q + 3) :: wdigits j.val

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have hh := hr 0 ⟨0, by norm_num [Nat.fib]⟩
  change [] = 3 :: wdigits 0 at hh
  simp at hh

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "Tower") "GoldenGapZeckendorf") "wdigits_fib_add") "Reg.D5.S0.Tower.GoldenGapZeckendorf/Reg.D5.S0.Tower.GoldenGapZeckendorf.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.Tower.GoldenGapZeckendorf, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end
end Reg.D5.S0.Tower.GoldenGapZeckendorf
