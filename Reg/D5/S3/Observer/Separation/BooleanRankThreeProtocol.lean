import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanRankThreeProtocol
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol

open _root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => delta a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => false) (fun e => nomatch e)

/-- The complete negated necessity statement, with the decoder row as readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := ¬ (TaskData →
    Protocol Ftheta 3 3 alpha beta (R.readout () ()) →
    ∃ c d, Balanced Ftheta c d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro _ hp
  have bad := hp.2.2 1 0 true (by decide)
  change false = true at bad
  exact Bool.noConfusion bad

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have bad := congrFun h 0
    change false = true at bad
    exact Bool.noConfusion bad

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Observer.Separation.BooleanRankThreeProtocol.result) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ a => delta a) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanRankThreeProtocol") "result") "Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol/Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ a => delta a) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, definition := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeProtocol, name := `D5.S3.Observer.Separation.BooleanRankThreeProtocol.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "domain", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms result
#print axioms registration

end Reg.D5.S3.Observer.Separation.BooleanRankThreeProtocol
