import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- A known high-bit coordinate selects the full physical clock/readout function. -/
abbrev signature : Signature where
  Params := Nat
  State _ := Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat → Nat → Fin 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Nat) (b : Fin 2),
    let P := 2 ^ j
    let read := R.readout () j b
    (∀ n r, r < P →
      (read n r).val = (b.val + n / P + (threshold P n r).val) % 2 ∧
      sensor P b n r = threshold P n r) ∧
    IsLeast (waitingBounds P j read) (sharpWait j) ∧
    CorrectOn read (rawMidpoint P b j) 0 0 P ∧
    ∀ r, r < P → (execute read (rawMidpoint P b j) 0 r).2 ≤ sharpWait j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0 1).1 0 0 (by decide)
  norm_num [rejected, realize, threshold] at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_forward_waiting_optimality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro h
    have point := congrFun (congrFun h 0) 0
    norm_num [actual, realize, rawBit] at point

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Budget") "DyadicForwardWaitingOptimality") "dyadic_forward_waiting_optimality") "Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality/Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "value"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
