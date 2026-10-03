import LeanInformationAuditInterface.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.History.FinitePrefixAntichainBudget
import Reg.Support.DependentFamily
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.BigOperators.Pi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.History.FinitePrefixAntichainBudget
namespace Reg.D5.S0.History.FinitePrefixAntichainBudget
universe u v
noncomputable section
open Classical
abbrev signature : Signature where
  Params := Σ E : Type u, Σ V : Type v, List E → V
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize signature
  (fun _ p h => p.2.2 h) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {E : Type u} {V : Type v} [DecidableEq E] [AddCommMonoid V]
    [Preorder V] [IsOrderedAddMonoid V] (m : List E → V),
    (∀ h (C : Finset E), ∑ a ∈ C, m (h ++ [a]) ≤ m h) →
    ∀ K : Finset (List E),
    (∀ h ∈ K, ∀ k ∈ K, h.IsPrefix k → h = k) →
    ∑ h ∈ K, m h ≤ R.readout () ⟨E, V, m⟩ []

def rejected : Realization signature.{u,v} := realize signature
  (fun _ p _ => p.2.2 (if h : Nonempty p.1 then [Classical.choice h] else []))
  (fun e => nomatch e)

def sample : List (ULift.{u} Unit) → (ULift.{v} Unit → ℕ) :=
  fun h _ => if h = [] then 1 else 0

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have localBudget : ∀ xs (C : Finset (ULift.{u} Unit)),
      ∑ a ∈ C, sample (xs ++ [a]) ≤ sample xs := by
    intro xs C
    intro z
    simp [sample, Finset.sum_apply]
  have bound := h sample localBudget {[]} (by simp)
  have b := bound (ULift.up ())
  simpa [rejected, realize, sample, Finset.sum_apply] using b

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Unit, (ULift.{v} Unit → ℕ), sample⟩, [], [⟨()⟩], by
      intro he
      have := congrFun he (ULift.up ())
      simpa [actual, realize, sample] using this⟩

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S0.History.FinitePrefixAntichainBudget
  coordinates := #[0, 1, 6]
  readouts := #[{path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "arg"], stateOperand := some #["arg"]}] }

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{max (max (u_2 + 2) (u_1 + 2)) ((max (u_1 + 1) (u_2 + 1)) + 2), max (max (u_2 + 2) (u_1 + 2)) ((max (u_1 + 1) (u_2 + 1)) + 2), max (u_1 + 1) (u_2 + 1), 1, 1, 0, 1, 1, 0, 0, 0, max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0, 0} (@_root_.D5.S0.History.FinitePrefixAntichainBudget.result.{u_1, u_2}) (type_of% (arena.{u_1, u_2})) (type_of% (arena.{u_1, u_2})) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2} (fun _ p h => p.2.2 h) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "History") "FinitePrefixAntichainBudget") "result") "Reg.D5.S0.History.FinitePrefixAntichainBudget/Reg.D5.S0.History.FinitePrefixAntichainBudget.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u_1, u_2})⟩,
  objectArena := ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2} (fun _ p h => p.2.2 h) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.History.FinitePrefixAntichainBudget, definition := none, coordinates := #[0, 1, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end
end Reg.D5.S0.History.FinitePrefixAntichainBudget
