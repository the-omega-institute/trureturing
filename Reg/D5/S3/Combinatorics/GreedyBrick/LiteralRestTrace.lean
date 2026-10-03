import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GreedyBrick.SuccessorBand
open _root_.D5.S3.Combinatorics.GreedyBrick.RestBlock
open _root_.D5.S3.Combinatorics.GreedyBrick.EventRealization
open _root_.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality

namespace Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace

abbrev signature : Signature where
  Params := RestTrace
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ T e => (T.state e).capacity.reverse) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun a => nomatch a)

/-- Only the sampled capacity observation varies. Every original existential,
clock, intermediate-placement and interval clause remains in the law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ T : RestTrace,
    (∀ e, T.bin (e + 1) = firstZeroBin (T.state e).capacity) ∧
    (∀ e, r.readout () T e = trajectory (T.state e).endpoint) ∧
    StrictMono (fun e => (T.state e).endpoint) ∧
    (∀ N, ∃ e, N ≤ (T.state e).endpoint) ∧
    (∀ e d, placeBricks (T.state e).endpoint (T.state e).capacity.reverse d =
      trajectory ((T.state e).endpoint + d)) ∧
    (∀ N, 1 ≤ N → ∃ e d, d < T.bin (e + 1) ∧
      N = (T.state e).endpoint + d ∧
      trajectory N = placeBricks (T.state e).endpoint (T.state e).capacity.reverse d)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨T, _, h, _⟩
  have hz := h 0
  change [] = trajectory (T.state 0).endpoint at hz
  rw [T.initial_endpoint] at hz
  simp [trajectory, step, transfer] at hz

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_trace_realization, rejected, rejected_law⟩
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
    obtain ⟨T, _⟩ := literal_trace_realization
    obtain ⟨e, he⟩ := T.unbounded 2
    refine ⟨T, 0, e, ?_⟩
    intro h
    change (T.state 0).capacity.reverse = (T.state e).capacity.reverse at h
    have hh := congrArg List.length h
    simp only [List.length_reverse, T.initial_capacity, List.length_singleton] at hh
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ T e => (T.state e).capacity.reverse) (fun a => nomatch a))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "GreedyBrick") "LiteralRestTrace") "literal_trace_realization") "Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace/Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ T e => (T.state e).capacity.reverse) (fun a => nomatch a)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, definition := none, coordinates := #[0], readouts := #[{ path := #["arg", "body", "arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace
