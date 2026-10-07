import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ T e => (T.state e).capacity.reverse) (fun a => nomatch a))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "GreedyBrick") "LiteralRestTrace") "literal_trace_realization") "Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace/Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration,
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
    (fun _ T e => (T.state e).capacity.reverse) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, definition := none, coordinates := #[0], readouts := #[{ path := #["arg", "body", "arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
      Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.actual)
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration)

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"literal_trace_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.arena
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.actual)
  Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration)

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.observation0 : (T : D5.S3.Combinatorics.GreedyBrick.EventRealization.RestTrace) →
  (e : Nat) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.signature PUnit.unit.{1} T :=
  fun (T : D5.S3.Combinatorics.GreedyBrick.EventRealization.RestTrace) (e : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.signature
    Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.actual PUnit.unit.{1} T e

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"literal_trace_realization\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization, part := .type, path := [.argument, .body, .argument, .function, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"literal_trace_realization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.literal_trace_realization, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration).actual (Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration).variation.2.choose (Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration).variation.1 (Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"GreedyBrick\",\"LiteralRestTrace\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace, declaration := `Reg.D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
