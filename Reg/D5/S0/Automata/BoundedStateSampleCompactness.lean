import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Automata.BoundedStateSampleCompactness
import Reg.Support.DependentFamily

namespace Reg.D5.S0.Automata.BoundedStateSampleCompactness

open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.BoundedStateSampleCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The same budget must be used for global and finite-sample realizability. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {Alphabet : Type u} {Output : Type v} [Finite Alphabet] [Finite Output]
    (D : Set (List Alphabet)) (target : D → Output) (s : ℕ),
    (∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
      Fintype.card State ≤ s ∧ CorrectOnFamily machine Subtype.val target) ↔
    ∀ E : Finset D,
      ∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
        Fintype.card State ≤ R.readout () () s ∧
          FitsSubsample machine Subtype.val target (fun i : E => i.val)

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let D : Set (List (ULift.{u} Unit)) := ∅
  let target : D → ULift.{v} Unit := fun _ => ⟨()⟩
  have hiff := h D target 1
  have global : ∃ (State : Type w) (_ : Fintype State)
      (machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) State),
      Fintype.card State ≤ 1 ∧ CorrectOnFamily machine Subtype.val target := by
    let machine : DFAO (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) :=
      { start := ⟨()⟩, step := fun q _ => q, accept := ∅, output := fun _ => ⟨()⟩ }
    refine ⟨ULift.{w} Unit, inferInstance, machine, by simp, ?_⟩
    intro i
    exact False.elim i.property
  obtain ⟨State, inst, machine, bound, _⟩ := hiff.mp global ∅
  have positive : 0 < Fintype.card State := Fintype.card_pos_iff.mpr ⟨machine.start⟩
  change Fintype.card State ≤ 0 at bound
  omega

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_state_sample_compactness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (0 : ℕ) ≠ 1; decide⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness.{u, v, w}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "Automata") "BoundedStateSampleCompactness") "bounded_state_sample_compactness") "Reg.D5.S0.Automata.BoundedStateSampleCompactness/Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u, v, w})⟩,
  objectArena := .source ⟨(arena.{u, v, w})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v, w}) ⟨(registration.{u, v, w})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.Automata.BoundedStateSampleCompactness, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Automata.BoundedStateSampleCompactness, declaration := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness, part := .type, path := [], levels := [.param `u, .param `v, .param `w] },
    { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v, .param `w] }], facts := [`Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalArenaFact, `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.sourceBridgeFact, `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.observationFact0, `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S0.Automata.BoundedStateSampleCompactness


noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalArenaOperand.{u, v, w} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}
noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalArenaFact.{u, v, w} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"))
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v), (.param `w)] }
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  .evidence
noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalObjectArenaOperand.{u, v, w} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}
noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalObjectArenaFact.{u, v, w} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"))
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v), (.param `w)] }
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  .evidence


noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.sourceLaw.{u, v, w} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.) (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).actual

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.sourceBridgeFact.{u, v, w} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"bounded_state_sample_compactness\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"))
  { owner := `D5.S0.Automata.BoundedStateSampleCompactness, declaration := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness, part := .type, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).bridge

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.observation0.{u, v, w} : {Alphabet : Type u} →
  {Output : Type v} →
    [Finite.{u + 1} Alphabet] →
      [Finite.{v + 1} Output] →
        (D : Set.{u} (List.{u} Alphabet)) →
          (target : @Set.Elem.{u} (List.{u} Alphabet) D → Output) →
            (s : Nat) →
              (E : Finset.{u} (@Set.Elem.{u} (List.{u} Alphabet) D)) →
                (State : Type w) →
                  Fintype.{w} State →
                    (machine : D5.S0.Automata.DFAOStateLowerBound.DFAO.{u, v, w} Alphabet Output State) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S0.Automata.BoundedStateSampleCompactness.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {Alphabet : Type u} {Output : Type v} [Finite.{u + 1} Alphabet] [Finite.{v + 1} Output]
    (D : Set.{u} (List.{u} Alphabet)) (target : @Set.Elem.{u} (List.{u} Alphabet) D → Output) (s : Nat)
    (E : Finset.{u} (@Set.Elem.{u} (List.{u} Alphabet) D)) (State : Type w) (x : Fintype.{w} State)
    (machine : D5.S0.Automata.DFAOStateLowerBound.DFAO.{u, v, w} Alphabet Output State) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S0.Automata.BoundedStateSampleCompactness.signature Reg.D5.S0.Automata.BoundedStateSampleCompactness.actual
    PUnit.unit.{1} PUnit.unit.{1} s

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.observationFact0.{u, v, w} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"bounded_state_sample_compactness\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"))
  { owner := `D5.S0.Automata.BoundedStateSampleCompactness, declaration := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .body, .function, .argument, .argument], levels := [(.param `u), (.param `v), (.param `w)] }
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.observation0, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.varyingLawInput.{u, v, w} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.canonicalArenaOperand.{u, v, w})
noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.varyingLaw.{u, v, w}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.statementExclusion.{u, v, w} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"bounded_state_sample_compactness\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  statementLocation := { owner := `D5.S0.Automata.BoundedStateSampleCompactness, declaration := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness, part := .type, path := [], levels := [(.param `u), (.param `v), (.param `w)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).actual (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).variation.2.choose (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).variation.1 (Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}).variation.2.choose_spec

noncomputable def Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Automata\",\"BoundedStateSampleCompactness\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]],[\"param\",[\"w\"]]]}"))
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v), (.param `w)] }
  { owner := `Reg.D5.S0.Automata.BoundedStateSampleCompactness, declaration := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v), (.param `w)] }
  (by first | rfl | (ext <;> rfl))
