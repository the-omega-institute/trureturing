import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Point
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => vertex n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => vertex (n + 1)) (fun e => nomatch e)

/-- All nine geometric clauses and all three infinite series identities remain in the law.
Only the first vertex in the adjacent-edge squared distance is intervened on. -/
def arena : Arena where
  signature := signature
  Law r :=
    (∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (r.readout () () n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have edge := (h.1 0).2.1
  norm_num [rejected, realize, sqDist] at edge

def registration : Registration arena
    ((∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (vertex n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    have edge := (_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result.1 0).2.1
    change vertex 0 = vertex 1 at h
    simp only [Nat.zero_add, h, sqDist, sub_self, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] at edge
    norm_num at edge

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => vertex n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "BoerdijkCoxeterGeneratingFunctions") "result") "Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions/Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => vertex n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceBridgeFact, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observationFact0, `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions


noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.arena) (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).actual

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).bridge

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observation0 : (n : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.signature
    Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [.function, .argument, .body, .argument, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).actual (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.2.choose (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.1 (Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"BoerdijkCoxeterGeneratingFunctions\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions, declaration := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
