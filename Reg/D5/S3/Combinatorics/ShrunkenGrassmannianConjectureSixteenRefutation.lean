import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange (normalWord)

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ k => ecc k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k L N =>
    if k = 3 then (L * (N - L) + 1) / 2
    else if k = 4 then formulaFour L N else formulaFive L N) (fun e => nomatch e)

/-- The whole negated disjunction, retaining all three clauses for each reading. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ (conjSixteen (r.readout () ()) ∨ conjSixteen diam)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  left
  constructor
  · intro L N _ _ _
    rfl
  constructor
  · intro L N _ _ _
    rfl
  · exact ⟨0, fun _ _ _ _ => rfl⟩

/-- With a window longer than the word no edge exists, at every reach depth. -/
theorem oversize_reach (m : ℕ) (x y : List Bool) (hx : x.length < 5)
    (h : Reach 5 m x y) : y = x := by
  induction m generalizing y with
  | zero => exact h
  | succ m ih =>
    rcases h with h | ⟨z, hz, i, hi, _⟩
    · exact ih y h
    · have hz := ih z hz
      subst z
      omega

theorem oversize_ecc : ecc 5 2 4 = 0 := by
  have empty : {m | ∀ y, IsVertex 2 4 y → Reach 5 m (normalWord 2 (4 - 2)) y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro m h
    have hreach := h [true, true, false, false] ⟨rfl, rfl⟩
    have equal := oversize_reach m _ _ (by decide) hreach
    have : ([true, true, false, false] : List Bool) = [false, false, true, true] := equal
    contradiction
  simp only [ecc, empty, Nat.sInf_empty]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 3, 5, ?_⟩
  intro h
  have equal := congrFun (congrFun h 2) 4
  change ecc 3 2 4 = ecc 5 2 4 at equal
  rw [oversize_ecc,
    (_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
      2 4 (by decide) (by decide) (by decide)).1] at equal
  contradiction

noncomputable def registration : Registration arena
    (¬ _root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => ecc k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "ShrunkenGrassmannianConjectureSixteenRefutation") "result") "Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation/Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => ecc k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, definition := some { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, name := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation


noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.arena
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.arena
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.arena) (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).actual

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).bridge

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.observation0 : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.signature PUnit.unit.{1} →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.signature PUnit.unit.{1} PUnit.unit.{1} :=
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.signature
  Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"claim\"],\"part\":\"value\",\"path\":[\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim, part := .value, path := [.function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).actual (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).variation.2.choose (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).variation.1 (Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"ShrunkenGrassmannianConjectureSixteenRefutation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation, declaration := `Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
