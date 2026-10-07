import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
open _root_.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → Fin n
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => ⇑s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => id) (fun e => nomatch e)

/-- The complete claim; only the permutation in the fixed-point condition is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ n : ℕ, 2 < n →
    ((∃ s : Equiv.Perm (Fin n), (∀ i, O.readout () n s i ≠ i) ∧
      ∀ X : Type, IsSolution n (simpleMap (X := X) s)) ↔ Even n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs, -⟩ := (h 4 (by norm_num)).mpr (by decide)
  exact hs 0 rfl

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, Equiv.refl (Fin 2), (Equiv.swap (0 : Fin 2) 1 : Equiv.Perm (Fin 2)),
    fun h => ?_⟩
  have h0 : Equiv.refl (Fin 2) 0 = Equiv.swap (0 : Fin 2) 1 0 := congrFun h (0 : Fin 2)
  simp at h0

def registration : Registration arena claim where
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
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => ⇑s) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "StatisticalMechanics") "VertexModels") "SimplexFixedPointFreePermutations") "result") "Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations/Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => ⇑s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, definition := some { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, name := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.claim, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body", "fn", "arg", "body", "fn", "arg", "fn"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalArenaFact, `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.sourceBridgeFact, `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.observationFact0, `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations


noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.arena
noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.arena) (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).actual

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).bridge

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.observation0 : (n : Nat) →
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    (s : Equiv.Perm.{1} (Fin n)) →
      (i : Fin n) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.signature PUnit.unit.{1} n :=
  fun (n : Nat) (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
    (s : Equiv.Perm.{1} (Fin n)) (i : Fin n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.signature
    Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.actual PUnit.unit.{1} n s

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"argument\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.claim, part := .value, path := [.body, .body, .function, .argument, .argument, .body, .function, .argument, .body, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).actual (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).variation.2.choose (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).variation.1 (Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"VertexModels\",\"SimplexFixedPointFreePermutations\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations, declaration := `Reg.D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
