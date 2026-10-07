import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
open _root_.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete negated claim; only the matrix in `WeaklyConnected A` is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 ≤ A i j) → (∀ i, A i i = 0) →
    WeaklyConnected (O.readout () n A) → ∀ g, IsForwardLevels A g → forwardDemocracy A g ≤ 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n A _ hdiag hconn g _
  change WeaklyConnected (0 : Matrix (Fin n) (Fin n) ℝ) at hconn
  rcases n with _ | _ | n
  · exact hconn.nonempty.elim fun v => Fin.elim0 v
  · have hA : A = 0 := by
      ext i j
      fin_cases i; fin_cases j
      exact hdiag 0
    subst hA
    simp [forwardDemocracy]
  · exfalso
    obtain ⟨w⟩ := hconn.preconnected 0 1
    cases w with
    | cons hadj _ =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with hlt | hlt <;> simp at hlt

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  change (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 at this
  simp at this

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
    · intro i; exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ A => A) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "HierarchyDemocracyRefutation") "result") "Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation/Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ A => A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, definition := some { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, name := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim, path := #["arg"] }, coordinates := #[0], readouts := #[{ path := #["arg", "body", "body", "body", "body", "domain", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation


noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena
noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena
noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena
    (Not D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim)
    Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.arena
  (Not D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim)
  Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.observation0 : (n : Nat) →
  (A : Matrix.{0, 0, 0} (Fin n) (Fin n) Real) →
    (∀ (i j : Fin n),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (A i j)) →
      (∀ (i : Fin n),
          @Eq.{1} Real (A i i) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.signature PUnit.unit.{1} n :=
  fun (n : Nat) (A : Matrix.{0, 0, 0} (Fin n) (Fin n) Real)
    (a :
      ∀ (i j : Fin n),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (A i j))
    (a_1 :
      ∀ (i : Fin n),
        @Eq.{1} Real (A i i) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.signature
    Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.actual PUnit.unit.{1} n A

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.claim, part := .value, path := [.body, .body, .body, .body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration).actual (Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration).variation.1 (Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"HierarchyDemocracyRefutation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation, declaration := `Reg.D5.S3.Combinatorics.Graph.HierarchyDemocracyRefutation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
