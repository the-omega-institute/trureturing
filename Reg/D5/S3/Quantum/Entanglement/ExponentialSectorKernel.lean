import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ExponentialSectorKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 / x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ (loss : ℕ → ℝ) (_horder : Monotone loss) (n : ℕ),
    (∀ w : Fin (n + 1) → ℝ, 0 ≤ energy n loss w) ∧
    (∀ i, 0 ≤ equilibriumWeight n loss i) ∧
    (∀ i : Fin (n + 1),
      ∑ j : Fin (n + 1), kernel loss i j * equilibriumWeight n loss j = 1) ∧
    (∑ i, equilibriumWeight n loss i) = normalizer n loss ∧
    0 < normalizer n loss ∧
    (fun i => equilibriumWeight n loss i / normalizer n loss) ∈
      stdSimplex ℝ (Fin (n + 1)) ∧
    energy n loss (fun i => equilibriumWeight n loss i / normalizer n loss) =
      observation.readout () () (normalizer n loss) ∧
    (∀ p ∈ stdSimplex ℝ (Fin (n + 1)),
      1 / normalizer n loss ≤ energy n loss p) ∧
    normalizer n loss = 1 +
      ∑ i : Fin n, Real.tanh ((loss (i + 1) - loss i) / 4) ∧
    1 - kernel loss 0 n ≤ 2 * (1 - 1 / normalizer n loss) ∧
    2 * (1 - 1 / normalizer n loss) ≤
      2 * (loss n - loss 0) / (4 + (loss n - loss 0)) ∧
    (∀ epsilon : ℝ, epsilon < 2 →
      (2 * (1 - 1 / normalizer n loss) ≤ epsilon ↔
        normalizer n loss - 1 ≤ epsilon / (2 - epsilon))) ∧
    ((∀ i < n, loss i < loss (i + 1)) → ∀ i, 0 < equilibriumWeight n loss i)

theorem actual_law : arena.Law actual := by
  intro loss horder n
  exact _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result loss horder n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (fun _ => 0) (by intro i j hij; rfl) 0).2.2.2.2.2.2.1
  norm_num [energy, equilibriumWeight, normalizer, kernel, rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 / x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "ExponentialSectorKernel") "result") "Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel/Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 / x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.anchorEnumeration }


#print axioms _root_.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result
#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel


noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
      Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.actual)
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration)

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.arena
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.actual)
  Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration)

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.observation0 : (loss : Nat → Real) →
  (horder : @Monotone.{0, 0} Nat Real Nat.instPreorder Real.instPreorder loss) →
    (n : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (loss : Nat → Real) (horder : @Monotone.{0, 0} Nat Real Nat.instPreorder Real.instPreorder loss) (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.signature
    Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.actual PUnit.unit.{1} PUnit.unit.{1}
    (D5.S3.Quantum.Entanglement.ExponentialSectorKernel.normalizer n loss)

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result, part := .type, path := [.body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `D5.S3.Quantum.Entanglement.ExponentialSectorKernel.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration).actual (Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration).variation.1 (Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ExponentialSectorKernel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel, declaration := `Reg.D5.S3.Quantum.Entanglement.ExponentialSectorKernel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
