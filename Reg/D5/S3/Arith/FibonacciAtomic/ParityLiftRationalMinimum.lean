import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ × ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => parityTask w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

/-- Vary the complete word response while preserving the linear minimum contract. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ w : List Window, wordBehavior fourDimensional w = R.readout () () w) ∧
    Module.finrank ℚ BlockState = 4 ∧
    (∀ (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (R : WordRepresentation ℚ Window V (ℚ × ℚ)),
      (∀ w : List Window, wordBehavior R w = parityTask w) → 4 ≤ Module.finrank ℚ V) ∧
    parityTask [.middle] = (1, 1) ∧ integerRationalTask [.middle] = (1, 3) ∧
    responseMinor = !![1, 1, 0, 0; 1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0] ∧
    responseMinor.det = 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h.1 []
  have hne : wordBehavior fourDimensional [] ≠ (0, 0) := by decide +kernel
  exact hne hz

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result.{u}, rejected, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u}⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), ([] : List Window), ([.middle] : List Window), ?_⟩
    change parityTask [] ≠ parityTask [.middle]
    decide +kernel

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.result.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => parityTask w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "ParityLiftRationalMinimum") "result") "Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum/Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => parityTask w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
      Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1})

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.arena.{u_1}
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1})

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.observation0 : (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.signature
    Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.actual PUnit.unit.{1} PUnit.unit.{1} w

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"result\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.result, part := .type, path := [.function, .argument, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1}).actual (Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1}).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1}).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ParityLiftRationalMinimum\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
