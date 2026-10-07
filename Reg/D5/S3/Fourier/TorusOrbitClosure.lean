import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.TorusOrbitClosure
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Fourier.TorusOrbitClosure
open _root_.D5.S3.Fourier.TorusOrbitClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped BigOperators
noncomputable section
universe u

def signature : Signature where
  Params := Type u
  State I := I → Circle
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := ℕ → (I → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (g z : I → Circle),
    z ∈ closure (range (R.readout () I g)) ↔
      ∀ k : I → ℤ, (∏ i, g i ^ k i) = 1 → (∏ i, z i ^ k i) = 1

def actual : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (I : Type u) (g : I → Circle) (n : ℕ) => g ^ n)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (I : Type u) (_ : I → Circle) (_ : ℕ) => (1 : I → Circle))
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have hz := (h (I := ULift.{u} Unit) (fun _ => -1) (fun _ => -1)).mpr
    (by intro k hk; exact hk)
  change (fun _ : ULift.{u} Unit => (-1 : Circle)) ∈
    closure (range (fun _ : ℕ => (1 : ULift.{u} Unit → Circle))) at hz
  rw [range_const, isClosed_singleton.closure_eq, mem_singleton_iff] at hz
  have heq := congrArg (fun f : ULift.{u} Unit → Circle => ((f ⟨()⟩ : Circle) : ℂ)) hz
  norm_num at heq

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro I hI g z; exact result g z, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, (fun _ => -1), (fun _ => 1), ?_⟩
    intro h
    have heq := congrArg
      (fun f : ℕ → ULift.{u} Unit → Circle => ((f 1 ⟨()⟩ : Circle) : ℂ)) h
    norm_num [actual, realize] at heq

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.TorusOrbitClosure.result.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
    (fun (_ : Unit) (I : Type (u_1)) (g : I → Circle) (n : ℕ) => g ^ n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "TorusOrbitClosure") "result") "Reg.D5.S3.Fourier.TorusOrbitClosure/Reg.D5.S3.Fourier.TorusOrbitClosure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1}
    (fun (_ : Unit) (I : Type (u_1)) (g : I → Circle) (n : ℕ) => g ^ n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.TorusOrbitClosure, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.TorusOrbitClosure, declaration := `D5.S3.Fourier.TorusOrbitClosure.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.observationFact0, `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.anchorEnumeration }


#print axioms registration
end

end Reg.D5.S3.Fourier.TorusOrbitClosure


noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.TorusOrbitClosure.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.TorusOrbitClosure.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Fourier.TorusOrbitClosure.arena.) (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.TorusOrbitClosure, declaration := `D5.S3.Fourier.TorusOrbitClosure.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.observation0.{u_1} : {I : Type u_1} →
  [Fintype.{u_1} I] →
    (g z : I → Circle) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
        Reg.D5.S3.Fourier.TorusOrbitClosure.signature.{u_1} PUnit.unit.{1} I :=
  fun {I : Type u_1} [Fintype.{u_1} I] (g z : I → Circle) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Fourier.TorusOrbitClosure.signature.{u_1} Reg.D5.S3.Fourier.TorusOrbitClosure.actual.{u_1} PUnit.unit.{1}
    I g

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.TorusOrbitClosure, declaration := `D5.S3.Fourier.TorusOrbitClosure.result, part := .type, path := [.body, .body, .body, .body, .function, .argument, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Fourier.TorusOrbitClosure, declaration := `D5.S3.Fourier.TorusOrbitClosure.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).actual (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).variation.2.choose (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).variation.1 (Reg.D5.S3.Fourier.TorusOrbitClosure.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"TorusOrbitClosure\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.TorusOrbitClosure, declaration := `Reg.D5.S3.Fourier.TorusOrbitClosure.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
