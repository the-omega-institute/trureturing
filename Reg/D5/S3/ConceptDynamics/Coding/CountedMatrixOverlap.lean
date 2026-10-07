import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Reg.Support.DependentFamily
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basis

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

abbrev joinSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ U : CountMat n m, CountMat m n
  State p := Edge (p.2.2.1 * p.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge (p.2.2.1 * p.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def reverseEdge {n m : Nat} {M : CountMat n m} (a : Edge M) : Edge M :=
  ⟨a.source, a.target, Fin.rev a.number⟩

def joinActual : Realization joinSignature :=
  realize joinSignature (fun _ _ a => a) (fun e => nomatch e)

def joinRejected : Realization joinSignature :=
  realize joinSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def joinArena : Arena where
  signature := joinSignature
  Law r := ∀ {n m : Nat} (U : CountMat n m) (V : CountMat m n)
    (a : Edge (U * V)),
    join U V (split U V a).1 (split U V a).2 (by rfl) =
      r.readout () ⟨n, m, U, V⟩ a

theorem join_rejected_law : ¬ joinArena.Law joinRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hUV : (U * V) 0 0 = 2 := by
    change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
    simp
  let a : Edge (U * V) :=
    ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
  have hh := h U V a
  rw [join_split] at hh
  have hn := congrArg (fun e : Edge (U * V) => e.number.val) hh
  simp [joinRejected, realize, reverseEdge, U, V, a] at hn

def joinRegistration : Registration joinArena (joinArena.Law joinActual) where
  actual := joinActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m U V a
    simpa [joinActual, realize] using join_split U V a,
    joinRejected, join_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨joinRejected, ?_, rfl, join_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    let V : CountMat 1 1 := fun _ _ => 1
    have hUV : (U * V) 0 0 = 2 := by
      change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
      simp
    let a : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
    let b : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (1 : Fin 2)⟩
    change ∃ p : joinSignature.Params, ∃ x y : joinSignature.State p, x ≠ y
    exact ⟨⟨1, 1, U, V⟩, a, b, by simp [a, b]⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split) (type_of% (realize.{0, 0, 0, 0, 0} joinSignature (fun _ _ a => a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedMatrixOverlap") "join_split") "Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap/Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(joinArena)⟩,
  objectArena := .source ⟨(joinArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (joinArena) ⟨(joinRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} joinSignature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.anchorEnumeration }


abbrev splitSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, CountMat n m
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def splitActual : Realization splitSignature :=
  realize splitSignature (fun _ _ a => a) (fun e => nomatch e)

def splitRejected : Realization splitSignature :=
  realize splitSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def splitArena : Arena where
  signature := splitSignature
  Law r := ∀ {n m : Nat} (U : CountMat n m) (V : CountMat m n)
    (a : Edge U) (b : Edge V) (h : a.target = b.source),
    split U V (join U V a b h) =
      (r.readout () ⟨n, m, U⟩ a, b)

theorem split_rejected_law : ¬ splitArena.Law splitRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hU : U 0 0 = 2 := by rfl
  let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
  let b : Edge V := ⟨0, 0, 0⟩
  have hh := h U V a b rfl
  rw [split_join] at hh
  have hfirst := congrArg (fun p : Edge U × Edge V => p.1) hh
  have hn := congrArg (fun e : Edge U => e.number.val) hfirst
  simp [splitRejected, realize, reverseEdge, U, V, a, b] at hn

def splitRegistration : Registration splitArena (splitArena.Law splitActual) where
  actual := splitActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m U V a b h
    simpa [splitActual, realize] using split_join U V a b h,
    splitRejected, split_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨splitRejected, ?_, rfl, split_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    have hU : U 0 0 = 2 := by rfl
    let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
    let b : Edge U := ⟨0, 0, hU.symm ▸ (1 : Fin 2)⟩
    change ∃ p : splitSignature.Params, ∃ x y : splitSignature.State p, x ≠ y
    refine ⟨⟨1, 1, U⟩, a, b, ?_⟩
    intro h
    have hn := congrArg (fun e : Edge U => e.number.val) h
    exact Nat.zero_ne_one hn

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join) (type_of% (realize.{0, 0, 0, 0, 0} splitSignature (fun _ _ a => a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedMatrixOverlap") "split_join") "Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap/Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(splitArena)⟩,
  objectArena := .source ⟨(splitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (splitArena) ⟨(splitRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} splitSignature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.anchorEnumeration }


#print axioms joinRegistration
#print axioms splitRegistration

end Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitArena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitArena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinArena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinArena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitArena) (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"split_join\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.observation0 : {n m : Nat} →
  (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) →
    (V : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n) →
      (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n m U) →
        (b : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge m n V) →
          (h :
              @Eq.{1} (Fin m) (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n m U a)
                (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.source m n V b)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitSignature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat
                (fun (n : Nat) =>
                  @Sigma.{0, 0} Nat fun (m : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
                n
                (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
                  m U)) :=
  fun {n m : Nat} (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
    (V : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
    (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n m U)
    (b : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge m n V)
    (h :
      @Eq.{1} (Fin m) (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n m U a)
        (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.source m n V b)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitSignature
    Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (m : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
      n (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) m U))
    a

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"split_join\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"split_join\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).actual (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"splitRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinArena) (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"join_split\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.observation0 : {n m : Nat} →
  (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) →
    (V : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n) →
      (a :
          @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n
            (@HMul.hMul.{0, 0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
              (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n) (Matrix.{0, 0, 0} (Fin n) (Fin n) Nat)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin m) (Fin n) Nat (Fin.fintype m)
                instMulNat Nat.instAddCommMonoid)
              U V)) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinSignature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat
            (fun (n : Nat) =>
              @Sigma.{0, 0} Nat fun (m : Nat) =>
                @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
                  fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
                  D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
            n
            (@Sigma.mk.{0, 0} Nat
              (fun (m : Nat) =>
                @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
                  fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
                  D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
              m
              (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
                (fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
                  D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
                U V))) :=
  fun {n m : Nat} (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
    (V : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
    (a :
      @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n
        (@HMul.hMul.{0, 0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
          (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n) (Matrix.{0, 0, 0} (Fin n) (Fin n) Nat)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin n) (Fin m) (Fin n) Nat (Fin.fintype m)
            instMulNat Nat.instAddCommMonoid)
          U V)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinSignature
    Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (m : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
            fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
            D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
      n
      (@Sigma.mk.{0, 0} Nat
        (fun (m : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
            fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
            D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
        m
        (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m)
          (fun (U : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n m) =>
            D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m n)
          U V)))
    a

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"join_split\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split, part := .type, path := [.body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"join_split\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).actual (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedMatrixOverlap\",\"joinRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
