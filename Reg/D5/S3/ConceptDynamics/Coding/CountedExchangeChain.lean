import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedExchangeChain
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.Coding.CountedExchangeChain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain

abbrev signature : Signature where
  Params := ℕ
  State m := CountMat m m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := CountMat m m
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ B => B) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n m : ℕ} {A : CountMat n n} {B : CountMat m m} {L : ℕ}
    (c : ExchangeChain ℕ A B L), Nonempty (WindowConjugacy A (R.readout () m B) L)

theorem actual_law : arena.Law actual := by
  intro n m A B L c
  exact chain_has_window_conjugacy c

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let x : Path A := ⟨fun _ => ⟨0, 0, 0⟩, fun _ => rfl⟩
  obtain ⟨f⟩ := h (ExchangeChain.nil A)
  exact Fin.elim0 ((f.homeomorph x).val 0).number

def registration : Registration arena
    (∀ {n m : ℕ} {A : CountMat n n} {B : CountMat m m} {L : ℕ}
      (c : ExchangeChain ℕ A B L), Nonempty (WindowConjugacy A B L)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (m : ℕ) (x y : CountMat m m), x ≠ y
    refine ⟨1, (fun _ _ => 1), (fun _ _ => 2), ?_⟩
    intro h
    have hentry := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
    exact (by decide : (1 : ℕ) ≠ 2) hentry

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ B => B) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedExchangeChain") "chain_has_window_conjugacy") "Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain/Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ B => B) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.arena) (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"chain_has_window_conjugacy\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.observation0 : {n m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m m} →
      {L : Nat} →
        (c :
            @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring n m A B
              L) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.signature PUnit.unit.{1} m :=
  fun {n m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat m m} {L : Nat}
    (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring n m A B L) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.signature
    Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.actual PUnit.unit.{1} m B

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"chain_has_window_conjugacy\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"chain_has_window_conjugacy\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `D5.S3.ConceptDynamics.Coding.CountedExchangeChain.chain_has_window_conjugacy, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CountedExchangeChain\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CountedExchangeChain.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
