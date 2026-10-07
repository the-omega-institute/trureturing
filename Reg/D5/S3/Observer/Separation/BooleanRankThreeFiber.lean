import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanRankThreeFiber
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
open _root_.D5.S3.Observer.Separation.BooleanRankThreeFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Task (Fin 8) (Fin 6)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => rank T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (T : Task X Y), Admissible T →
      ((∃ c d, Balanced T (residual T c d)) → HasBudget T 3 3) ∧
      ((∀ c d, ¬ Balanced T (residual T c d)) →
        3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T)) ∧
      (¬ HasBudget T 3 3 → 3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T))) ∧
    (∃ T : Task (Fin 8) (Fin 6), Admissible T ∧ R.readout () () T = 3 ∧
      (∀ c d, ¬ Balanced T (residual T c d)) ∧ RankThreeShape T ∧ HasBudget T 3 3)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, T, _, h, _⟩
  change (0 : ℤ) = 3 at h
  norm_num at h

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨(), ⟨fun _ _ => none⟩, ⟨fun _ _ => some 0⟩, ?_⟩
    change rank (Task.mk (fun (_ : Fin 8) (_ : Fin 6) => none)) ≠
      rank (Task.mk (fun (_ : Fin 8) (_ : Fin 6) => some 0))
    simp only [rank, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Separation.BooleanRankThreeFiber.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ T => rank T) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanRankThreeFiber") "result") "Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber/Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ T => rank T) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `D5.S3.Observer.Separation.BooleanRankThreeFiber.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.observationFact0, `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.anchorEnumeration }


#print axioms registration
#print axioms result

end
end Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
      Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.actual)
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `D5.S3.Observer.Separation.BooleanRankThreeFiber.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.arena
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.actual)
  Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.observation0 : (T :
    D5.S3.Observer.Separation.BooleanRankThreeFiber.Task
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun
    (T :
      D5.S3.Observer.Separation.BooleanRankThreeFiber.Task
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.signature
    Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.actual PUnit.unit.{1} PUnit.unit.{1} T

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `D5.S3.Observer.Separation.BooleanRankThreeFiber.result, part := .type, path := [.argument, .argument, .body, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `D5.S3.Observer.Separation.BooleanRankThreeFiber.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration).actual (Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration).variation.2.choose (Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration).variation.1 (Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanRankThreeFiber\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber, declaration := `Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
