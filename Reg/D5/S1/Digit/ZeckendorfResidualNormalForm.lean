import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfResidualNormalForm
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfResidualNormalForm
open D5.S1.Digit.ZeckendorfContextualReplacement

namespace Reg.D5.S1.Digit.ZeckendorfResidualNormalForm
noncomputable section
open Classical

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ H w => _root_.D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib H) w)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H, 14 ≤ H → ∀ w : List (Fin 2), NoAdjacentOnes w →
    ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
      R.readout () H w = R.readout () H v ∧ ¬ B1 <:+: v.drop 7

def rejected : Realization signature := realize signature
  (fun _ _ w _ => some (decide (w.length = 0))) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v,hv,hl,he⟩ := h 14 le_rfl [] (by simp [NoAdjacentOnes])
  have ee := congrFun he.1 []
  have hvne : v ≠ [] := by intro h; subst v; simp at hl
  simp [rejected,realize,hvne] at ee

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_state_cover,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨0,[],[1],?_⟩
    intro he
    have ee := congrFun he []
    have h0 : D5.S0.Conventions.wdigits 0 = [] := by simp [D5.S0.Conventions.wdigits]
    have h1 : D5.S0.Conventions.wdigits 1 = [2] := by
      symm
      apply D5.S0.Conventions.wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    simpa [actual,realize,_root_.D5.S1.Digit.ZeckendorfRawWindow.residual,NoAdjacentOnes,value,
      D5.S1.Digit.GoldenBase4IntervalMachine.fibPair,parity,h0,h1] using ee

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S1.Digit.ZeckendorfResidualNormalForm
  coordinates := #[0]
  readouts := #[{path := #["body","body","body","body","arg","body",
      "arg","arg","fn","arg","fn","arg"], stateOperand := some #["arg"]}] }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfResidualNormalForm.normalized_state_cover) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ H w => _root_.D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib H) w)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfResidualNormalForm") "normalized_state_cover") "Reg.D5.S1.Digit.ZeckendorfResidualNormalForm/Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ H w => _root_.D5.S1.Digit.ZeckendorfRawWindow.residual (Nat.fib H) w)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfResidualNormalForm, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `D5.S1.Digit.ZeckendorfResidualNormalForm.normalized_state_cover, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.observationFact0, `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Digit.ZeckendorfResidualNormalForm


noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena
noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.actual)
    Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration)

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"normalized_state_cover\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `D5.S1.Digit.ZeckendorfResidualNormalForm.normalized_state_cover, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.arena Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.actual)
  Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration)

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.observation0 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) H) →
    (w : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w) →
        (v : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.signature PUnit.unit.{1} H :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) H)
    (w : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w)
    (v : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.signature Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.actual
    PUnit.unit.{1} H w

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"normalized_state_cover\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `D5.S1.Digit.ZeckendorfResidualNormalForm.normalized_state_cover, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"normalized_state_cover\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `D5.S1.Digit.ZeckendorfResidualNormalForm.normalized_state_cover, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration).actual (Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration).variation.1 (Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfResidualNormalForm\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm, declaration := `Reg.D5.S1.Digit.ZeckendorfResidualNormalForm.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
