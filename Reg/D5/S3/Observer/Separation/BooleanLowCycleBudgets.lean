import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Separation.BooleanLowCycleBudgets
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets

open _root_.D5.S3.Observer.Separation.BooleanLowCycleBudgets
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The observed operand is the original class-wide total-budget threshold.
The law retains the original task quantifiers and all three hypotheses. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s + 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (s p q : ℕ) (_hs : s ≤ 2) (_hp : 0 < p) (_hq : 0 < q),
    UniformBudget s p q ↔ 2 ≤ p ∧ 2 ≤ q ∧ R.readout () () s ≤ p + q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : UniformBudget 1 2 2 :=
    (h 1 2 2 (by decide) (by decide) (by decide)).mpr
      ⟨le_rfl, le_rfl, by decide⟩
  have hn := (result 1 2 2 (by decide) (by decide) (by decide)).mp hb
  omega

def registration : Registration arena
    (∀ (s p q : ℕ) (_hs : s ≤ 2) (_hp : 0 < p) (_hq : 0 < q),
      UniformBudget s p q ↔ 2 ≤ p ∧ 2 ≤ q ∧ s + 4 ≤ p + q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    exact (by decide : (0 : ℕ) + 4 ≠ 1 + 4)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Separation.BooleanLowCycleBudgets.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s + 4) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Separation") "BooleanLowCycleBudgets") "result") "Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets/Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s + 4) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `D5.S3.Observer.Separation.BooleanLowCycleBudgets.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.observationFact0, `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets


noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena
noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena
    (∀ (s p q : Nat) (_hs : @LE.le.{0} Nat instLENat s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (_hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
      (_hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
      Iff (D5.S3.Observer.Separation.BooleanLowCycleBudgets.UniformBudget s p q)
        (And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p)
          (And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p q)))))
    Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `D5.S3.Observer.Separation.BooleanLowCycleBudgets.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.arena
  (∀ (s p q : Nat) (_hs : @LE.le.{0} Nat instLENat s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (_hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
    (_hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
    Iff (D5.S3.Observer.Separation.BooleanLowCycleBudgets.UniformBudget s p q)
      (And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p)
        (And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p q)))))
  Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration)

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.observation0 : (s p q : Nat) →
  (hs : @LE.le.{0} Nat instLENat s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
    (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
      (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (s p q : Nat) (hs : @LE.le.{0} Nat instLENat s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
    (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.signature
    Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.actual PUnit.unit.{1} PUnit.unit.{1} s

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `D5.S3.Observer.Separation.BooleanLowCycleBudgets.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `D5.S3.Observer.Separation.BooleanLowCycleBudgets.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration).actual (Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration).variation.2.choose (Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration).variation.1 (Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Separation\",\"BooleanLowCycleBudgets\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets, declaration := `Reg.D5.S3.Observer.Separation.BooleanLowCycleBudgets.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
