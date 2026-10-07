import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SolidPartitionFirstColumn
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn
open _root_.D5.S3.Combinatorics.SolidPartitionFirstColumn

/-- Dimension is unrestricted (including zero); the positive-dimension and size
guards belong to the complete Law, not to a restricted signature. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ d n => tau d n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = r.readout () d n ∧
    shrinkColumn d n = tau d (n + 1)

theorem tau_one (d : ℕ) : tau d 1 = 1 := by
  have singleton : {v : Fin d → ℕ | ∏ i, v i = 1} = {fun _ => 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.prod_eq_one_iff,
      Finset.mem_univ, forall_const, funext_iff]
  rw [tau, singleton, Set.ncard_singleton]

theorem tau_two_two_ne_one : tau 2 2 ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h
  let a : Fin 2 → ℕ := fun i => if i = 0 then 2 else 1
  let b : Fin 2 → ℕ := fun i => if i = 1 then 2 else 1
  have ha : a ∈ {v : Fin 2 → ℕ | ∏ i, v i = 2} := by decide
  have hb : b ∈ {v : Fin 2 → ℕ | ∏ i, v i = 2} := by decide
  rw [hv, Set.mem_singleton_iff] at ha hb
  have e := congrFun (ha.trans hb.symm) 0
  change 2 = 1 at e
  contradiction

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have original :=
    (_root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result 2 1 (by decide) (by decide)).1
  rw [tau_one] at original
  have zero := (h 2 1 (by decide) (by decide)).1
  change firstColumn 2 1 = 0 at zero
  omega

/-- One permitted fiber witnesses dependence; the Law still quantifies over every dimension. -/
theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨2, 1, 2, ?_⟩
  change tau 2 1 ≠ tau 2 2
  rw [tau_one]
  exact Ne.symm tau_two_two_ne_one

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.SolidPartitionFirstColumn.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ d n => tau d n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "SolidPartitionFirstColumn") "result") "Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn/Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ d n => tau d n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, definition := some { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, name := `D5.S3.Combinatorics.SolidPartitionFirstColumn.claim, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `D5.S3.Combinatorics.SolidPartitionFirstColumn.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `D5.S3.Combinatorics.SolidPartitionFirstColumn.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn


noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.arena
noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.arena
noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.arena) (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).actual

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `D5.S3.Combinatorics.SolidPartitionFirstColumn.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).bridge

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.observation0 : (d n : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.signature PUnit.unit.{1} d :=
  fun (d n : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
    (a_1 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.signature Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.actual
    PUnit.unit.{1} d n

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `D5.S3.Combinatorics.SolidPartitionFirstColumn.claim, part := .value, path := [.body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `D5.S3.Combinatorics.SolidPartitionFirstColumn.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).actual (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).variation.2.choose (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).variation.1 (Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"SolidPartitionFirstColumn\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn, declaration := `Reg.D5.S3.Combinatorics.SolidPartitionFirstColumn.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
