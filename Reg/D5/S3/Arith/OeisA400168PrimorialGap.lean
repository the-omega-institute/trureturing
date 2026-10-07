import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.OeisA400168PrimorialGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.OeisA400168PrimorialGap
open _root_.D5.S3.Arith.OeisA400168PrimorialGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

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
  realize signature (fun _ _ n => L (D n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original negation and domain, varying only the derivative-length reading. -/
abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ n : ℕ, 1 ≤ n → R.readout () () n ≤ M n + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n _
  exact Nat.zero_le _

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  have hD0 : D 0 = 0 := by simp [D]
  have hD2 : D 2 = 1 := by simp [D, Nat.prime_two.factorization]
  have hL0 : L 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' _ (by change 0 < P 0; decide)
  have hL1 : L 1 = 1 := by
    apply le_antisymm
    · exact Nat.find_min' _ (by change 1 < P 1; simp [P])
    · apply Nat.le_of_not_gt
      intro h
      have hz : L 1 = 0 := by omega
      have hspec : 1 < P (L 1) := by unfold L; exact Nat.find_spec (p := fun k => 1 < P k) _
      rw [hz] at hspec
      exact (by decide : ¬ (1 < P 0)) hspec
  change L (D 0) ≠ L (D 2)
  rw [hD0, hD2, hL0, hL1]
  decide

def registration : Registration arena (Not claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.OeisA400168PrimorialGap.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => L (D n)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "OeisA400168PrimorialGap") "result") "Reg.D5.S3.Arith.OeisA400168PrimorialGap/Reg.D5.S3.Arith.OeisA400168PrimorialGap.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => L (D n)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.OeisA400168PrimorialGap, definition := some { owner := `D5.S3.Arith.OeisA400168PrimorialGap, name := `D5.S3.Arith.OeisA400168PrimorialGap.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.OeisA400168PrimorialGap, declaration := `D5.S3.Arith.OeisA400168PrimorialGap.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Arith.OeisA400168PrimorialGap, declaration := `D5.S3.Arith.OeisA400168PrimorialGap.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.observationFact0, `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.OeisA400168PrimorialGap


noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.OeisA400168PrimorialGap.arena
noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.OeisA400168PrimorialGap.arena
noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.OeisA400168PrimorialGap.arena) (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).actual

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.OeisA400168PrimorialGap, declaration := `D5.S3.Arith.OeisA400168PrimorialGap.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).bridge

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.observation0 : (n : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.OeisA400168PrimorialGap.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.OeisA400168PrimorialGap.signature Reg.D5.S3.Arith.OeisA400168PrimorialGap.actual PUnit.unit.{1}
    PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.OeisA400168PrimorialGap, declaration := `D5.S3.Arith.OeisA400168PrimorialGap.claim, part := .value, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.OeisA400168PrimorialGap, declaration := `D5.S3.Arith.OeisA400168PrimorialGap.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).actual (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).variation.2.choose (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).variation.1 (Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"OeisA400168PrimorialGap\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.OeisA400168PrimorialGap, declaration := `Reg.D5.S3.Arith.OeisA400168PrimorialGap.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
