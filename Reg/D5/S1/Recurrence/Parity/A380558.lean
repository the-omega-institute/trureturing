import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.A380558
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.Parity.A380558

open PowerSeries
open _root_.D5.S1.Recurrence.Parity.A380558
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n generatingSeries) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r :=
    constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 0 ∧
    generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 ∧
    (∀ F : PowerSeries ℤ, constantCoeff F = 0 → coeff 1 F = 0 →
      F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1 →
      F = generatingSeries) ∧
    ∀ n : ℕ, Odd (r.readout () () n) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h2 := (h.2.2.2.2 2).2 (Or.inl rfl)
  change Odd (0 : ℤ) at h2
  norm_num at h2

def registration : Registration arena
    (constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 0 ∧
    generatingSeries.subst (X - generatingSeries) =
      X ^ 2 * invOfUnit (1 - X ^ 2) 1 ∧
    (∀ F : PowerSeries ℤ, constantCoeff F = 0 → coeff 1 F = 0 →
      F.subst (X - F) = X ^ 2 * invOfUnit (1 - X ^ 2) 1 →
      F = generatingSeries) ∧
    ∀ n : ℕ, Odd (coeff n generatingSeries) ↔ n = 2 ∨
      ∃ m j : ℕ, n = 2 * m ∧ 3 * 2 ^ j ≤ m ∧ m < 4 * 2 ^ j) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i
      cases j
      exact False.elim (h rfl)
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (2 : ℕ), ?_⟩
    change coeff 0 generatingSeries ≠ coeff 2 generatingSeries
    intro h
    have h0 : coeff 0 generatingSeries = 0 := by
      simpa only [coeff_zero_eq_constantCoeff] using result.1
    have hodd : Odd (coeff 2 generatingSeries) := (result.2.2.2.2 2).2 (Or.inl rfl)
    rw [h0] at h
    rw [← h] at hodd
    norm_num at hodd

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.Parity.A380558.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => coeff.{0} n generatingSeries) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "Parity") "A380558") "result") "Reg.D5.S1.Recurrence.Parity.A380558/Reg.D5.S1.Recurrence.Parity.A380558.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.Parity.A380558.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => coeff.{0} n generatingSeries) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.Parity.A380558, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "arg", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Recurrence.Parity.A380558, declaration := `D5.S1.Recurrence.Parity.A380558.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalArenaFact, `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.sourceBridgeFact, `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.observationFact0, `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S1.Recurrence.Parity.A380558


noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.Parity.A380558.arena
noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.Parity.A380558.arena
noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Recurrence.Parity.A380558.arena) (Reg.D5.S1.Recurrence.Parity.A380558.registration).actual

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.Parity.A380558, declaration := `D5.S1.Recurrence.Parity.A380558.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Recurrence.Parity.A380558.registration).bridge

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.observation0 : (n : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.Parity.A380558.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.Parity.A380558.signature Reg.D5.S1.Recurrence.Parity.A380558.actual PUnit.unit.{1}
    PUnit.unit.{1} n

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.Parity.A380558, declaration := `D5.S1.Recurrence.Parity.A380558.result, part := .type, path := [.argument, .argument, .argument, .argument, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Recurrence.Parity.A380558.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Recurrence.Parity.A380558, declaration := `D5.S1.Recurrence.Parity.A380558.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Recurrence.Parity.A380558.registration).actual (Reg.D5.S1.Recurrence.Parity.A380558.registration).variation.2.choose (Reg.D5.S1.Recurrence.Parity.A380558.registration).variation.1 (Reg.D5.S1.Recurrence.Parity.A380558.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Recurrence.Parity.A380558.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Parity\",\"A380558\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Parity.A380558, declaration := `Reg.D5.S1.Recurrence.Parity.A380558.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
