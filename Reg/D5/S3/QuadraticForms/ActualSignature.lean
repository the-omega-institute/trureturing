import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.ActualSignature
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ActualSignature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.ActualSignature

noncomputable section

def signatureFamily : Signature where
  Params := ℕ
  State := fun n => Mat ℝ n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signatureFamily := realize signatureFamily
  (fun (_ : Unit) (n : ℕ) (A : Mat ℝ n) => signature A.toQuadraticForm') (fun e => nomatch e)

def rejected : Realization signatureFamily := realize signatureFamily
  (fun (_ : Unit) (n : ℕ) (_ : Mat ℝ n) => (1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signatureFamily
  Law R := ∀ (n : ℕ) (A : Mat ℝ n) (_hs : ∀ r s, A r s = A s r) (z : ℤ),
    Realizes n A z ↔ R.readout () n A = z

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨realizes_iff_signature, rejected, ?_⟩
    intro h
    have hh := (h 0 0 (by simp) 0).mp rfl
    change (1 : ℤ) = 0 at hh
    exact one_ne_zero hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hh := (h 0 0 (by simp) 0).mp rfl
        change (1 : ℤ) = 0 at hh
        exact one_ne_zero hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : Mat ℝ 1), (1 : Mat ℝ 1), ?_⟩
    have hz : signature (0 : Mat ℝ 1).toQuadraticForm' = 0 :=
      (realizes_iff_signature 1 0 (by simp) 0).mp (by
        exact Or.inl ⟨by simp, rfl⟩)
    have ho : signature (1 : Mat ℝ 1).toQuadraticForm' = 1 :=
      (realizes_iff_signature 1 1 (by intro r s; simp [Matrix.one_apply, eq_comm]) 1).mp (by
        refine Or.inr (Or.inl ⟨0, Or.inl ⟨by norm_num, ?_⟩⟩)
        norm_num [Realizes])
    change signature (0 : Mat ℝ 1).toQuadraticForm' ≠
      signature (1 : Mat ℝ 1).toQuadraticForm'
    rw [hz, ho]
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature) (type_of% (realize.{0, 0, 0, 0, 0} signatureFamily
    (fun (_ : Unit) (n : ℕ) (A : Mat.{0} ℝ n) => signature.{0} A.toQuadraticForm') (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "QuadraticForms") "ActualSignature") "realizes_iff_signature") "Reg.D5.S3.QuadraticForms.ActualSignature/Reg.D5.S3.QuadraticForms.ActualSignature.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.QuadraticForms.ActualSignature.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signatureFamily
    (fun (_ : Unit) (n : ℕ) (A : Mat.{0} ℝ n) => signature.{0} A.toQuadraticForm') (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.QuadraticForms.ActualSignature, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.QuadraticForms.ActualSignature, declaration := `D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalArenaFact, `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.sourceBridgeFact, `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.observationFact0, `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.anchorEnumeration }


end
end Reg.D5.S3.QuadraticForms.ActualSignature


noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuadraticForms.ActualSignature.arena
noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuadraticForms.ActualSignature.arena
noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.QuadraticForms.ActualSignature.arena) (Reg.D5.S3.QuadraticForms.ActualSignature.registration).actual

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"realizes_iff_signature\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuadraticForms.ActualSignature, declaration := `D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.QuadraticForms.ActualSignature.registration).bridge

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.observation0 : (n : Nat) →
  (A : D5.S3.QuadraticForms.ActualSignature.Mat.{0} Real n) →
    (hs : ∀ (r s : Fin n), @Eq.{1} Real (A r s) (A s r)) →
      (z : Int) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.QuadraticForms.ActualSignature.signatureFamily PUnit.unit.{1} n :=
  fun (n : Nat) (A : D5.S3.QuadraticForms.ActualSignature.Mat.{0} Real n)
    (hs : ∀ (r s : Fin n), @Eq.{1} Real (A r s) (A s r)) (z : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuadraticForms.ActualSignature.signatureFamily Reg.D5.S3.QuadraticForms.ActualSignature.actual
    PUnit.unit.{1} n A

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"realizes_iff_signature\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuadraticForms.ActualSignature, declaration := `D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature, part := .type, path := [.body, .body, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"realizes_iff_signature\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.QuadraticForms.ActualSignature, declaration := `D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.QuadraticForms.ActualSignature.registration).actual (Reg.D5.S3.QuadraticForms.ActualSignature.registration).variation.2.choose (Reg.D5.S3.QuadraticForms.ActualSignature.registration).variation.1 (Reg.D5.S3.QuadraticForms.ActualSignature.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.QuadraticForms.ActualSignature.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuadraticForms\",\"ActualSignature\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuadraticForms.ActualSignature, declaration := `Reg.D5.S3.QuadraticForms.ActualSignature.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
