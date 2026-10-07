import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
open LeanInformationAudit
open scoped BigOperators Matrix

noncomputable section
namespace Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable

def signature : Signature where
  Params := ℝ
  State _ := Fin 2 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 2 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Fin 2 → ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (z : ℝ) (p : Fin 2 → ℝ) (_hz : 0 < z) (_hp : ∀ j, 0 < p j),
    (∀ j, 0 < u z (R.readout () z p) j) ∧
      (∀ i j, 0 < K z p i j) ∧
        ∃ lambda1 lambda2 : ℝ,
          0 < lambda1 ∧ lambda1 < q z p ∧ 0 < lambda2 ∧ lambda2 < q z p ∧
            ∃ S : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ,
              IsUnit S.det ∧
                Q z p * S =
                  S * Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0
                    (fun _ _ => q z p)

theorem actual_law : arena.Law actual := by
  intro z p hz hp
  simpa [actual, realize] using
    singular_support_candidate_positive_and_diagonalizable z p hz hp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Fin 2 → ℝ := fun _ => 1
  have hresult := h 1 p (by norm_num) (by intro j; norm_num [p])
  have hzero := hresult.1 0
  norm_num [rejected, realize, u, q, K, gZero, H, r, Matrix.mulVec, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_two] at hzero

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, funext fun e => Empty.elim e, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(1 : ℝ), (0 : Fin 2 → ℝ), (fun _ => 1), ?_⟩
  intro h
  have hentry := congrFun h 0
  norm_num [actual, realize] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "QuantumContext") "SingularSupportCandidateDiagonalizable") "singular_support_candidate_positive_and_diagonalizable") "Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable/Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ p => p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalArenaFact, `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.sourceBridgeFact, `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.observationFact0, `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable


noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
      Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.actual)
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration)

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"singular_support_candidate_positive_and_diagonalizable\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.arena
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.actual)
  Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration)

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.observation0 : (z : Real) →
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real) →
    (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z) →
      (hp :
          ∀ (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (p j)) →
        (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.signature PUnit.unit.{1} z :=
  fun (z : Real) (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
    (hp :
      ∀ (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (p j))
    (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.signature
    Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.actual PUnit.unit.{1} z p

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"singular_support_candidate_positive_and_diagonalizable\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable, part := .type, path := [.body, .body, .body, .body, .function, .argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"singular_support_candidate_positive_and_diagonalizable\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.singular_support_candidate_positive_and_diagonalizable, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration).actual (Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration).variation.2.choose (Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration).variation.1 (Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"QuantumContext\",\"SingularSupportCandidateDiagonalizable\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable, declaration := `Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
