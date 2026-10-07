import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.OeisA398589EventualPeriodicity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity

namespace Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity

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
  realize signature (fun _ k t => row k t) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ k : ℕ, ∃ N p : ℕ, 0 < p ∧
    ∀ t : ℕ, N ≤ t → r.readout () k (t + p) = r.readout () k t

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, p, hp, ht⟩ := h 0
  have heq := ht N le_rfl
  change N + p = N at heq
  omega

noncomputable def registration : Registration arena
    (∀ k : ℕ, ∃ N p : ℕ, 0 < p ∧
      ∀ t : ℕ, N ≤ t → row k (t + p) = row k t) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventual_periodicity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change row 1 0 ≠ row 1 1
    have hz : row 1 0 = 1 := by
      unfold row
      rw [Nat.strongRec_eq]
      simp [rowStep]
    intro heq
    have he : row 1 1 = 1 := heq.symm.trans hz
    have hstep : row 1 1 = rowStep 1 1 (fun m _ => row 1 m) := by
      unfold row
      rw [Nat.strongRec_eq]
    rw [hstep] at he
    unfold rowStep at he
    rw [dif_neg (by decide : ¬ (1 : ℕ) = 0)] at he
    generalize_proofs h at he
    have hbad := (Nat.find_spec h).2 0 (by decide) (by
      simpa [hz] using he.symm)
    rw [he] at hbad
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ k t => row k t) (fun a => nomatch a))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "OeisA398589EventualPeriodicity") "eventual_periodicity") "Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity/Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ k t => row k t) (fun a => nomatch a)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg", "body", "arg", "body", "arg", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.anchorEnumeration }


#print axioms _root_.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity
#print axioms registration
end Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity


noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena
noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena
noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena
    (∀ (k : Nat),
      @Exists.{1} Nat fun (N : Nat) =>
        @Exists.{1} Nat fun (p : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
            (∀ (t : Nat),
              @LE.le.{0} Nat instLENat N t →
                @Eq.{1} Nat
                  (D5.S3.Combinatorics.OeisA398589EventualPeriodicity.row k
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t p))
                  (D5.S3.Combinatorics.OeisA398589EventualPeriodicity.row k t)))
    Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration)

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"eventual_periodicity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.arena
  (∀ (k : Nat),
    @Exists.{1} Nat fun (N : Nat) =>
      @Exists.{1} Nat fun (p : Nat) =>
        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
          (∀ (t : Nat),
            @LE.le.{0} Nat instLENat N t →
              @Eq.{1} Nat
                (D5.S3.Combinatorics.OeisA398589EventualPeriodicity.row k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t p))
                (D5.S3.Combinatorics.OeisA398589EventualPeriodicity.row k t)))
  Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration)

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.observation0 : (k N p t : Nat) →
  @LE.le.{0} Nat instLENat N t →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
        Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.signature k →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.signature PUnit.unit.{1} k :=
  fun (k N p t : Nat) (a : @LE.le.{0} Nat instLENat N t) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.signature
    Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.actual PUnit.unit.{1} k

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"eventual_periodicity\"],\"part\":\"type\",\"path\":[\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"body\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity, part := .type, path := [.body, .argument, .body, .argument, .body, .argument, .body, .body, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"eventual_periodicity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `D5.S3.Combinatorics.OeisA398589EventualPeriodicity.eventual_periodicity, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration).actual (Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration).variation.2.choose (Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration).variation.1 (Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"OeisA398589EventualPeriodicity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity, declaration := `Reg.D5.S3.Combinatorics.OeisA398589EventualPeriodicity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
