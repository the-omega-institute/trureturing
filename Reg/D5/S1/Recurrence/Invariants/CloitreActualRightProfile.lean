import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
import Reg.Support.DependentFamily

open _root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile

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

def actual : Realization signature := realize signature (fun _ _ n => C n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => C n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
    (∀ N : ℕ, 3 ≤ N → R.readout () () N = C (g N) + C (N - g N))

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have he := hr.2 3 (by omega)
  have ha := actual_foundations.2 3 (by omega)
  change C 3 + 1 = C (g 3) + C (3 - g 3) at he
  omega

def registration : Registration arena
    ((∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
      (∀ N : ℕ, 3 ≤ N → C N = C (g N) + C (N - g N))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_foundations, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (4 : ℕ), ?_⟩
    change C 1 ≠ C 4
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => C n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Recurrence") "Invariants") "CloitreActualRightProfile") "actual_foundations") "Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile/Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => C n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalArenaFact, `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.sourceBridgeFact, `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.observationFact0, `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile


noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena
noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena
noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena
    (And
      (∀ (N i : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
          @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
            (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.D N)
            (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.X N i))
      (∀ (N : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
          @Eq.{1} Nat (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C N)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C
                (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.g N))
              (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                  (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.g N))))))
    Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration)

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"actual_foundations\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.arena
  (And
    (∀ (N i : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
        @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
          (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.D N)
          (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.X N i))
    (∀ (N : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
        @Eq.{1} Nat (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C N)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C
              (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.g N))
            (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.C
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                (D5.S1.Recurrence.Invariants.CloitreActualRightProfile.g N))))))
  Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration)

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.observation0 : (N : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (N : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.signature
    Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual PUnit.unit.{1} PUnit.unit.{1} N

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"actual_foundations\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations, part := .type, path := [.argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"actual_foundations\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `D5.S1.Recurrence.Invariants.CloitreActualRightProfile.actual_foundations, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration).actual (Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration).variation.2.choose (Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration).variation.1 (Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Invariants\",\"CloitreActualRightProfile\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile, declaration := `Reg.D5.S1.Recurrence.Invariants.CloitreActualRightProfile.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
