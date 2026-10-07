import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FibreCountAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount

theorem dependence : ObservationalDependence EvenFibre.signature EvenFibre.actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenFibre.actual, EvenFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 0) (n := 2) (word := [])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl []), rfl⟩)
    (by decide)

theorem rejected_law : ¬ FibreCount.arena.Law EvenFibre.rejected := by
  intro h
  have h := @h 2 (by decide)
  have h := h.1
  change (0 : ℕ) = 1 at h
  cases h

def registration : Registration FibreCount.arena (∀ (m : ℕ) (hm : 2 ≤ m),
    (fibre (2 * m)).length = 1 ∧ (fibre (2 * m + 1)).length = m + 1) where
  actual := EvenFibre.actual
  bridge := Iff.rfl
  variation := ⟨@zhan_bie_conjectures_3_4, EvenFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4) (type_of% (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Patterns") "CyclicStackPreimages") "zhan_bie_conjectures_3_4") "Reg.D5.S1.Words.Patterns.CyclicStackPreimages/D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(FibreCount.arena)⟩,
  objectArena := .source ⟨(FibreCount.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (FibreCount.arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.observationFact0, `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.anchorEnumeration }


end FibreCountAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimages


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena
    (∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m),
      And
        (@Eq.{1} Nat
          (@List.length.{0} (List.{0} Nat)
            (D5.S1.Words.Patterns.CyclicStackPreimages.fibre
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat
          (@List.length.{0} (List.{0} Nat)
            (D5.S1.Words.Patterns.CyclicStackPreimages.fibre
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"zhan_bie_conjectures_3_4\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount.arena
  (∀ (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m),
    And
      (@Eq.{1} Nat
        (@List.length.{0} (List.{0} Nat)
          (D5.S1.Words.Patterns.CyclicStackPreimages.fibre
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Nat
        (@List.length.{0} (List.{0} Nat)
          (D5.S1.Words.Patterns.CyclicStackPreimages.fibre
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration)

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.observation0 : (m : Nat) →
  (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.signature
    D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenFibre.actual PUnit.unit.{1} PUnit.unit.{1} m

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"zhan_bie_conjectures_3_4\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4, part := .type, path := [.body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"zhan_bie_conjectures_3_4\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `D5.S1.Words.Patterns.CyclicStackPreimages.zhan_bie_conjectures_3_4, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration).actual (Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration).variation.2.choose (Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration).variation.1 (Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Patterns\",\"CyclicStackPreimages\",\"FibreCountAudit\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages, declaration := `Reg.D5.S1.Words.Patterns.CyclicStackPreimages.FibreCountAudit.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
