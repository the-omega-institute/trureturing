import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift
open LeanInformationAudit
open Lean Meta

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ → ℤ → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ → ℤ → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (_hM : 3 ≤ M) (_hN : 3 ≤ N) (y : EdgeLabel M N) (_hy : Flat y)
      (a : ZMod 2),
    ∃! x : ℤ → ℤ → ZMod 2, IsCoverLift y a (R.readout () () x)

theorem actual_law : arena.Law actual := by
  intro M N _ _ hM hN y hy a
  simpa [actual, realize, signature] using flat_unique_cover_lift hM hN y hy a

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  let y : EdgeLabel 3 3 := seam 0 0
  have hy : Flat y := seam_flat 0 0
  obtain ⟨x, hx, _⟩ := hr (by omega : 3 ≤ 3) (by omega : 3 ≤ 3) y hy 1
  have h := hx.1
  change (0 : ZMod 2) = 1 at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro he
  have h := congrArg (fun f : ℤ → ℤ → ZMod 2 => f 0 0) he
  change (0 : ZMod 2) = 1 at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

def registration : Registration arena
    (∀ {M N : ℕ} [NeZero M] [NeZero N]
      (_hM : 3 ≤ M) (_hN : 3 ≤ N) (y : EdgeLabel M N) (_hy : Flat y)
      (a : ZMod 2), ∃! x : ℤ → ℤ → ZMod 2, IsCoverLift y a x) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "PeriodicGridCoverLift") "flat_unique_cover_lift") "Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift/Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.arena
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.arena) (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"flat_unique_cover_lift\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.observation0 : {M N : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] →
    [inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
      (_hM : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) M) →
        (_hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N) →
          (y : D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N) →
            (hy : @D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.Flat M N inst inst_1 y) →
              (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                (x : Int → Int → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {M N : Nat} [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
    [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N]
    (_hM : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) M)
    (_hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N)
    (y : D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.EdgeLabel M N)
    (hy : @D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.Flat M N inst inst_1 y)
    (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (x : Int → Int → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.signature
    Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.actual PUnit.unit.{1} PUnit.unit.{1} x

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"flat_unique_cover_lift\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"flat_unique_cover_lift\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.flat_unique_cover_lift, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).actual (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"PeriodicGridCoverLift\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift, declaration := `Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridCoverLift.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
