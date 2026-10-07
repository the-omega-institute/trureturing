import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.Billiards.CollidingBlocksRecords
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

open LeanInformationAudit Real
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords
open _root_.D5.S3.Constants.Billiards.CollidingBlocksRecords

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
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    r.readout () () n ≠ ⌊π * √(n : ℝ)⌋ →
      ∀ k : ℕ, 1 ≤ k → k < n → r.readout () () k < r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfloor : (0 : ℤ) < ⌊π * √(2 : ℝ)⌋ := by
    rw [Int.floor_pos]
    have hs : (1 : ℝ) ≤ √2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.pi_gt_three,
      mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hs)]
  have hbad := h 2 (by norm_num) (by change (0 : ℤ) ≠ ⌊π * √(2 : ℝ)⌋; omega) 1 (by norm_num) (by norm_num)
  change (0 : ℤ) < 0 at hbad
  exact (lt_irrefl _ hbad)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change a 0 ≠ a 1
  have ha0 : a 0 = -1 := by simp [a]
  have ha1 : a 1 = 3 := by
    simp [a, Real.arctan_one]
  omega

def registration : Registration arena (_root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Constants") "Billiards") "CollidingBlocksRecords") "result") "Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords/Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => a n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, definition := some { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, name := `D5.S3.Constants.Billiards.CollidingBlocksRecords.claim, path := #[] }, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `D5.S3.Constants.Billiards.CollidingBlocksRecords.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `D5.S3.Constants.Billiards.CollidingBlocksRecords.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalArenaFact, `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.sourceBridgeFact, `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.observationFact0, `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords


noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena
noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena
noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena D5.S3.Constants.Billiards.CollidingBlocksRecords.claim
    Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration)

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `D5.S3.Constants.Billiards.CollidingBlocksRecords.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.arena D5.S3.Constants.Billiards.CollidingBlocksRecords.claim
  Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration)

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.observation0 : (n : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
    @Ne.{1} Int (D5.S3.Constants.Billiards.CollidingBlocksRecords.a n)
        (@Int.floor.{0} Real Real.instRing Real.linearOrder Real.instFloorRing
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
            (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast n)))) →
      (k : Nat) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
          @LT.lt.{0} Nat instLTNat k n →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
    (a_1 :
      @Ne.{1} Int (D5.S3.Constants.Billiards.CollidingBlocksRecords.a n)
        (@Int.floor.{0} Real Real.instRing Real.linearOrder Real.instFloorRing
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Real.pi
            (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast n)))))
    (k : Nat) (a_2 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
    (a_3 : @LT.lt.{0} Nat instLTNat k n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.signature
    Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.actual PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `D5.S3.Constants.Billiards.CollidingBlocksRecords.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `D5.S3.Constants.Billiards.CollidingBlocksRecords.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration).actual (Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration).variation.2.choose (Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration).variation.1 (Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Constants\",\"Billiards\",\"CollidingBlocksRecords\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords, declaration := `Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
