import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists

open _root_.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
open _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => cubefreePart j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    (mordellCurve (-3 * (r.readout () () j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (cubefreePart j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (-3 * (block j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (block j : ℤ) ^ 2)).IsElliptic ∧
    InfiniteOrderPoint (-3 * (cubefreePart j : ℤ) ^ 2)
      ((cubefreePart j : ℤ) * cubePartRoot j)
      ((cubefreePart j : ℤ) * D5.S1.Scale.goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (cubefreePart j : ℤ) ^ 2)
      (5 * (cubefreePart j : ℤ) * cubePartRoot j)
      (25 * (cubefreePart j : ℤ) * Nat.fib (3 ^ j)) ∧
    InfiniteOrderPoint (-3 * (block j : ℤ) ^ 2)
      (block j : ℤ) ((block j : ℤ) * D5.S1.Scale.goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (block j : ℤ) ^ 2)
      (5 * (block j : ℤ)) (25 * (block j : ℤ) * Nat.fib (3 ^ j)) ∧
    ∀ i : ℕ, 1 ≤ i → i ≠ j →
      (¬∃ q : ℚ, (cubefreePart i : ℚ) = q ^ 3 * (cubefreePart j : ℚ)) ∧
      (¬∃ q : ℚ,
        ((-3 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((-3 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6) ∧
      (¬∃ q : ℚ,
        ((125 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((125 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by decide)).1
  have hunit : IsUnit (0 : ℚ) := by
    simpa [rejected, realize, mordellCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] using hbad.isUnit
  norm_num at hunit

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    exact actual_cubic_twists
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change cubefreePart 1 ≠ cubefreePart 2
    intro heq
    have hsep := (actual_cubic_twists 2 (by decide)).2.2.2.2.2.2.2.2
      1 (by decide) (by decide)
    exact hsep.1 ⟨1, by norm_num [heq]⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => cubefreePart j) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Mordell") "GoldenCubicBlockMordellTwists") "actual_cubic_twists") "Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists/Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => cubefreePart j) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.observationFact0, `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists


noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.arena
noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.arena
noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.arena) (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).actual

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"actual_cubic_twists\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).bridge

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.observation0 : (j : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.signature
    Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"actual_cubic_twists\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists, part := .type, path := [.body, .body, .function, .argument, .argument, .argument, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"actual_cubic_twists\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).actual (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).variation.2.choose (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).variation.1 (Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"GoldenCubicBlockMordellTwists\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists, declaration := `Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
