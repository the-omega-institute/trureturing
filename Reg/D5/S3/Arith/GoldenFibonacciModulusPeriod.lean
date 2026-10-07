import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod

open scoped Matrix
open _root_.D5.S3.Arith.GoldenFibonacciModulusPeriod
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
  realize signature (fun _ _ n => 4 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => 4 * n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 5 ≤ n) (_hodd : Odd n),
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n))) =
      r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 5 (by decide) (by decide)
  have hgood := golden_fibonacci_modulus_period 5 (by decide) (by decide)
  change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib 5))) =
    4 * 5 + 1 at hbad
  omega

def registration : Registration arena
    (∀ (n : ℕ) (_hn : 5 ≤ n) (_hodd : Odd n),
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (Nat.fib n))) =
        4 * n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_fibonacci_modulus_period, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (5 : ℕ), (7 : ℕ), ?_⟩
    change (20 : ℕ) ≠ 28
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 4 * n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "GoldenFibonacciModulusPeriod") "golden_fibonacci_modulus_period") "Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod/Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 4 * n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.observationFact0, `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod


noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.arena
noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.arena
noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.arena) (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).actual

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"golden_fibonacci_modulus_period\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).bridge

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.observation0 : (n : Nat) →
  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n) →
    (hodd : @Odd.{0} Nat Nat.instSemiring n) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n)
    (hodd : @Odd.{0} Nat Nat.instSemiring n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.signature Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.actual
    PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"golden_fibonacci_modulus_period\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period, part := .type, path := [.body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"golden_fibonacci_modulus_period\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `D5.S3.Arith.GoldenFibonacciModulusPeriod.golden_fibonacci_modulus_period, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).actual (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).variation.2.choose (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).variation.1 (Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenFibonacciModulusPeriod\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod, declaration := `Reg.D5.S3.Arith.GoldenFibonacciModulusPeriod.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
