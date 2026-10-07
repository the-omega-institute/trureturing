import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks

open _root_.D5.S1.Scale
open _root_.D5.S0.Carrier
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace C

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
  realize signature (fun _ _ j => 3 ^ (j + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => 3 ^ (j + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
    fibonacciRank p = r.readout () () j ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 1) =
        padicValNat p (Nat.fib (fibonacciRank p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (17 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 1 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := (cubic_block_c_prime_rank 1 17 (by decide) (by decide) hdiv).1
  have hbad := (h 1 17 (by decide) (by decide) hdiv).1
  change fibonacciRank 17 = 3 ^ (1 + 1) at hgood
  change fibonacciRank 17 = 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1),
      fibonacciRank p = 3 ^ (j + 1) ∧
        padicValInt p (goldenLucas (3 ^ j) ^ 2 + 1) =
          padicValNat p (Nat.fib (fibonacciRank p))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_c_prime_rank, rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change 3 ^ (1 + 1) ≠ 3 ^ (2 + 1)
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => 3 ^ (j + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenCubicBlockRanks") "cubic_block_c_prime_rank") "Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks/Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => 3 ^ (j + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.anchorEnumeration }


end C

namespace B

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
  realize signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => 2 * 3 ^ (j + 1) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3),
    fibonacciRank p = r.readout () () j ∧
      @legendreSym p ⟨_hp⟩ 5 = 1 ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 3) =
        padicValNat p (Nat.fib (fibonacciRank p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hdiv : (19 : ℤ) ∣ goldenLucas (3 ^ 1) ^ 2 + 3 := by
    norm_num [goldenLucas, trace, D5.S0.Carrier.phi, pow_succ]
  have hgood := (cubic_block_b_prime_rank 1 19 (by decide) (by decide) hdiv).1
  have hbad := (h 1 19 (by decide) (by decide) hdiv).1
  change fibonacciRank 19 = 2 * 3 ^ (1 + 1) at hgood
  change fibonacciRank 19 = 2 * 3 ^ (1 + 1) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (j p : ℕ) (_hj : 1 ≤ j) (_hp : p.Prime)
      (_hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3),
      fibonacciRank p = 2 * 3 ^ (j + 1) ∧
        @legendreSym p ⟨_hp⟩ 5 = 1 ∧
        padicValInt p (goldenLucas (3 ^ j) ^ 2 + 3) =
          padicValNat p (Nat.fib (fibonacciRank p))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_b_prime_rank, rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change 2 * 3 ^ (1 + 1) ≠ 2 * 3 ^ (2 + 1)
    norm_num

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenCubicBlockRanks") "cubic_block_b_prime_rank") "Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks/Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => 2 * 3 ^ (j + 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.observationFact0, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.anchorEnumeration }


end B

end Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks


noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena
    (∀ (j p : Nat) (_hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (_hp : Nat.Prime p)
      (_hpB :
        @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (D5.S1.Scale.goldenLucas
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))),
      And
        (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (And
          (@Eq.{1} Int
            (@legendreSym p (@Fact.mk (Nat.Prime p) _hp) (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))))
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Nat
            (padicValInt p
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
            (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_b_prime_rank\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.arena
  (∀ (j p : Nat) (_hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
    (_hp : Nat.Prime p)
    (_hpB :
      @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (D5.S1.Scale.goldenLucas
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))),
    And
      (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (And
        (@Eq.{1} Int
          (@legendreSym p (@Fact.mk (Nat.Prime p) _hp) (@OfNat.ofNat.{0} Int (nat_lit 5) (@instOfNat (nat_lit 5))))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Eq.{1} Nat
          (padicValInt p
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
          (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.observation0 : (j p : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    (hp : Nat.Prime p) →
      (hpB :
          @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j p : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
    (hp : Nat.Prime p)
    (hpB :
      @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (D5.S1.Scale.goldenLucas
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.signature Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.actual
    PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_b_prime_rank\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_b_prime_rank\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration).actual (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration).variation.1 (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"B\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.B.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena
    (∀ (j p : Nat) (_hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
      (_hp : Nat.Prime p)
      (_hpC :
        @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (D5.S1.Scale.goldenLucas
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
      And
        (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Eq.{1} Nat
          (padicValInt p
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)))))
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_c_prime_rank\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.arena
  (∀ (j p : Nat) (_hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
    (_hp : Nat.Prime p)
    (_hpC :
      @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (D5.S1.Scale.goldenLucas
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))),
    And
      (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Eq.{1} Nat
        (padicValInt p
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (D5.S1.Scale.goldenLucas
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)))))
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.observation0 : (j p : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    (hp : Nat.Prime p) →
      (hpC :
          @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j p : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
    (hp : Nat.Prime p)
    (hpC :
      @Dvd.dvd.{0} Int Int.instDvd (@Nat.cast.{0} Int instNatCastInt p)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (D5.S1.Scale.goldenLucas
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.signature Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.actual
    PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_c_prime_rank\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"cubic_block_c_prime_rank\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_c_prime_rank, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration).actual (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration).variation.1 (Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockRanks\",\"C\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockRanks.C.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
