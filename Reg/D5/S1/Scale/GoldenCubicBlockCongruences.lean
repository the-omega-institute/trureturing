import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Scale.GoldenCubicBlockCongruences
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Scale.GoldenCubicBlockCongruences

open _root_.D5.S1.Scale
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    (((r.readout () () j : ℤ) : ZMod 72)) = 4 ∧
      padicValInt 2 (goldenLucas (3 ^ j)) = 2 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 : ℤ) : ZMod 5)) = 1 ∧
      (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 ∧
      goldenLucas (3 ^ (j + 1)) =
        goldenLucas (3 ^ j) * (goldenLucas (3 ^ j) ^ 2 + 3)

def registration : Registration arena
    (∀ (j : ℕ), 1 ≤ j →
      ((goldenLucas (3 ^ j) : ℤ) : ZMod 72) = 4 ∧
        padicValInt 2 (goldenLucas (3 ^ j)) = 2 ∧
        (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 9)) = 1 ∧
        (((goldenLucas (3 ^ j) ^ 2 : ℤ) : ZMod 5)) = 1 ∧
        (((goldenLucas (3 ^ j) ^ 2 + 3 : ℤ) : ZMod 80)) = 19 ∧
        goldenLucas (3 ^ (j + 1)) =
          goldenLucas (3 ^ j) * (goldenLucas (3 ^ j) ^ 2 + 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_lucas_block, rejected, ?_⟩
    intro h
    have hbad := (h 1 (by omega)).1
    change ((0 : ℤ) : ZMod 72) = 4 at hbad
    exact (by decide : (0 : ZMod 72) ≠ 4) hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := (h 1 (by omega)).1
        change ((0 : ℤ) : ZMod 72) = 4 at hbad
        exact (by decide : (0 : ZMod 72) ≠ 4) hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [actual, realize, goldenLucas, D5.S0.Carrier.trace,
      D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Scale.golden_cubic_lucas_block) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Scale") "golden_cubic_lucas_block") "Reg.D5.S1.Scale.GoldenCubicBlockCongruences/Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_lucas_block, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.sourceBridgeFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.observationFact0, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.anchorEnumeration }


abbrev fibonacciSignature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def fibonacciActual : Realization fibonacciSignature :=
  realize fibonacciSignature (fun _ _ (j : ℕ) => Nat.fib (3 ^ j))
    (fun e => nomatch e)

def fibonacciRejected : Realization fibonacciSignature :=
  realize fibonacciSignature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

def fibonacciArena : Arena where
  signature := fibonacciSignature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    ((r.readout () () j : ℕ) : ZMod 4) = 2 ∧
      padicValNat 2 (Nat.fib (3 ^ j)) = 1 ∧
      (Nat.fib (3 ^ (j + 1)) : ℤ) =
        (Nat.fib (3 ^ j) : ℤ) * (goldenLucas (3 ^ j) ^ 2 + 1)

def fibonacciRegistration : Registration fibonacciArena
    (∀ (j : ℕ), 1 ≤ j →
      ((Nat.fib (3 ^ j) : ℕ) : ZMod 4) = 2 ∧
        padicValNat 2 (Nat.fib (3 ^ j)) = 1 ∧
        (Nat.fib (3 ^ (j + 1)) : ℤ) =
          (Nat.fib (3 ^ j) : ℤ) * (goldenLucas (3 ^ j) ^ 2 + 1)) where
  actual := fibonacciActual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_fibonacci_block, fibonacciRejected, ?_⟩
    intro h
    have hbad := (h 1 (by omega)).1
    change ((0 : ℕ) : ZMod 4) = 2 at hbad
    exact (by decide : (0 : ZMod 4) ≠ 2) hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨fibonacciRejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := (h 1 (by omega)).1
        change ((0 : ℕ) : ZMod 4) = 2 at hbad
        exact (by decide : (0 : ZMod 4) ≠ 2) hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (3 ^ (0 : ℕ)) ≠ Nat.fib (3 ^ (1 : ℕ))
    decide

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Scale.golden_cubic_fibonacci_block) (type_of% (realize.{0, 0, 0, 0, 0} fibonacciSignature
    (fun _ _ (j : ℕ) => Nat.fib (3 ^ j)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Scale") "golden_cubic_fibonacci_block") "Reg.D5.S1.Scale.GoldenCubicBlockCongruences/Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(fibonacciArena)⟩,
  objectArena := .source ⟨(fibonacciArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (fibonacciArena) ⟨(fibonacciRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} fibonacciSignature
    (fun _ _ (j : ℕ) => Nat.fib (3 ^ j)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_fibonacci_block, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.sourceBridgeFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.observationFact0, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.anchorEnumeration }


def interlevelRejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def interlevelArena : Arena where
  signature := signature
  Law r := ∀ (i j : ℕ), 1 ≤ i → i < j →
    (r.readout () () j ^ 2 + 3) %
      ((goldenLucas (3 ^ i) ^ 2 + 3) ^ 2) = 3

def interlevelRegistration : Registration interlevelArena
    (∀ (i j : ℕ), 1 ≤ i → i < j →
      (goldenLucas (3 ^ j) ^ 2 + 3) %
        ((goldenLucas (3 ^ i) ^ 2 + 3) ^ 2) = 3) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_block_interlevel, interlevelRejected, ?_⟩
    intro h
    have hbad := h 1 2 (by omega) (by omega)
    change ((1 : ℤ) ^ 2 + 3) %
      ((goldenLucas (3 ^ (1 : ℕ)) ^ 2 + 3) ^ 2) = 3 at hbad
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ] at hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨interlevelRejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := h 1 2 (by omega) (by omega)
        change ((1 : ℤ) ^ 2 + 3) %
          ((goldenLucas (3 ^ (1 : ℕ)) ^ 2 + 3) ^ 2) = 3 at hbad
        norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi,
          pow_succ] at hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Scale.golden_cubic_block_interlevel) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Scale") "golden_cubic_block_interlevel") "Reg.D5.S1.Scale.GoldenCubicBlockCongruences/Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(interlevelArena)⟩,
  objectArena := .source ⟨(interlevelArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (interlevelArena) ⟨(interlevelRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_interlevel, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalObjectArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.sourceBridgeFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.observationFact0, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.anchorEnumeration }


def productArena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    r.readout () () j =
      4 * ∏ i ∈ Finset.Ico 1 j, (goldenLucas (3 ^ i) ^ 2 + 3)

def productRegistration : Registration productArena
    (∀ (j : ℕ), 1 ≤ j →
      goldenLucas (3 ^ j) =
        4 * ∏ i ∈ Finset.Ico 1 j, (goldenLucas (3 ^ i) ^ 2 + 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨golden_cubic_block_product, rejected, ?_⟩
    intro h
    have hbad := h 1 (by omega)
    change (0 : ℤ) = 4 * ∏ i ∈ Finset.Ico 1 1,
      (goldenLucas (3 ^ i) ^ 2 + 3) at hbad
    norm_num at hbad
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hbad := h 1 (by omega)
        change (0 : ℤ) = 4 * ∏ i ∈ Finset.Ico 1 1,
          (goldenLucas (3 ^ i) ^ 2 + 3) at hbad
        norm_num at hbad
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas (3 ^ (0 : ℕ)) ≠ goldenLucas (3 ^ (1 : ℕ))
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Scale.golden_cubic_block_product) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Scale") "golden_cubic_block_product") "Reg.D5.S1.Scale.GoldenCubicBlockCongruences/Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(productArena)⟩,
  objectArena := .source ⟨(productArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (productArena) ⟨(productRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (j : ℕ) => goldenLucas (3 ^ j)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_product, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalObjectArenaFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.sourceBridgeFact, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.observationFact0, `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.anchorEnumeration }


end Reg.D5.S1.Scale.GoldenCubicBlockCongruences


noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena
    (∀ (i j : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) i →
        @LT.lt.{0} Nat instLTNat i j →
          @Eq.{1} Int
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_interlevel\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_interlevel, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelArena
  (∀ (i j : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) i →
      @LT.lt.{0} Nat instLTNat i j →
        @Eq.{1} Int
          (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.observation0 : (i j : Nat) →
  (hi : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) i) →
    (hij : @LT.lt.{0} Nat instLTNat i j) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (i j : Nat) (hi : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) i)
    (hij : @LT.lt.{0} Nat instLTNat i j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature Reg.D5.S1.Scale.GoldenCubicBlockCongruences.actual
    PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_interlevel\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_interlevel, part := .type, path := [.body, .body, .body, .body, .function, .argument, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_interlevel\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_interlevel, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration).actual (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration).variation.2.choose (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration).variation.1 (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"interlevelRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.interlevelRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena
    (∀ (j : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
        @Eq.{1} Int
          (D5.S1.Scale.goldenLucas
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
            (@Finset.prod.{0, 0} Nat Int Int.instCommMonoid
              (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
              fun (i : Nat) =>
              @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))))
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_product, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productArena
  (∀ (j : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
      @Eq.{1} Int
        (D5.S1.Scale.goldenLucas
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
          (@Finset.prod.{0, 0} Nat Int Int.instCommMonoid
            (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
            fun (i : Nat) =>
            @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))))
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.observation0 : (j : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature Reg.D5.S1.Scale.GoldenCubicBlockCongruences.actual
    PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_product\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_product, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_block_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_block_product, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration).actual (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration).variation.2.choose (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration).variation.1 (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"productRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.productRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena
    (∀ (j : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
        And
          (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@Nat.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (And
            (@Eq.{1} Nat
              (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Int
              (@Nat.cast.{0} Int instNatCastInt
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (@Nat.cast.{0} Int instNatCastInt
                  (Nat.fib
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))))
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_fibonacci_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_fibonacci_block, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciArena
  (∀ (j : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
      And
        (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Nat.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
            (Nat.fib
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (And
          (@Eq.{1} Nat
            (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Int
            (@Nat.cast.{0} Int instNatCastInt
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@Nat.cast.{0} Int instNatCastInt
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))))
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.observation0 : (j : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciSignature
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciActual PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_fibonacci_block\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_fibonacci_block, part := .type, path := [.body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_fibonacci_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_fibonacci_block, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration).actual (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration).variation.2.choose (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration).variation.1 (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"fibonacciRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.fibonacciRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena
    (∀ (j : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
        And
          (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
            (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))))
              (D5.S1.Scale.goldenLucas
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))) (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (nat_lit 4)
                (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))))))
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
          (And
            (@Eq.{1} Nat
              (padicValInt (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (D5.S1.Scale.goldenLucas
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (And
              (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                  (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (D5.S1.Scale.goldenLucas
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 1)
                  (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))))))
              (And
                (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (D5.S1.Scale.goldenLucas
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 1)
                    (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))))
                (And
                  (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (@AddGroupWithOne.toIntCast.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))
                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          (D5.S1.Scale.goldenLucas
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (nat_lit 19)
                      (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (nat_lit 19)
                        (@AddMonoidWithOne.toNatCast.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                              (@CommRing.toRing.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))))
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))))))))
                  (@Eq.{1} Int
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                      (D5.S1.Scale.goldenLucas
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                          (D5.S1.Scale.goldenLucas
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))))))))
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_lucas_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_lucas_block, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.arena
  (∀ (j : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
      And
        (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
          (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
            (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))))
            (D5.S1.Scale.goldenLucas
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))) (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))) (nat_lit 4)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))))))
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
        (And
          (@Eq.{1} Nat
            (padicValInt (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (D5.S1.Scale.goldenLucas
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (And
            (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
              (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
              (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                  (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))))))
            (And
              (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 1)
                  (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                          (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))))))
              (And
                (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                  (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (@AddGroupWithOne.toIntCast.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (@Ring.toAddGroupWithOne.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                      (@HPow.hPow.{0, 0, 0} Int Nat Int
                        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                        (D5.S1.Scale.goldenLucas
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))) (nat_lit 19)
                    (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (nat_lit 19)
                      (@AddMonoidWithOne.toNatCast.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))))
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))))))))
                (@Eq.{1} Int
                  (D5.S1.Scale.goldenLucas
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (D5.S1.Scale.goldenLucas
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                      (@HPow.hPow.{0, 0, 0} Int Nat Int
                        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                        (D5.S1.Scale.goldenLucas
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))))))))))
  Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration)

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.observation0 : (j : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Scale.GoldenCubicBlockCongruences.signature Reg.D5.S1.Scale.GoldenCubicBlockCongruences.actual
    PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_lucas_block\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_lucas_block, part := .type, path := [.body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Scale\",\"golden_cubic_lucas_block\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `D5.S1.Scale.golden_cubic_lucas_block, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration).actual (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration).variation.2.choose (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration).variation.1 (Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Scale\",\"GoldenCubicBlockCongruences\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences, declaration := `Reg.D5.S1.Scale.GoldenCubicBlockCongruences.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
