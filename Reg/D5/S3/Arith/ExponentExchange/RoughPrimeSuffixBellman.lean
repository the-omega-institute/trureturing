import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Every clause is retained; the root state's integer budget is observed. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (y B : ℕ) (_hy : 1 ≤ y) (hB : 1 ≤ B),
    (∀ i b h : ℕ, 1 ≤ b →
      V y i b h = (branchValues y i b h).max' (by
        classical
        exact ⟨1, Finset.mem_insert_self _ _⟩) ∧
      (∀ t : List ℕ, Feasible y i b h t → suffixWeight y i t ≤ V y i b h) ∧
      (∃ t : List ℕ, Feasible y i b h t ∧ suffixWeight y i t = V y i b h) ∧
      (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b → b / prime y i ^ a < b)) ∧
    (∀ p : ℕ, p.Prime ∧ y < p ↔ ∃ i : ℕ, p = prime y i) ∧
    (∀ a : ℕ, a ≤ rootCap y B ↔ prime y 0 ^ a ≤ B) ∧
    (∀ (i : ℕ) (t : List ℕ),
      (ArithmeticFunction.sigma 1 (suffixNumber y i t) : ℝ) /
        suffixNumber y i t = suffixWeight y i t) ∧
    (∃ (n : ℕ) (t : List ℕ), 1 ≤ n ∧ n ≤ B ∧ Rough y n ∧
      Feasible y 0 B (rootCap y B) t ∧ suffixNumber y 0 t = n ∧
      suffixWeight y 0 t = U y B) ∧
    U y B = V y 0 (R.readout () () B) (rootCap y B)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq := (h 1 1 (by decide) (by decide)).2.2.2.2.2
  have hrough : Rough 1 1 := by
    intro p hp hd
    exact (hp.ne_one (Nat.dvd_one.mp hd)).elim
  simp [rejected, realize, V, U, Finset.filter_singleton, hrough] at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rough_prime_suffix_complete, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "rough_prime_suffix_complete") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.observationFact0, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms registration

abbrev supportSignature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def supportActual : Realization supportSignature :=
  realize supportSignature (fun _ p t => suffixNumber p.1 p.2 t) (fun e => nomatch e)

def supportRejected : Realization supportSignature :=
  realize supportSignature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def supportArena : Arena where
  signature := supportSignature
  Law R := ∀ (y i : ℕ) (t : List ℕ),
    0 < R.readout () ⟨y, i⟩ t ∧
      (∀ p : ℕ, p.Prime → p ∣ suffixNumber y i t →
        ∃ j : ℕ, j < t.length ∧ p = prime y (i + j)) ∧
      Rough y (suffixNumber y i t)

theorem support_rejected_law : ¬ supportArena.Law supportRejected := by
  intro h
  have hh := (h 0 0 []).1
  change (0 : ℕ) < 0 at hh
  omega

def supportRegistration : Registration supportArena (supportArena.Law supportActual) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨suffix_prime_factors, supportRejected, support_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨supportRejected, ?_, rfl, support_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨0, 0⟩, [], [1], ?_⟩
    change suffixNumber 0 0 [] ≠ suffixNumber 0 0 [1]
    simp only [suffixNumber, pow_one, Nat.mul_one]
    exact (Nat.prime_nth_prime _).ne_one.symm

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors) (type_of% (realize.{0, 0, 0, 0, 0} supportSignature (fun _ p t => suffixNumber p.1 p.2 t)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "suffix_prime_factors") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(supportArena)⟩,
  objectArena := .source ⟨(supportArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (supportArena) ⟨(supportRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} supportSignature (fun _ p t => suffixNumber p.1 p.2 t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.sourceBridgeFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.observationFact0, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.anchorEnumeration }


@[reducible] def bellmanArena : Arena where
  signature := signature
  Law R := ∀ (y i b h : ℕ) (_hb : 1 ≤ b),
    V y i b h = (branchValues y i b h).max' (by
      classical
      exact ⟨1, Finset.mem_insert_self _ _⟩) ∧
    (∀ t : List ℕ, Feasible y i b h t → suffixWeight y i t ≤ V y i b h) ∧
    (∃ t : List ℕ, Feasible y i b h t ∧ suffixWeight y i t = V y i b h) ∧
    (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b →
      b / prime y i ^ a < R.readout () () b)

theorem bellman_rejected_law : ¬ bellmanArena.Law rejected := by
  intro h
  have hh := (h 0 0 (prime 0 0) 1 (Nat.prime_nth_prime _).one_lt.le).2.2.2
    1 (by decide) (by simp)
  change prime 0 0 / prime 0 0 ^ 1 < 0 at hh
  exact Nat.not_lt_zero _ hh

def bellmanRegistration : Registration bellmanArena (bellmanArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bellman_complete, rejected, bellman_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bellman_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; decide⟩

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "bellman_complete") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(bellmanArena)⟩,
  objectArena := .source ⟨(bellmanArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (bellmanArena) ⟨(bellmanRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.sourceBridgeFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.observationFact0, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.anchorEnumeration }


abbrev finiteSignature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ _ t => t) (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => []) (fun e => nomatch e)

@[reducible] def finiteArena : Arena where
  signature := finiteSignature
  Law R := ∀ y i b h : ℕ, {t : List ℕ | Feasible y i b h (R.readout () () t)}.Finite

theorem finite_rejected_law : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hh := h 0 0 1 0
  have heq : {t : List ℕ | Feasible 0 0 1 0 (finiteRejected.readout () () t)} =
      Set.univ := by
    ext t
    simp [finiteRejected, realize, Feasible, Ordered, suffixNumber]
  rw [heq] at hh
  exact Set.infinite_univ.not_finite hh

def finiteRegistration : Registration finiteArena (finiteArena.Law finiteActual) where
  actual := finiteActual
  bridge := Iff.rfl
  variation := ⟨feasible_finite, finiteRejected, finite_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finite_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), [], [0], by change ([] : List ℕ) ≠ [0]; simp⟩

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite) (type_of% (realize.{0, 0, 0, 0, 0} finiteSignature (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "feasible_finite") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(finiteArena)⟩,
  objectArena := .source ⟨(finiteArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (finiteArena) ⟨(finiteRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} finiteSignature (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.sourceBridgeFact, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.observationFact0, `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.anchorEnumeration }


#print axioms supportRegistration
#print axioms bellmanRegistration
#print axioms finiteRegistration

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman


noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.arena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.arena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanArena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteArena) (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).actual

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"feasible_finite\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).bridge

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.observation0 : (y i b h : Nat) →
  (t : List.{0} Nat) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (y i b h : Nat) (t : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteSignature
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteActual PUnit.unit.{1} PUnit.unit.{1} t

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"feasible_finite\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite, part := .type, path := [.body, .body, .body, .body, .argument, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"feasible_finite\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).actual (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).variation.2.choose (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).variation.1 (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"finiteRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportArena) (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).actual

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"suffix_prime_factors\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).bridge

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.observation0 : (y i : Nat) →
  (t : List.{0} Nat) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportSignature PUnit.unit.{1}
      (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) y i) :=
  fun (y i : Nat) (t : List.{0} Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportSignature
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) y i) t

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"suffix_prime_factors\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors, part := .type, path := [.body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"suffix_prime_factors\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).actual (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).variation.2.choose (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).variation.1 (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"supportRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.arena) (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).actual

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"rough_prime_suffix_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).bridge

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.observation0 : (y B : Nat) →
  (_hy : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y) →
    (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (y B : Nat) (_hy : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
    (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.signature
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.actual PUnit.unit.{1} PUnit.unit.{1} B

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"rough_prime_suffix_complete\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete, part := .type, path := [.body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"rough_prime_suffix_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).actual (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).variation.2.choose (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).variation.1 (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanArena) (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).actual

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"bellman_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).bridge

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.observation0 : (y i b h : Nat) →
  (hb : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b) →
    (a : Nat) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
        @LE.le.{0} Nat instLENat
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.prime y i) a)
            b →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (y i b h : Nat) (hb : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
    (a : Nat) (a_1 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
    (a_2 :
      @LE.le.{0} Nat instLENat
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.prime y i) a)
        b) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.signature
    Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.actual PUnit.unit.{1} PUnit.unit.{1} b

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"bellman_complete\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument, .argument, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"bellman_complete\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).actual (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).variation.2.choose (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).variation.1 (Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"RoughPrimeSuffixBellman\",\"bellmanRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, declaration := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
