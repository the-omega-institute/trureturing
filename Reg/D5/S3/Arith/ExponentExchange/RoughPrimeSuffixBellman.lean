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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "rough_prime_suffix_complete") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors) (type_of% (supportArena)) (type_of% (supportArena)) (type_of% (realize.{0, 0, 0, 0, 0} supportSignature (fun _ p t => suffixNumber p.1 p.2 t)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "suffix_prime_factors") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.supportRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(supportArena)⟩,
  objectArena := ⟨(supportArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (supportArena) ⟨(supportRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} supportSignature (fun _ p t => suffixNumber p.1 p.2 t)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete) (type_of% (bellmanArena)) (type_of% (bellmanArena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "bellman_complete") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellmanRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(bellmanArena)⟩,
  objectArena := ⟨(bellmanArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (bellmanArena) ⟨(bellmanRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => b) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite) (type_of% (finiteArena)) (type_of% (finiteArena)) (type_of% (realize.{0, 0, 0, 0, 0} finiteSignature (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "RoughPrimeSuffixBellman") "feasible_finite") "Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman/Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.finiteRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(finiteArena)⟩,
  objectArena := ⟨(finiteArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (finiteArena) ⟨(finiteRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} finiteSignature (fun _ _ t => t) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms supportRegistration
#print axioms bellmanRegistration
#print axioms finiteRegistration

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
