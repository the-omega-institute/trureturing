import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ell => suffixNumber 1 0 ell) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (ell : List ℕ) (_hell : Ordered (ell.headD 0) ell) (B : ℕ),
    let M := R.readout () () ell
    (B < M ↔ ¬∃ n : ℕ, 1 ≤ n ∧ n ≤ B ∧ M ∣ n) ∧
    (M ≤ B → ∃ (n : ℕ) (t : List ℕ),
      1 ≤ n ∧ n ≤ B ∧ M ∣ n ∧
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        n.factorization q ≤ n.factorization p) ∧
      Ordered (rootCap 1 B) t ∧ suffixNumber 1 0 t = n ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n = suffixWeight 1 0 t ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ B → M ∣ m →
        (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
          (ArithmeticFunction.sigma 1 n : ℝ) / n))

theorem actual_law : arena.Law actual := by
  exact forced_core_normalization

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h [] (by trivial) 0).1
  norm_num [rejected, realize] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
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
    refine ⟨(), [], [1], ?_⟩
    simpa only [actual, realize, suffixNumber, pow_one, mul_one,
      prime, Nat.add_zero] using
      (Nat.prime_nth_prime (Nat.primeCounting 1)).ne_one.symm

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => suffixNumber 1 0 ell)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "ForcedCoreNormalization") "forced_core_normalization") "Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization/Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => suffixNumber 1 0 ell)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
