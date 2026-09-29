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

register_information_theorem forced_core_normalization in arena
  readout via (realize signature (fun _ _ ell => suffixNumber 1 0 ell)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "value"], stateBinder := 0 }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "forced core normalization registration is not declaredValidated"

#print axioms registration

end Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
