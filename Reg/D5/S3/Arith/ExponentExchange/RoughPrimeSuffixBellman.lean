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

register_information_theorem rough_prime_suffix_complete in arena
  readout via (realize signature (fun _ _ b => b) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "rough prime suffix registration is not declaredValidated"

#print axioms rejected_law
#print axioms registration

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
