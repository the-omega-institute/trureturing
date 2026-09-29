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

register_information_theorem suffix_prime_factors in supportArena
  readout via (realize supportSignature (fun _ p t => suffixNumber p.1 p.2 t)
    (fun e => nomatch e))
  realizes supportRegistration
  escape from source ({
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

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

register_information_theorem bellman_complete in bellmanArena
  readout via (realize signature (fun _ _ b => b) (fun e => nomatch e))
  realizes bellmanRegistration
  escape from source ({
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "body", "body", "body", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

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

register_information_theorem feasible_finite in finiteArena
  readout via (realize finiteSignature (fun _ _ t => t) (fun e => nomatch e))
  realizes finiteRegistration
  escape from source ({
    owner := `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

open Lean in
run_meta do
  for name in [
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite,
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete,
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == name
    unless row.any (fun record => match record.result with
        | .declaredValidated _ => true | _ => false) do
      throwError "{name} registration is not declaredValidated"

#print axioms supportRegistration
#print axioms bellmanRegistration
#print axioms finiteRegistration

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
