import D5.S3.Arith.Primes.LucasSquareClassification
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.LucasSquareClassification

open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.LucasSquareClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => goldenLucas n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def intervention (i : Fin 2) : Realization signature :=
  realize signature (fun j _ n => if j = i then 0 else goldenLucas n)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    (IsSquare (r.readout 0 () n) ↔ n = 1 ∨ n = 3) ∧
      ((∃ x : ℤ, r.readout 1 () n = 2 * x ^ 2) ↔ n = 0 ∨ n = 6)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : IsSquare (rejected.readout 0 () 0) := ⟨0, rfl⟩
  have hb := (h 0).1.mp hs
  omega

theorem intervention_law_failure (i : Fin 2) : ¬ arena.Law (intervention i) := by
  intro h
  fin_cases i
  · have hs : IsSquare ((intervention 0).readout 0 () 0) := by
      refine ⟨0, ?_⟩
      norm_num [intervention, realize]
    have hb := (h 0).1.mp hs
    omega
  · have hs : ∃ x : ℤ, (intervention 1).readout 1 () 1 = 2 * x ^ 2 := by
      refine ⟨0, ?_⟩
      norm_num [intervention, realize]
    have hb := (h 1).2.mp hs
    omega

def registration : Registration arena
    (∀ n : ℕ, (IsSquare (goldenLucas n) ↔ n = 1 ∨ n = 3) ∧
      ((∃ x : ℤ, goldenLucas n = 2 * x ^ 2) ↔ n = 0 ∨ n = 6)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lucas_square_classifications, rejected, rejected_law⟩
  sensitivity := by
    classical
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law_failure i⟩
      intro j hji
      funext p n
      change (j : Fin 2) ≠ (i : Fin 2) at hji
      simp only [actual, intervention, realize]
      exact (if_neg hji).symm
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas 0 ≠ goldenLucas 1
    decide

register_information_theorem
  lucas_square_classifications
  in arena
  readout via (realize signature (fun _ _ n => goldenLucas n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.LucasSquareClassification
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }, {
      path := #["body", "arg", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.LucasSquareClassification
