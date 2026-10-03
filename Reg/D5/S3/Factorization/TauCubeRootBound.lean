import D5.S3.Factorization.TauCubeRootBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.TauCubeRootBound

open _root_.D5.S3.Factorization.TauCubeRootBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ j => j.divisors.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ j : ℕ, 0 < j →
      (R.readout () () j : ℝ) ≤ 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) ∧
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) < 4 * (j : ℝ) ^ ((1 : ℝ) / 3)) ∧
    (R.readout () () 2520 : ℝ) =
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq : (0 : ℝ) = 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
      (2520 : ℝ) ^ ((1 : ℝ) / 3) := by
    simpa [arena, rejected, realize] using h.2
  have hp : 0 < 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
      (2520 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  linarith

def registration : Registration arena
    ((∀ j : ℕ, 0 < j →
      (j.divisors.card : ℝ) ≤ 8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) ∧
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (j : ℝ) ^ ((1 : ℝ) / 3) < 4 * (j : ℝ) ^ ((1 : ℝ) / 3)) ∧
    ((2520 : ℕ).divisors.card : ℝ) =
      8 * (3 / 35 : ℝ) ^ ((1 : ℝ) / 3) *
        (2520 : ℝ) ^ ((1 : ℝ) / 3)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

register_information_theorem result in arena
  readout via (realize signature (fun _ _ j => j.divisors.card)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.TauCubeRootBound
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.TauCubeRootBound
