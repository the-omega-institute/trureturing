/- GID: D5/S3/ResourceOrder/FiniteAnchorCoverage
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/FiniteAnchorCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite anchor families have bounded coverage and admit exact off-union evasion. -/

/- Library-search audit trail (2026-08-14):
   * `Finset.card_biUnion_le` is the exact finite-union bound used below.
   * The repository uses that lemma for a different program-record covering
     argument, but has no complete anchor-suite coverage and evasion theorem.
   * The Boolean implementation and its exact error-set identity are assembled
     here rather than replacing the library cardinality lemma.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

open Set

namespace D5.S3.ResourceOrder.FiniteAnchorCoverage

universe u v

/-- The inputs exposed by at least one suite in a finite anchor family. -/
def coveredInputs {Anchor : Type u} {Input : Type v} [Fintype Anchor]
    [DecidableEq Input] (suite : Anchor -> Finset Input) : Finset Input :=
  Finset.univ.biUnion suite

/-- A family of at most `2 ^ h` suites of size at most `m` covers at most
`2 ^ h * m` inputs. There is an implementation that agrees with the truth on
every suite and disagrees with it exactly outside their union. -/
theorem finite_anchor_coverage_bound_and_evasion
    {Anchor : Type u} {Input : Type v} [Fintype Anchor] [DecidableEq Input]
    (suite : Anchor -> Finset Input) (truth : Input -> Bool) (h m : Nat)
    (anchor_card : Fintype.card Anchor <= 2 ^ h)
    (suite_card : forall anchor, (suite anchor).card <= m) :
    (coveredInputs suite).card <= 2 ^ h * m ∧
      exists implementation : Input -> Bool,
        (forall anchor input, input ∈ suite anchor ->
          implementation input = truth input) ∧
        {input | implementation input != truth input} =
          (↑(coveredInputs suite) : Set Input)ᶜ := by
  classical
  constructor
  · calc
      (coveredInputs suite).card <=
          ∑ anchor ∈ (Finset.univ : Finset Anchor), (suite anchor).card := by
        exact Finset.card_biUnion_le
      _ <= ∑ _anchor ∈ (Finset.univ : Finset Anchor), m := by
        exact Finset.sum_le_sum fun anchor _ => suite_card anchor
      _ = Fintype.card Anchor * m := by simp
      _ <= 2 ^ h * m := Nat.mul_le_mul_right m anchor_card
  · let implementation : Input -> Bool := fun input =>
      if input ∈ coveredInputs suite then truth input else !truth input
    refine ⟨implementation, ?_, ?_⟩
    · intro anchor input input_mem
      have input_covered : input ∈ coveredInputs suite := by
        exact Finset.mem_biUnion.mpr ⟨anchor, Finset.mem_univ _, input_mem⟩
      simp [implementation, input_covered]
    · ext input
      by_cases input_covered : input ∈ coveredInputs suite
      · simp [implementation, input_covered]
      · cases truth input <;> simp [implementation, input_covered]

/-- A two-anchor, three-input family witnesses that the complete hypothesis
bundle is satisfiable with positive anchor and suite budgets. -/
example :
    exists (suite : Fin 2 -> Finset (Fin 3)) (_truth : Fin 3 -> Bool) (h m : Nat),
      Fintype.card (Fin 2) <= 2 ^ h ∧
        forall anchor, (suite anchor).card <= m := by
  refine ⟨fun _ => {0}, fun _ => false, 1, 1, by decide, ?_⟩
  intro anchor
  simp

/-- The concrete input domain used by the satisfiability witness is inhabited. -/
example : Nonempty (Fin 3) := inferInstance

#print axioms finite_anchor_coverage_bound_and_evasion

end D5.S3.ResourceOrder.FiniteAnchorCoverage
