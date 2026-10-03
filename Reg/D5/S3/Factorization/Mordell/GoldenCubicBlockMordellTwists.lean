import D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists

open _root_.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
open _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => cubefreePart j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ), 1 ≤ j →
    (mordellCurve (-3 * (r.readout () () j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (cubefreePart j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (-3 * (block j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (block j : ℤ) ^ 2)).IsElliptic ∧
    InfiniteOrderPoint (-3 * (cubefreePart j : ℤ) ^ 2)
      ((cubefreePart j : ℤ) * cubePartRoot j)
      ((cubefreePart j : ℤ) * D5.S1.Scale.goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (cubefreePart j : ℤ) ^ 2)
      (5 * (cubefreePart j : ℤ) * cubePartRoot j)
      (25 * (cubefreePart j : ℤ) * Nat.fib (3 ^ j)) ∧
    InfiniteOrderPoint (-3 * (block j : ℤ) ^ 2)
      (block j : ℤ) ((block j : ℤ) * D5.S1.Scale.goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (block j : ℤ) ^ 2)
      (5 * (block j : ℤ)) (25 * (block j : ℤ) * Nat.fib (3 ^ j)) ∧
    ∀ i : ℕ, 1 ≤ i → i ≠ j →
      (¬∃ q : ℚ, (cubefreePart i : ℚ) = q ^ 3 * (cubefreePart j : ℚ)) ∧
      (¬∃ q : ℚ,
        ((-3 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((-3 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6) ∧
      (¬∃ q : ℚ,
        ((125 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((125 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by decide)).1
  have hunit : IsUnit (0 : ℚ) := by
    simpa [rejected, realize, mordellCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] using hbad.isUnit
  norm_num at hunit

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    exact actual_cubic_twists
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change cubefreePart 1 ≠ cubefreePart 2
    intro heq
    have hsep := (actual_cubic_twists 2 (by decide)).2.2.2.2.2.2.2.2
      1 (by decide) (by decide)
    exact hsep.1 ⟨1, by norm_num [heq]⟩

register_information_theorem
  _root_.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists.actual_cubic_twists
  in arena
  readout via (realize signature (fun _ _ j => cubefreePart j) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
