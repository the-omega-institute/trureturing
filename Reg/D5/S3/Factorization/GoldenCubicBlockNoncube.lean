import D5.S3.Factorization.GoldenCubicBlockNoncube
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.GoldenCubicBlockNoncube

open _root_.D5.S0.Carrier
open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.GoldenCubicBlockNoncube
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => goldenLucas (3 ^ j) ^ 2 + 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (j : ℕ) (_hj : 1 ≤ j),
    ¬ ∃ t : ℤ, t ^ 3 = r.readout () () j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 1 (by decide)
  change ¬ ∃ t : ℤ, t ^ 3 = 0 at hzero
  exact hzero ⟨0, by norm_num⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro j hj
    exact golden_cubic_block_not_cube j hj
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℕ),
      goldenLucas (3 ^ x) ^ 2 + 3 ≠ goldenLucas (3 ^ y) ^ 2 + 3
    refine ⟨(), 1, 2, ?_⟩
    have h3 : goldenLucas 3 = 4 := by
      norm_num [goldenLucas, trace, phi, pow_succ]
    have h9 : goldenLucas 9 = 76 := by
      simpa [h3] using (golden_cubic_lucas_block 1 (by decide)).2.2.2.2.2
    norm_num [h3, h9]

register_information_theorem
  _root_.D5.S3.Factorization.GoldenCubicBlockNoncube.golden_cubic_block_not_cube
  in arena
  readout via (realize signature
    (fun _ _ j => goldenLucas (3 ^ j) ^ 2 + 3) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.GoldenCubicBlockNoncube
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.GoldenCubicBlockNoncube
