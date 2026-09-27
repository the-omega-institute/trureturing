import D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
import Reg.Support.DependentFamily
import Mathlib.Tactic.Linarith

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
open _root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => expectedRange n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℤ, r.readout () () n * 2 ^ (3 * n - 3) = m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, hm⟩ := h 1 (by norm_num)
  change (1 / 2 : ℚ) * 2 ^ (3 * 1 - 3) = m at hm
  have hi : (m : ℚ) > 0 ∧ (m : ℚ) < 1 := by norm_num at hm; constructor <;> linarith
  have : (0 : ℤ) < m ∧ m < 1 := by exact_mod_cast hi
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change expectedRange 0 ≠ expectedRange 1
  decide +kernel

def registration : Registration arena (_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.result in arena
  readout via (realize signature (fun _ _ n => expectedRange n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
    «definition» := some {
      owner := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
      name := `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality.claim }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
