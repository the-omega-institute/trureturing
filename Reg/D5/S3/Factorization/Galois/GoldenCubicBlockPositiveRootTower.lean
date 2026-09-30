import D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower

open _root_.D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

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
  realize signature
    (fun _ _ J => Module.finrank ComplexBase (complexTower J))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ J : ℕ, R.readout () () J = 3 ^ J

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0
  norm_num [rejected, realize] at hzero

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro J
    exact golden_cubic_block_positive_root_tower_degree J
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
    refine ⟨(), 0, 1, ?_⟩
    change Module.finrank ComplexBase (complexTower 0) ≠
      Module.finrank ComplexBase (complexTower 1)
    rw [golden_cubic_block_positive_root_tower_degree 0,
      golden_cubic_block_positive_root_tower_degree 1]
    norm_num

register_information_theorem golden_cubic_block_positive_root_tower_degree in arena
  readout via (realize signature
    (fun _ _ J => Module.finrank ComplexBase (complexTower J))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration


end
end Reg.D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
