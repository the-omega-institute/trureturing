import D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower

open _root_.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ → Ambient
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ roots J => Module.finrank Base (tower roots J))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (roots : ℕ → Ambient)
    (hroots : ∀ j, 1 ≤ j →
      roots j ^ 3 = algebraMap Base Ambient (block j)) (J : ℕ),
    R.readout () roots J = 3 ^ J

private def witnessRoots (j : ℕ) : Ambient :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Base Ambient (block j)) (by decide : 0 < 3))

private theorem witnessRoots_spec (j : ℕ) :
    witnessRoots j ^ 3 = algebraMap Base Ambient (block j) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Base Ambient (block j)) (by decide : 0 < 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h witnessRoots (fun j _ => witnessRoots_spec j) 0
  norm_num [rejected, realize] at hzero

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro roots hroots J
    exact golden_cubic_block_kummer_tower_degree roots hroots J
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
    refine ⟨witnessRoots, 0, 1, ?_⟩
    change Module.finrank Base (tower witnessRoots 0) ≠
      Module.finrank Base (tower witnessRoots 1)
    rw [golden_cubic_block_kummer_tower_degree witnessRoots
      (fun j _ => witnessRoots_spec j) 0,
      golden_cubic_block_kummer_tower_degree witnessRoots
        (fun j _ => witnessRoots_spec j) 1]
    norm_num

register_information_theorem golden_cubic_block_kummer_tower_degree in arena
  readout via (realize signature
    (fun _ roots J => Module.finrank Base (tower roots J))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration


end
end Reg.D5.S3.Factorization.Galois.GoldenCubicBlockKummerTower
