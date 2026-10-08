/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyRanks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyRanks
   mirror-E: none(waiver:cyclic-rank-constructions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Dist]
   utility: none
   digest: The alternating rank sequence is a permutation with classified edge lengths. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyDefs
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs

/-- The alternating rank sequence is a permutation, with each possible edge length once. -/
theorem alternating_ranks (a : ℕ) :
    ∃ q : Fin a ≃ Fin a,
      (∀ j, (q j).val = altVertex a j.val) ∧
      (∀ j : ℕ, j + 1 < a →
        Nat.dist (altVertex a j) (altVertex a (j + 1)) = a - 1 - j) := by
  let f : Fin a → Fin a := fun j =>
    ⟨altVertex a j.val, by
      have hj := j.isLt
      unfold altVertex
      split_ifs <;> omega⟩
  let g : Fin a → Fin a := fun x =>
    ⟨if 2 * x.val < a then 2 * x.val else 2 * (a - 1 - x.val) + 1, by
      have hx := x.isLt
      split_ifs <;> omega⟩
  have hgf : ∀ j, g (f j) = j := by
    intro j
    apply Fin.ext
    have hj := j.isLt
    dsimp [f, g, altVertex]
    split_ifs <;> omega
  have hfg : ∀ x, f (g x) = x := by
    intro x
    apply Fin.ext
    have hx := x.isLt
    dsimp [f, g, altVertex]
    split_ifs <;> omega
  refine ⟨⟨f, g, hgf, hfg⟩, fun _ => rfl, ?_⟩
  intro j hj
  unfold altVertex Nat.dist
  split_ifs <;> omega

end D5.S3.Combinatorics.DihedralRamsey
