/- GID: D5/S3/Combinatorics/DihedralRamsey/PathPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/PathPath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact dihedral Ramsey number of two alternating paths. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPathPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.PathPath

open DihedralRamseyDefs
open Finset

/-- Damnjanović–Đorđević Conjecture 4.4. -/
theorem result : DihedralRamseyDefs.claimPathPath := by
  classical
  intro a b ha hb
  let N := a + b - 2 - a * b % 2
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    DihedralEmbeddable (altPath a) G ∨ DihedralEmbeddable (altPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_contra h
    obtain ⟨hA, hB⟩ := not_or.mp h
    exact path_pair_edge_contradiction ha hb G
      (extremal ha G (not_cyclic_of_not_dihedral G hA))
      (extremal hb Gᶜ (not_cyclic_of_not_dihedral Gᶜ hB))
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    obtain ⟨W, hA, hB⟩ := path_pair_lower_colouring ha hb
    let e : Fin n → Fin (N - 1) := fun i => ⟨i.val, by dsimp [N]; omega⟩
    have he : StrictMono e := fun _ _ hij => hij
    let G := W.comap e
    rcases hforce G with ⟨s, refl, ψ, hψ, hadj⟩ | ⟨s, refl, ψ, hψ, hadj⟩
    · exact hA ⟨s, refl, e ∘ ψ, he.comp hψ, fun i j hij => hadj i j hij⟩
    · apply hB
      refine ⟨s, refl, e ∘ ψ, he.comp hψ, ?_⟩
      intro i j hij
      obtain ⟨hne, hnot⟩ := (SimpleGraph.compl_adj _ _ _).mp (hadj i j hij)
      exact (SimpleGraph.compl_adj _ _ _).mpr ⟨he.injective.ne hne, hnot⟩
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  exact lower (sInf S) (by omega) (Nat.sInf_mem ⟨N, upper⟩)

end D5.S3.Combinatorics.DihedralRamsey.PathPath
