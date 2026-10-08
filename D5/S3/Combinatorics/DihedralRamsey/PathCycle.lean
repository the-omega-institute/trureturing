/- GID: D5/S3/Combinatorics/DihedralRamsey/PathCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/PathCycle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp dihedral Ramsey number for an alternating path and a monotone cycle. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneCycleBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.PathCycle

open DihedralRamseyDefs CyclicRamseyDefs

theorem result : CyclicRamseyDefs.claimPathCycle := by
  classical
  intro a b ha hb
  obtain ⟨hupper, hlower⟩ := path_cycle_bounds ha hb
  let N := 1 + (a - 1) * (b - 1)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    DihedralEmbeddable (altPath a) G ∨ DihedralEmbeddable (monoCycle b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    rcases hupper G with ⟨s, ψ, hψ, hadj⟩ | ⟨s, ψ, hψ, hadj⟩
    · exact Or.inl ⟨s, false, ψ, hψ, hadj⟩
    · exact Or.inr ⟨s, false, ψ, hψ, hadj⟩
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  obtain ⟨G, hp, hc⟩ := hlower (sInf S) (by omega)
  exact (Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩) G).elim hp hc

end D5.S3.Combinatorics.DihedralRamsey.PathCycle
