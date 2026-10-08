/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicCyclePath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicCyclePath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp cyclic Ramsey number for a monotone cycle and an alternating path. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneCycleBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicCyclePath

open DihedralRamseyDefs CyclicRamseyDefs

theorem result : CyclicRamseyDefs.claimCycCyclePath := by
  classical
  intro a b ha hb
  obtain ⟨hupper, hlower⟩ := path_cycle_bounds hb ha
  let N := 1 + (a - 1) * (b - 1)
  have hN : 1 + (b - 1) * (a - 1) = N := by
    dsimp [N]
    rw [Nat.mul_comm]
  rw [hN] at hupper hlower
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (monoCycle a) G ∨ CyclicEmbeddable (altPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    have h := hupper Gᶜ
    rcases h with hp | hc
    · exact Or.inr hp
    · exact Or.inl (by simpa only [compl_compl] using hc)
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  obtain ⟨G, hp, hc⟩ := hlower (sInf S) (by dsimp [N] at hn; omega)
  have h := Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩) Gᶜ
  rcases h with ⟨s, ψ, hψ, hadj⟩ | ⟨s, ψ, hψ, hadj⟩
  · exact hc ⟨s, false, ψ, hψ, hadj⟩
  · apply hp
    refine ⟨s, false, ψ, hψ, ?_⟩
    simpa only [compl_compl] using hadj

end D5.S3.Combinatorics.DihedralRamsey.CyclicCyclePath
