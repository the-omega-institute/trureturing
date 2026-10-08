/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicMonMon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicMonMon
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact cyclic Ramsey number of two monotone paths. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyLayers
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicMonMon

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-- Bašić–Damnjanović–Stevanović–Stošić Conjecture 4.7. -/
theorem result : MonotoneRamseyDefs.claimCycMonMon := by
  classical
  intro a b ha hab
  let N := 1 + (a - 1) * (b - 2)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (monoPath a) G ∨ CyclicEmbeddable (monoPath b) Gᶜ}
  have upper : N ∈ S := monotone_monotone_forcing ha hab
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    rcases hforce G with ⟨s, ψ, hψ, he⟩ | ⟨s, ψ, hψ, he⟩
    · exact block_mono_red_avoiding (by omega) ⟨s, false, ψ, hψ, he⟩
    · apply block_mono_blue_avoiding (by omega) (by omega)
        (show n ≤ (a - 1) * (b - 2) from by dsimp [N] at hn; omega)
      exact ⟨s, false, ψ, hψ, he⟩
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  exact lower (sInf S) (by omega) (Nat.sInf_mem ⟨N, upper⟩)

end D5.S3.Combinatorics.DihedralRamsey.CyclicMonMon
