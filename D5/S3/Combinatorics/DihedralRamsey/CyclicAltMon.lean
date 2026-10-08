/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicAltMon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicAltMon
   mirror-E: none(waiver:cyclic-alternating-monotone-ramsey)
   anchors: []
   utility: none
   digest: The exact cyclic Ramsey number of an alternating path versus a monotone path. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDensity
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicAltMon

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-- Conjecture 4.9 of arXiv:2604.16188. -/
theorem result : MonotoneRamseyDefs.claimCycAltMon := by
  classical
  intro a b ha hb
  let N := 1 + (a - 1) * (b - 2)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable (monoPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_cases hp : CyclicEmbeddable (altPath a) G
    · exact Or.inl hp
    exact Or.inr (MonotoneRamseyDensity.forces_monotone ha hb G
      (extremal (by omega) G hp))
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    have red := block_path_avoiding (n := n) (by omega : 2 ≤ a)
    have blue := block_mono_blue_avoiding (n := n) (d := a - 1)
      (by omega : 3 ≤ b) (by omega) (by dsimp [N] at hn; omega)
    rcases hforce G with ⟨s, ψ, hψ, he⟩ | ⟨s, ψ, hψ, he⟩
    · exact red ⟨s, false, ψ, hψ, he⟩
    · exact blue ⟨s, false, ψ, hψ, he⟩
  change sInf S = N
  apply le_antisymm (Nat.sInf_le upper)
  have hm := Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩)
  by_contra hlt
  exact lower _ (by omega) hm

end D5.S3.Combinatorics.DihedralRamsey.CyclicAltMon
