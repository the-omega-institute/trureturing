/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicStarMon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicStarMon
   mirror-E: none(waiver:cyclic-star-monotone-ramsey)
   anchors: []
   utility: none
   digest: The exact cyclic Ramsey number of a star versus a monotone path. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyStar
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDensity
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicStarMon

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-- Conjecture 4.16 of arXiv:2604.16188. -/
theorem result : MonotoneRamseyDefs.claimCycStarMon := by
  classical
  intro a b ha hb
  let N := 1 + (a - 1) * (b - 2)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (startStar a) G ∨ CyclicEmbeddable (monoPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_cases hp : CyclicEmbeddable (startStar a) G
    · exact Or.inl hp
    have hd : ∀ v : Fin N, G.degree v ≤ a - 2 := by
      intro v
      by_contra hdegree
      apply hp
      exact (star_iff_degree (by omega : 2 ≤ a) false G).mpr ⟨v, by omega⟩
    have sparse : 2 * G.edgeFinset.card ≤ (a - 2) * N := by
      rw [← G.sum_degrees_eq_twice_card_edges]
      calc
        _ ≤ ∑ _ : Fin N, (a - 2) := Finset.sum_le_sum fun v _ => hd v
        _ = _ := by simp [Nat.mul_comm]
    exact Or.inr (MonotoneRamseyDensity.forces_monotone ha hb G sparse)
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    have red := block_star_red_avoiding (n := n) (by omega : 2 ≤ a)
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

end D5.S3.Combinatorics.DihedralRamsey.CyclicStarMon
