/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralAltMon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralAltMon
   mirror-E: none(waiver:dihedral-alternating-monotone-ramsey)
   anchors: []
   utility: none
   digest: The exact dihedral Ramsey number of an alternating path versus a monotone path. -/

import D5.S3.Combinatorics.DihedralRamsey.CyclicAltMon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.DihedralAltMon

open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-- Conjecture 4.6 of arXiv:2607.06817. -/
theorem result : MonotoneRamseyDefs.claimDihAltMon := by
  classical
  intro a b ha hb
  let N := 1 + (a - 1) * (b - 2)
  let C : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable (monoPath b) Gᶜ}
  have heq : sInf C = N := CyclicAltMon.result a b ha hb
  have hpos : 0 < sInf C := by rw [heq]; dsimp [N]; omega
  have forcing : N ∈ C := by
    have hm := Nat.sInf_mem (Nat.nonempty_of_pos_sInf hpos)
    simpa only [heq] using hm
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    DihedralEmbeddable (altPath a) G ∨ DihedralEmbeddable (monoPath b) Gᶜ}
  have upper : N ∈ S := by
    intro G
    rcases forcing G with ⟨s, ψ, hψ, hE⟩ | ⟨s, ψ, hψ, hE⟩
    · exact Or.inl ⟨s, false, ψ, hψ, hE⟩
    · exact Or.inr ⟨s, false, ψ, hψ, hE⟩
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    have red := block_path_avoiding (n := n) (by omega : 2 ≤ a)
    have blue := block_mono_blue_avoiding (n := n) (d := a - 1)
      (by omega : 3 ≤ b) (by omega) (by dsimp [N] at hn; omega)
    exact (hforce G).elim red blue
  change sInf S = N
  apply le_antisymm (Nat.sInf_le upper)
  have hm := Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩)
  by_contra hlt
  exact lower _ (by omega) hm

end D5.S3.Combinatorics.DihedralRamsey.DihedralAltMon
