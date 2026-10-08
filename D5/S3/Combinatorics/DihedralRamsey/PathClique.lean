/- GID: D5/S3/Combinatorics/DihedralRamsey/PathClique
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/PathClique
   mirror-E: none(waiver:dihedral-path-clique-ramsey)
   anchors: []
   utility: none
   digest: Block obstructions and sharp alternating path versus clique Ramsey numbers. -/

import D5.S3.Combinatorics.DihedralRamsey.CyclicCliquePath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.PathClique

open DihedralRamseyDefs

/-- Damnjanović–Đorđević Conjecture 4.9. -/
theorem result : DihedralRamseyDefs.claimPathClique := by
  classical
  intro a b ha hb
  let N := 1 + (a - 1) * (b - 1)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    DihedralEmbeddable (altPath a) G ∨
      DihedralEmbeddable (⊤ : SimpleGraph (Fin b)) Gᶜ}
  have upper : N ∈ S := by
    have hc := CyclicCliquePath.core a b ha hb
    unfold CyclicRamseyDefs.cyclicRamsey at hc
    let T : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
        CyclicRamseyDefs.CyclicEmbeddable (altPath a) G ∨
        CyclicRamseyDefs.CyclicEmbeddable (⊤ : SimpleGraph (Fin b)) Gᶜ}
    change sInf T = N at hc
    have hnonempty : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty] at hc
      dsimp only [N] at hc
      omega
    have hm := Nat.sInf_mem hnonempty
    rw [hc] at hm
    intro G
    rcases hm G with ⟨s, ψ, hψ, he⟩ | ⟨s, ψ, hψ, he⟩
    · exact Or.inl ⟨s, false, ψ, hψ, he⟩
    · exact Or.inr ⟨s, false, ψ, hψ, he⟩
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    by_cases hsmall : a = 1 ∨ b = 1
    · have hn0 : n = 0 := by
        rcases hsmall with h | h <;> simp [N, h] at hn <;> omega
      subst n
      rcases hforce ⊥ with ⟨s, refl, ψ, _, _⟩ | ⟨s, refl, ψ, _, _⟩
      · exact Fin.elim0 (ψ ⟨0, by omega⟩)
      · exact Fin.elim0 (ψ ⟨0, by omega⟩)
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    exact (hforce G).elim (block_path_avoiding ha2)
      (block_clique_avoiding ha2 hb2 (by dsimp [N] at hn; omega))
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  exact lower (sInf S) (by omega) (Nat.sInf_mem ⟨N, upper⟩)

end D5.S3.Combinatorics.DihedralRamsey.PathClique
