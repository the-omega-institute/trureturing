/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicCliquePath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicCliquePath
   mirror-E: none(waiver:dihedral-path-clique-ramsey)
   anchors: []
   utility: none
   digest: Block obstructions and sharp alternating path versus clique Ramsey numbers. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyBlocks
import D5.S3.Combinatorics.DihedralRamsey.CyclicRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyExtremal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicCliquePath

open DihedralRamseyDefs CyclicRamseyDefs

/-- The path-first form of the cyclic clique bound. -/
theorem core : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    cyclicRamsey (altPath a) (⊤ : SimpleGraph (Fin b)) = 1 + (a - 1) * (b - 1) := by
  classical
  intro a b ha hb
  let N := 1 + (a - 1) * (b - 1)
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (altPath a) G ∨
      CyclicEmbeddable (⊤ : SimpleGraph (Fin b)) Gᶜ}
  have singleton : ∀ (n : ℕ), 0 < n → ∀ (H : SimpleGraph (Fin 1))
      (G : SimpleGraph (Fin n)), CyclicEmbeddable H G := by
    intro n hn H G
    refine ⟨0, (fun _ => ⟨0, hn⟩), ?_, ?_⟩
    · intro i j hij
      exact (ne_of_lt hij (Subsingleton.elim _ _)).elim
    · intro i j hij
      exact (H.ne_of_adj hij (Subsingleton.elim _ _)).elim
  have upper : N ∈ S := by
    intro G
    by_cases hone : a = 1
    · subst a
      exact Or.inl (singleton N (by dsimp [N]; omega) _ _)
    by_cases hone : b = 1
    · subst b
      exact Or.inr (singleton N (by dsimp [N]; omega) _ _)
    by_cases hpath : CyclicEmbeddable (altPath a) G
    · exact Or.inl hpath
    refine Or.inr (clique_of_sparse_induces (by omega) G ?_)
    intro m e
    apply extremal (by omega)
    rintro ⟨s, ψ, hψ, hadj⟩
    apply hpath
    refine ⟨s, e ∘ ψ, e.strictMono.comp hψ, ?_⟩
    intro i j hij
    exact hadj i j hij
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    by_cases hsmall : a = 1 ∨ b = 1
    · have hn0 : n = 0 := by
        rcases hsmall with h | h <;> simp [N, h] at hn <;> omega
      subst n
      rcases hforce ⊥ with ⟨s, ψ, _, _⟩ | ⟨s, ψ, _, _⟩
      · exact Fin.elim0 (ψ ⟨0, by omega⟩)
      · exact Fin.elim0 (ψ ⟨0, by omega⟩)
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    let G := SimpleGraph.fromRel fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)
    have hpath := block_path_avoiding (n := n) ha2
    have hclique := block_clique_avoiding (n := n) ha2 hb2 (by dsimp [N] at hn; omega)
    rcases hforce G with ⟨s, ψ, hψ, he⟩ | ⟨s, ψ, hψ, he⟩
    · exact hpath ⟨s, false, ψ, hψ, he⟩
    · exact hclique ⟨s, false, ψ, hψ, he⟩
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  have hm := Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩)
  exact lower (sInf S) (by omega) hm

theorem cyclicRamsey_comm {a b : ℕ} (H : SimpleGraph (Fin a)) (J : SimpleGraph (Fin b)) :
    cyclicRamsey H J = cyclicRamsey J H := by
  unfold cyclicRamsey
  congr 1
  ext n
  constructor
  · intro h G
    rcases h Gᶜ with hH | hJ
    · exact Or.inr hH
    · simpa only [compl_compl] using Or.inl hJ
  · intro h G
    rcases h Gᶜ with hJ | hH
    · exact Or.inr hJ
    · simpa only [compl_compl] using Or.inl hH

theorem result : CyclicRamseyDefs.claimCycCliquePath := by
  intro a b ha hb
  rw [cyclicRamsey_comm]
  simpa [Nat.mul_comm] using core b a hb ha

end D5.S3.Combinatorics.DihedralRamsey.CyclicCliquePath
