/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneCycleBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneCycleBlocks
   mirror-E: none(waiver:monotone-cycle-block-obstruction)
   anchors: []
   utility: none
   digest: A monotone cycle in a multipartite ordered graph requires one block per vertex. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyBlocks
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyExtremal
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPermutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs

theorem block_cycle_avoiding {b n d : ℕ} (hb : 2 ≤ b) (hd : 0 < d)
    (hn : n ≤ d * (b - 1)) :
    ¬DihedralEmbeddable (monoCycle b)
      (SimpleGraph.fromRel fun x y : Fin n => x.val / d = y.val / d)ᶜ := by
  classical
  rintro ⟨s, refl, ψ, hψ, hcycle⟩
  have adj : ∀ x y : Fin b, (monoCycle b).Adj x y ↔
      Nat.dist x.val y.val = 1 ∨ Nat.dist x.val y.val = b - 1 := by
    intro x y
    have hx := x.isLt
    have hy := y.isLt
    simp only [monoCycle, SimpleGraph.fromRel_adj]
    rw [Fin.ne_iff_vne]
    unfold Nat.dist
    omega
  have onto := Finite.surjective_of_injective (dihedralPerm_injective b s refl)
  have step : ∀ (j : ℕ) (hj : j + 1 < b),
      (ψ ⟨j, by omega⟩).val / d < (ψ ⟨j + 1, hj⟩).val / d := by
    intro j hj
    let i : Fin b := ⟨j, by omega⟩
    let k : Fin b := ⟨j + 1, hj⟩
    obtain ⟨x, hx⟩ := onto i
    obtain ⟨y, hy⟩ := onto k
    have near : Nat.dist i.val k.val = 1 ∨ Nat.dist i.val k.val = b - 1 := by
      left
      simp [i, k, Nat.dist]
    have edge := hcycle x y ((adj x y).mpr
      ((dihedralPerm_circular hb s refl x y).mpr (by simpa [hx, hy] using near)))
    rw [hx, hy] at edge
    exact block_blue_quotient_lt
      (hψ (show i < k by change j < j + 1; omega)) edge
  have bound : ∀ (j : ℕ) (hj : j < b), j ≤ (ψ ⟨j, hj⟩).val / d := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
        intro hj
        have h := step j hj
        have h' := ih (by omega)
        omega
  let last : Fin b := ⟨b - 1, by omega⟩
  have small : (ψ last).val / d < b - 1 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have h := lt_of_lt_of_le (ψ last).isLt hn
    simpa only [Nat.mul_comm] using h
  have large := bound (b - 1) (by omega)
  change b - 1 ≤ (ψ last).val / d at large
  omega

theorem path_cycle_bounds {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) :
    (∀ G : SimpleGraph (Fin (1 + (a - 1) * (b - 1))),
      CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable (monoCycle b) Gᶜ) ∧
    (∀ n : ℕ, n < 1 + (a - 1) * (b - 1) →
      ∃ G : SimpleGraph (Fin n),
        ¬DihedralEmbeddable (altPath a) G ∧ ¬DihedralEmbeddable (monoCycle b) Gᶜ) := by
  classical
  constructor
  · intro G
    by_cases hone : a = 1
    · subst a
      refine Or.inl ⟨0, fun _ => ⟨0, by simp⟩, ?_, ?_⟩
      · intro i j hij
        exact (ne_of_lt hij (Subsingleton.elim _ _)).elim
      · intro i j hij
        exact ((altPath 1).ne_of_adj hij (Subsingleton.elim _ _)).elim
    by_cases hpath : CyclicEmbeddable (altPath a) G
    · exact Or.inl hpath
    have sparse : ∀ (m : ℕ) (e : Fin m ↪o Fin (1 + (a - 1) * (b - 1))),
        2 * (G.comap e).edgeFinset.card ≤ (a - 2) * m := by
      intro m e
      apply extremal (by omega)
      rintro ⟨s, ψ, hψ, hadj⟩
      apply hpath
      exact ⟨s, e ∘ ψ, e.strictMono.comp hψ, hadj⟩
    obtain ⟨s, ψ, hψ, hclique⟩ := clique_of_sparse_induces (by omega) G sparse
    exact Or.inr ⟨s, ψ, hψ, fun i j hij =>
      hclique i j ((SimpleGraph.top_adj _ _).mpr ((monoCycle b).ne_of_adj hij))⟩
  · intro n hn
    by_cases hone : a = 1
    · subst a
      have hn0 : n = 0 := by simpa using hn
      subst n
      refine ⟨⊥, ?_, ?_⟩
      · rintro ⟨s, refl, ψ, _, _⟩
        exact Fin.elim0 (ψ ⟨0, by omega⟩)
      · rintro ⟨s, refl, ψ, _, _⟩
        exact Fin.elim0 (ψ ⟨0, by omega⟩)
    refine ⟨SimpleGraph.fromRel (fun x y : Fin n =>
      x.val / (a - 1) = y.val / (a - 1)), block_path_avoiding (by omega), ?_⟩
    exact block_cycle_avoiding hb (by omega) (by omega)

end D5.S3.Combinatorics.DihedralRamsey
