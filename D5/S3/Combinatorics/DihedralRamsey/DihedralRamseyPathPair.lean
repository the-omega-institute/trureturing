/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyPathPair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyPathPair
   mirror-E: none(waiver:shared-path-pair-estimates)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Parity-sensitive edge estimates and sharp path-pair avoiding colourings. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyExtremal
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyCircular
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs CyclicRamseyDefs Finset

/-- The two edge bounds contradict the complete-graph edge count, including odd parity. -/
theorem path_pair_edge_contradiction {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (G : SimpleGraph (Fin (a + b - 2 - a * b % 2)))
    [DecidableRel G.Adj]
    (hA : 2 * G.edgeFinset.card ≤ (a - 2) * (a + b - 2 - a * b % 2))
    (hB : 2 * Gᶜ.edgeFinset.card ≤ (b - 2) * (a + b - 2 - a * b % 2)) : False := by
  classical
  let N := a + b - 2 - a * b % 2
  change 2 * G.edgeFinset.card ≤ (a - 2) * N at hA
  change 2 * Gᶜ.edgeFinset.card ≤ (b - 2) * N at hB
  have hdeg : ∀ v : Fin N, G.degree v + Gᶜ.degree v = N - 1 := by
    intro v
    have hl := G.degree_lt_card_verts v
    rw [G.degree_compl, Fintype.card_fin]
    simp only [Fintype.card_fin] at hl
    omega
  have heq : 2 * G.edgeFinset.card + 2 * Gᶜ.edgeFinset.card = N * (N - 1) := by
    rw [← G.sum_degrees_eq_twice_card_edges, ← Gᶜ.sum_degrees_eq_twice_card_edges,
      ← Finset.sum_add_distrib]
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, N]
  have hp : a * b % 2 ≤ 1 := by omega
  have hN : 0 < N := by dsimp [N]; omega
  by_cases hpar : a * b % 2 = 0
  · have he : N = a + b - 2 := by simp [N, hpar]
    have hsum : a + b = N + 2 := by omega
    have ha' : a - 2 + 2 = a := by omega
    have hb' : b - 2 + 2 = b := by omega
    have hN' : N - 1 + 1 = N := by omega
    nlinarith
  · have hpar' : a * b % 2 = 1 := by omega
    have hpa : a % 2 = 1 := by
      rw [Nat.mul_mod] at hpar'
      have : a % 2 < 2 := Nat.mod_lt _ (by omega)
      have : b % 2 < 2 := Nat.mod_lt _ (by omega)
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · simp [h] at hpar'
      · exact h
    have hpb : b % 2 = 1 := by
      rw [Nat.mul_mod, hpa] at hpar'
      simpa using hpar'
    have hNr : N = a + b - 3 := by dsimp [N]; omega
    have hNodd : N % 2 = 1 := by omega
    have hpa' : (a - 2) % 2 = 1 := by omega
    have hpb' : (b - 2) % 2 = 1 := by omega
    have hprodA : ((a - 2) * N) % 2 = 1 := by
      simp [Nat.mul_mod, hpa', hNodd]
    have hprodB : ((b - 2) * N) % 2 = 1 := by
      simp [Nat.mul_mod, hpb', hNodd]
    have hevA : (2 * G.edgeFinset.card) % 2 = 0 := by omega
    have hevB : (2 * Gᶜ.edgeFinset.card) % 2 = 0 := by omega
    have hAA : 2 * G.edgeFinset.card + 1 ≤ (a - 2) * N := by omega
    have hBB : 2 * Gᶜ.edgeFinset.card + 1 ≤ (b - 2) * N := by omega
    have hsum : a + b = N + 3 := by omega
    have ha' : a - 2 + 2 = a := by omega
    have hb' : b - 2 + 2 = b := by omega
    have hN' : N - 1 + 1 = N := by omega
    nlinarith

set_option maxHeartbeats 1000000 in
-- Parity-dependent circular colourings and both boundary orders are combined.
/-- Sharp avoiding colourings for every pair of alternating-path orders. -/
theorem path_pair_lower_colouring {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ W : SimpleGraph (Fin (a + b - 2 - a * b % 2 - 1)),
      ¬DihedralEmbeddable (altPath a) W ∧ ¬DihedralEmbeddable (altPath b) Wᶜ := by
  classical
  let N := a + b - 2 - a * b % 2
  have no_edge (c : ℕ) (hc : 2 ≤ c) :
      ¬DihedralEmbeddable (altPath c) (⊥ : SimpleGraph (Fin (N - 1))) := by
    rintro ⟨s, refl, ψ, hψ, hE⟩
    let i : Fin c := ⟨0, by omega⟩
    let j : Fin c := ⟨c - 1, by omega⟩
    have hadj : (altPath c).Adj i j := by
      change i ≠ j ∧ _
      refine ⟨?_, Or.inl ⟨0, by omega, rfl, ?_⟩⟩
      · intro he
        have := congrArg Fin.val he
        dsimp [i, j] at this
        omega
      · change c - 1 = altVertex c 1
        simp [altVertex]
    exact hE i j hadj
  have large_pattern (c : ℕ) (G : SimpleGraph (Fin (N - 1))) (hc : N - 1 < c) :
      ¬DihedralEmbeddable (altPath c) G := by
    rintro ⟨s, refl, ψ, hψ, hE⟩
    have hsize := Fintype.card_le_of_injective ψ hψ.injective
    simp only [Fintype.card_fin] at hsize
    omega
  have witness : ∃ W : SimpleGraph (Fin (N - 1)),
      ¬DihedralEmbeddable (altPath a) W ∧ ¬DihedralEmbeddable (altPath b) Wᶜ := by
    by_cases ha2 : a = 2
    · refine ⟨⊥, no_edge a ha, large_pattern b _ ?_⟩
      dsimp [N]
      subst a
      omega
    by_cases hb2 : b = 2
    · refine ⟨⊤, large_pattern a _ ?_, ?_⟩
      · dsimp [N]
        subst b
        have hmod : a * 2 % 2 = 0 := by omega
        omega
      · simpa only [compl_top] using no_edge b hb
    have ha3 : 3 ≤ a := by omega
    have hb3 : 3 ≤ b := by omega
    by_cases hpa : a % 2 = 0
    · let r := (a - 2) / 2
      have hpar : a * b % 2 = 0 := by simp [Nat.mul_mod, hpa]
      have hNr : N - 1 = 2 * r + b - 1 := by dsimp [N, r]; omega
      obtain ⟨W, hA, _, hB⟩ := short_circular_colouring
        (a := a) (n := N - 1) (r := r) (by dsimp [r]; omega) (by omega)
      exact ⟨W, hA, hB b hb3 (by omega)⟩
    by_cases hpb : b % 2 = 0
    · let r := (b - 2) / 2
      have hpar : a * b % 2 = 0 := by simp [Nat.mul_mod, hpb]
      have hNr : N - 1 = 2 * r + a - 1 := by dsimp [N, r]; omega
      obtain ⟨W, hB, _, hA⟩ := short_circular_colouring
        (a := b) (n := N - 1) (r := r) (by dsimp [r]; omega) (by omega)
      refine ⟨Wᶜ, hA a ha3 (by omega), ?_⟩
      simpa only [compl_compl] using hB
    · let r := (a - 3) / 2
      have hpa1 : a % 2 = 1 := by omega
      have hpb1 : b % 2 = 1 := by omega
      have hpar : a * b % 2 = 1 := by simp [Nat.mul_mod, hpa1, hpb1]
      have hNr : N - 1 = 2 * r + b - 1 := by dsimp [N, r]; omega
      obtain ⟨W, hA, _, hB⟩ := short_circular_colouring
        (a := a) (n := N - 1) (r := r) (by dsimp [r]; omega) (by omega)
      exact ⟨W, hA, hB b hb3 (by omega)⟩
  exact witness

/-- Any second path pattern with the same edge bound and dihedral transport has this value. -/
theorem path_pair_cyclic {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (H : SimpleGraph (Fin b))
    (hbound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ¬CyclicEmbeddable H G →
      ∀ [DecidableRel G.Adj], 2 * G.edgeFinset.card ≤ (b - 2) * n)
    (htransport : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      CyclicEmbeddable H G → DihedralEmbeddable (altPath b) G) :
    cyclicRamsey (altPath a) H = a + b - 2 - a * b % 2 := by
  classical
  let N := a + b - 2 - a * b % 2
  let S : Set ℕ := {n | ∀ G : SimpleGraph (Fin n),
    CyclicEmbeddable (altPath a) G ∨ CyclicEmbeddable H Gᶜ}
  have upper : N ∈ S := by
    intro G
    by_contra h
    obtain ⟨hA, hB⟩ := not_or.mp h
    exact path_pair_edge_contradiction ha hb G (extremal ha G hA) (hbound N Gᶜ hB)
  have lower : ∀ n, n < N → n ∉ S := by
    intro n hn hforce
    obtain ⟨W, hA, hB⟩ := path_pair_lower_colouring ha hb
    let e : Fin n → Fin (N - 1) := fun i => ⟨i.val, by dsimp [N]; omega⟩
    have he : StrictMono e := fun _ _ hij => hij
    let G := W.comap e
    rcases hforce G with ⟨s, ψ, hψ, hadj⟩ | hblue
    · exact hA ⟨s, false, e ∘ ψ, he.comp hψ, fun i j hij => hadj i j hij⟩
    · obtain ⟨s, refl, ψ, hψ, hadj⟩ := htransport n Gᶜ hblue
      apply hB
      refine ⟨s, refl, e ∘ ψ, he.comp hψ, ?_⟩
      intro i j hij
      obtain ⟨hne, hnot⟩ := (SimpleGraph.compl_adj _ _ _).mp (hadj i j hij)
      exact (SimpleGraph.compl_adj _ _ _).mpr ⟨he.injective.ne hne, hnot⟩
  change sInf S = N
  apply Nat.le_antisymm (Nat.sInf_le upper)
  by_contra hn
  exact lower (sInf S) (by omega) (Nat.sInf_mem ⟨N, upper⟩)

end D5.S3.Combinatorics.DihedralRamsey
