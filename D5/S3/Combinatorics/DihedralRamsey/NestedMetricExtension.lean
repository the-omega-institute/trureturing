/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedMetricExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedMetricExtension
   mirror-E: none(waiver:universal-vertex-predecessor)
   anchors: []
   utility: none
   digest: A universal red vertex extends the even-pair nested matching lower colouring. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedMetricColouring
import D5.S3.Combinatorics.DihedralRamsey.NestedDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedMetricExtension

open DihedralRamseyDefs CyclicRamseyDefs NestedRamseyDefs
open NestedMetricColouring NestedDeletion

/-- Adjoining a universal red vertex preserves the predecessor matching obstruction. -/
theorem matching_predecessor {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hkeven : k % 2 = 0) :
    ∃ G : SimpleGraph (Fin (2 * k + 2 * l - 4)),
      ¬CyclicEmbeddable (nestMatching (2 * k)) G ∧
      ¬CyclicEmbeddable (nestMatching (2 * l)) Gᶜ := by
  classical
  let n := 2 * k + 2 * l - 5
  obtain ⟨H, _, _, hred, hblue⟩ := metric_colouring (n := n) (t := k - 2) (by
    dsimp [n]
    omega)
  have hr : ¬CyclicEmbeddable (nestMatching (2 * (k - 1))) H := by
    have h := hred (by omega)
    have he : k - 2 + 1 = k - 1 := by omega
    rw [he] at h
    exact h
  have hb : ¬CyclicEmbeddable (nestMatching (2 * l)) Hᶜ := hblue l (by omega) (by
    dsimp [n]
    omega)
  let G : SimpleGraph (Fin (n + 1)) := SimpleGraph.fromRel fun x y =>
    x.val = n ∨ y.val = n ∨ ∃ (hx : x.val < n) (hy : y.val < n),
      H.Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩
  have hadj : ∀ x y, G.Adj x y ↔ x ≠ y ∧
      (x.val = n ∨ y.val = n ∨ ∃ (hx : x.val < n) (hy : y.val < n),
        H.Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩) := by
    intro x y
    simp only [G, SimpleGraph.fromRel_adj]
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      rcases h.2 with h | h
      · exact h
      · rcases h with h | h | ⟨hy, hx, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨hx, hy, h.symm⟩)
    · intro h
      exact ⟨h.1, Or.inl h.2⟩
  have hold : G.comap Fin.castSucc = H := by
    ext x y
    simp only [SimpleGraph.comap_adj]
    rw [hadj]
    constructor
    · intro h
      rcases h.2 with h | h | ⟨hx, hy, h⟩
      · have := x.isLt
        change x.val = n at h
        omega
      · have := y.isLt
        change y.val = n at h
        omega
      · exact h
    · intro h
      refine ⟨?_, Or.inr (Or.inr ⟨x.isLt, y.isLt, h⟩)⟩
      intro he
      exact h.ne (Fin.castSucc_injective n he)
  have hg : ¬CyclicEmbeddable (nestMatching (2 * k)) G := by
    intro h
    apply hr
    simpa only [hold] using delete_last (by omega) G h
  have hgc : ¬CyclicEmbeddable (nestMatching (2 * l)) Gᶜ := by
    rintro ⟨s, ψ, hψ, he⟩
    have below : ∀ i : Fin (2 * l), (ψ i).val < n := by
      intro i
      let inv : Fin (2 * l) := ⟨(i.val + (2 * l - s % (2 * l))) % (2 * l),
        Nat.mod_lt _ (by omega)⟩
      have hinv : dihedralPerm s false inv = i := by
        apply Fin.ext
        simp only [dihedralPerm, Bool.false_eq_true, ↓reduceIte, Fin.val_mk, inv]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [Nat.add_mod]
        have hcancel : (i.val + (2 * l - s % (2 * l)) + s % (2 * l)) %
            (2 * l) = i.val := by
          have hs := Nat.mod_lt s (show 0 < 2 * l by omega)
          have heq : i.val + (2 * l - s % (2 * l)) + s % (2 * l) =
              i.val + 2 * l := by omega
          rw [heq, Nat.add_mod]
          simp [Nat.mod_eq_of_lt i.isLt]
        simpa only [Nat.add_mod, Nat.mod_mod] using hcancel
      let j : Fin (2 * l) := ⟨2 * l - 1 - inv.val, by have := inv.isLt; omega⟩
      have hij : (nestMatching (2 * l)).Adj inv j := by
        simp only [nestMatching, SimpleGraph.fromRel_adj]
        have hneq : inv ≠ j := by
          intro heq
          have hval := congrArg Fin.val heq
          dsimp [j] at hval
          have := inv.isLt
          omega
        refine ⟨hneq, Or.inl ?_⟩
        dsimp [j]
        have := inv.isLt
        omega
      have hedge := (SimpleGraph.compl_adj _ _ _).mp (he inv j hij)
      rw [hinv] at hedge
      have hne : (ψ i).val ≠ n := by
        intro hn
        exact hedge.2 ((hadj _ _).mpr ⟨hedge.1, Or.inl hn⟩)
      have := (ψ i).isLt
      omega
    let χ : Fin (2 * l) → Fin n := fun i => ⟨(ψ i).val, below i⟩
    have hχ : StrictMono χ := by
      intro i j hij
      exact hψ hij
    apply hb
    refine ⟨s, χ, hχ, ?_⟩
    intro i j hij
    have hedge := (SimpleGraph.compl_adj _ _ _).mp (he i j hij)
    apply (SimpleGraph.compl_adj _ _ _).mpr
    constructor
    · intro hn
      apply hedge.1
      apply Fin.ext
      have hv := congrArg Fin.val hn
      exact hv
    · intro hH
      exact hedge.2 ((hadj _ _).mpr
        ⟨hedge.1, Or.inr (Or.inr ⟨below _, below _, hH⟩)⟩)
  have hn : n + 1 = 2 * k + 2 * l - 4 := by dsimp [n]; omega
  exact hn ▸ ⟨G, hg, hgc⟩

end D5.S3.Combinatorics.DihedralRamsey.NestedMetricExtension
