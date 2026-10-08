/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicPathRevPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicPathRevPath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Fin.Rev]
   utility: none
   digest: Reversing the ambient cyclic order gives the reverse alternating path bound. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPathPair
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicPathRevPath

open DihedralRamseyDefs CyclicRamseyDefs

/-- Reversal conjugates a rotation to its inverse rotation. -/
theorem rev_rotation {b : ℕ} (s : ℕ) (i : Fin b) :
    (dihedralPerm s false i.rev).rev = dihedralPerm (b - s % b) false i := by
  apply Fin.ext
  have hi := i.isLt
  have hb := Fin.pos i
  have hs := Nat.mod_lt s hb
  simp only [Fin.val_rev, dihedralPerm, Bool.false_eq_true, ↓reduceIte]
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : b - (i.val + 1) < b)]
  have hm (x : ℕ) (hx : x < 2 * b) : x % b = if x < b then x else x - b := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hm (b - (i.val + 1) + s % b) (by omega), hm (i.val + (b - s % b)) (by omega)]
  split_ifs <;> omega

/-- Reflecting the alternating path gives the fixed reverse alternating path. -/
theorem revAltPath_adj {b : ℕ} (i j : Fin b) :
    (revAltPath b).Adj i j ↔ (altPath b).Adj i.rev j.rev := by
  have bound (t : ℕ) (ht : t < b) : altVertex b t < b := by
    unfold altVertex
    split_ifs <;> omega
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨Fin.rev_injective.ne hne, ?_⟩
    simp only [Fin.val_rev]
    rcases h with ⟨t, ht, hi, hj⟩ | ⟨t, ht, hj, hi⟩
    · exact Or.inl ⟨t, ht, by have := bound t (by omega); omega,
        by have := bound (t + 1) ht; omega⟩
    · exact Or.inr ⟨t, ht, by have := bound t (by omega); omega,
        by have := bound (t + 1) ht; omega⟩
  · rintro ⟨hne, h⟩
    refine ⟨fun he => hne (congrArg Fin.rev he), ?_⟩
    simp only [Fin.val_rev] at h
    rcases h with ⟨t, ht, hi, hj⟩ | ⟨t, ht, hj, hi⟩
    · exact Or.inl ⟨t, ht, by have := i.isLt; omega, by have := j.isLt; omega⟩
    · exact Or.inr ⟨t, ht, by have := j.isLt; omega, by have := i.isLt; omega⟩

/-- A forward path in the reversed ambient order is a reverse path in the original order. -/
theorem cyclic_reversed_order {b n : ℕ} (G : SimpleGraph (Fin n))
    (h : CyclicEmbeddable (altPath b) (G.comap Fin.rev)) :
    CyclicEmbeddable (revAltPath b) G := by
  obtain ⟨s, ψ, hψ, hadj⟩ := h
  let ψ' : Fin b → Fin n := fun i => (ψ i.rev).rev
  have hψ' : StrictMono ψ' := by
    intro i j hij
    exact Fin.rev_lt_rev.mpr (hψ (Fin.rev_lt_rev.mpr hij))
  refine ⟨b - s % b, ψ', hψ', ?_⟩
  intro i j hij
  have h := hadj i.rev j.rev ((revAltPath_adj i j).mp hij)
  change G.Adj ((ψ (dihedralPerm s false i.rev)).rev)
    ((ψ (dihedralPerm s false j.rev)).rev) at h
  simpa only [ψ', ← rev_rotation s i, ← rev_rotation s j, Fin.rev_rev] using h

/-- A cyclic reverse path is also a dihedral alternating path. -/
theorem dihedral_of_cyclic_reverse {b n : ℕ} (G : SimpleGraph (Fin n))
    (h : CyclicEmbeddable (revAltPath b) G) : DihedralEmbeddable (altPath b) G := by
  obtain ⟨s, ψ, hψ, hadj⟩ := h
  have hp (i : Fin b) : dihedralPerm s true i = dihedralPerm s false i.rev := by
    apply Fin.ext
    simp only [dihedralPerm, Fin.val_rev, Bool.false_eq_true,
      ↓reduceIte]
    congr 2
    omega
  refine ⟨s, true, ψ, hψ, ?_⟩
  intro i j hij
  rw [hp i, hp j]
  apply hadj i.rev j.rev
  apply (revAltPath_adj i.rev j.rev).mpr
  simpa only [Fin.rev_rev] using hij

/-- Bašić–Damnjanović–Stevanović–Stošić Conjecture 4.10. -/
theorem result : CyclicRamseyDefs.claimCycPathRevPath := by
  classical
  intro a b ha hb
  apply path_pair_cyclic ha hb (revAltPath b)
  · intro n G h _
    have hrev : ¬CyclicEmbeddable (altPath b) (G.comap Fin.rev) := by
      intro he
      exact h (cyclic_reversed_order G he)
    have hbound := extremal hb (G.comap Fin.rev) hrev
    have hcard := (SimpleGraph.Iso.comap Fin.revPerm G).card_edgeFinset_eq
    change 2 * (G.comap Fin.revPerm).edgeFinset.card ≤ (b - 2) * n at hbound
    rw [hcard] at hbound
    exact hbound
  · intro n G h
    exact dihedral_of_cyclic_reverse G h

end D5.S3.Combinatorics.DihedralRamsey.CyclicPathRevPath
