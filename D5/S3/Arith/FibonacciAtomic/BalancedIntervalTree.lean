/- GID: D5/S3/Arith/FibonacciAtomic/BalancedIntervalTree
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/BalancedIntervalTree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Ordered bisection preserves all node blocks and attains logarithmic height. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.BalancedIntervalTree

open FirstRejectionCutCapacity (interval)
open TreeMessageRealization (Tree leaf fork leaves Full subtrees height)

/-- Bisection puts the larger half first. Every node is an interval; a node
whose left endpoint differs from its ancestor's occupies at most half that
ancestor's interval. The tree has the least possible logarithmic height. -/
theorem result (k l w : ℕ) (hw : 0 < w) (hbound : l + w ≤ k + 1) :
    ∃ t : TreeMessageRealization.Tree (Fin (k + 1)), Full t ∧ leaves t = interval k l (l + w) ∧
      height t = Nat.clog 2 w ∧
      ∀ s ∈ subtrees t, ∃ a b : ℕ, l ≤ a ∧ a < b ∧ b ≤ l + w ∧
        leaves s = interval k a b ∧ (a = l ∨ b - a ≤ w / 2) := by
  classical
  induction w using Nat.strong_induction_on generalizing l with
  | h w ih =>
    by_cases hone : w = 1
    · subst w
      let i : Fin (k + 1) := ⟨l, by omega⟩
      have hleaves : leaves (leaf i) = interval k l (l + 1) := by
        ext j
        simp only [leaves, Finset.mem_singleton, interval, Finset.mem_filter,
          Finset.mem_univ, true_and, Fin.ext_iff]
        dsimp [i]
        omega
      refine ⟨leaf i, by simp [Full], hleaves, by simp [height], ?_⟩
      intro s hs
      have he : s = leaf i := by simpa [subtrees] using hs
      subst s
      exact ⟨l, l + 1, le_rfl, by omega, le_rfl, hleaves, Or.inl rfl⟩
    · let u := (w + 1) / 2
      let v := w / 2
      have hu : 0 < u := by dsimp [u]; omega
      have hv : 0 < v := by dsimp [v]; omega
      have hul : u < w := by dsimp [u]; omega
      have hvl : v < w := by dsimp [v]; omega
      have huv : u + v = w := by dsimp [u, v]; omega
      have hvu : v ≤ u := by dsimp [u, v]; omega
      obtain ⟨L, hL, hLA, hLH, hLS⟩ := ih u hul l hu (by omega)
      obtain ⟨R, hR, hRA, hRH, hRS⟩ := ih v hvl (l + u) hv (by omega)
      have hdisjoint : Disjoint (leaves L) (leaves R) := by
        rw [hLA, hRA]
        apply Finset.disjoint_left.mpr
        intro i hi hj
        simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        omega
      have hleaves : leaves (fork L R) = interval k l (l + w) := by
        simp only [leaves, hLA, hRA]
        ext i
        simp only [Finset.mem_union, interval, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hh : height (fork L R) = Nat.clog 2 w := by
        have hLp : 0 < L.height := by
          cases L with
          | nil => simp [Full] at hL
          | node a l r => simp only [BinaryTree.height]; omega
        have hRp : 0 < R.height := by
          cases R with
          | nil => simp [Full] at hR
          | node a l r => simp only [BinaryTree.height]; omega
        have hLheight : L.height = Nat.clog 2 u + 1 := by
          unfold height at hLH
          omega
        have hRheight : R.height = Nat.clog 2 v + 1 := by
          unfold height at hRH
          omega
        have hm : Nat.clog 2 v ≤ Nat.clog 2 u := Nat.clog_mono_right 2 hvu
        rw [height, fork, BinaryTree.height, hLheight, hRheight,
          max_eq_left (by omega), Nat.add_sub_cancel]
        simpa [u] using (Nat.clog_of_one_lt (by decide : 1 < 2)
          (show 1 < w by omega)).symm
      refine ⟨fork L R, ⟨hL, hR, hdisjoint⟩, hleaves, hh, ?_⟩
      intro s hs
      simp only [fork, subtrees, Finset.mem_insert, Finset.mem_union] at hs
      rcases hs with rfl | hs | hs
      · exact ⟨l, l + w, le_rfl, by omega, le_rfl, hleaves, Or.inl rfl⟩
      · obtain ⟨a, b, ha, hab, hb, hsa, hshort⟩ := hLS s hs
        refine ⟨a, b, ha, hab, by omega, hsa, ?_⟩
        rcases hshort with he | hshort
        · exact Or.inl he
        · right
          dsimp [u, v] at *
          omega
      · obtain ⟨a, b, ha, hab, hb, hsa, _⟩ := hRS s hs
        refine ⟨a, b, by omega, hab, by omega, hsa, Or.inr ?_⟩
        dsimp [v] at *
        omega

end D5.S3.Arith.FibonacciAtomic.BalancedIntervalTree
