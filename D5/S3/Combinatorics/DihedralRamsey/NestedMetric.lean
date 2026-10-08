/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedMetric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedMetric
   mirror-E: none(waiver:metric-lower-constructions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Dist]
   utility: none
   digest: Circular distance bounds obstruct rank-reflection nested matchings. -/

import Mathlib.Data.Nat.Dist
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyOrder
import D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedMetric

/-- The two innermost gaps give the far bound; an antipodal pair gives the short bound. -/
theorem reflection_metric_bounds {k n : ℕ} (hkpos : 0 < k)
    (ψ : Fin (2 * k) → Fin n) (hψ : StrictMono ψ) (c : Fin (2 * k))
    (hc : c.val % 2 = 1) :
    (∀ t, k % 2 = 1 →
      (∀ i j : Fin (2 * k), (i.val + j.val) % (2 * k) = c.val →
        Nat.dist (ψ i).val (ψ j).val ≤ t ∨
          n - Nat.dist (ψ i).val (ψ j).val ≤ t) → k ≤ t) ∧
    (∀ T, (∀ i j : Fin (2 * k), (i.val + j.val) % (2 * k) = c.val →
      T ≤ Nat.dist (ψ i).val (ψ j).val ∧
        T ≤ n - Nat.dist (ψ i).val (ψ j).val) → 2 * k + 2 * T - 2 ≤ n) := by
  have stretch : ∀ x y : Fin (2 * k), x.val ≤ y.val →
      (ψ x).val + (y.val - x.val) ≤ (ψ y).val := by
    intro x y hxy
    have h := (circular_order_stretch ψ hψ x y).1
    have hmon : (ψ x).val ≤ (ψ y).val := hψ.monotone hxy
    rw [Nat.dist_eq_sub_of_le hxy, Nat.dist_eq_sub_of_le hmon] at h
    omega
  constructor
  · intro t hk hedges
    let u := if c.val < k then (c.val + k) / 2 else (c.val - k) / 2
    have hu : u < k := by
      have := c.isLt
      dsimp [u]
      split_ifs <;> omega
    let i : Fin (2 * k) := ⟨u, by omega⟩
    let j : Fin (2 * k) := ⟨u + k, by omega⟩
    have hsum : (i.val + j.val) % (2 * k) = c.val := by
      have := c.isLt
      dsimp [i, j, u]
      split_ifs with h
      · have hs : (c.val + k) / 2 + ((c.val + k) / 2 + k) = c.val + 2 * k := by
          omega
        rw [hs, Nat.add_mod]
        simp [Nat.mod_eq_of_lt c.isLt]
      · have hs : (c.val - k) / 2 + ((c.val - k) / 2 + k) = c.val := by omega
        rw [hs, Nat.mod_eq_of_lt c.isLt]
    have h₁ := stretch i j (by dsimp [i, j]; omega)
    let z : Fin (2 * k) := ⟨0, by omega⟩
    let w : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
    have h₂ := stretch z i (by dsimp [z, i]; omega)
    have h₃ := stretch j w (by change u + k ≤ 2 * k - 1; omega)
    have hw := (ψ w).isLt
    have hij : i ≤ j := by change u ≤ u + k; omega
    have hm : (ψ i).val ≤ (ψ j).val := hψ.monotone hij
    have he := hedges i j hsum
    rw [Nat.dist_eq_sub_of_le hm] at he
    simp only [i, j, Nat.add_sub_cancel_left] at h₁
    change (ψ z).val + u ≤ (ψ i).val at h₂
    change (ψ j).val + (2 * k - 1 - (u + k)) ≤ (ψ w).val at h₃
    dsimp only [i, j, z, w] at he hw h₂ h₃ hm
    rcases he with he | he <;> omega
  
  · intro T hedges
    let p := (c.val + 1) / 2
    have hp : 1 ≤ p ∧ p ≤ k ∧ c.val = 2 * p - 1 := by
      have := c.isLt
      dsimp [p]
      omega
    let z : Fin (2 * k) := ⟨0, by omega⟩
    let w : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
    let i : Fin (2 * k) := ⟨p - 1, by omega⟩
    let j : Fin (2 * k) := ⟨p, by omega⟩
    have hs : (i.val + j.val) % (2 * k) = c.val := by
      have he : i.val + j.val = c.val := by change p - 1 + p = c.val; omega
      rw [he, Nat.mod_eq_of_lt c.isLt]
    have hij : (ψ i).val ≤ (ψ j).val :=
      hψ.monotone (show i ≤ j by change p - 1 ≤ p; omega)
    have hgap := (hedges i j hs).1
    rw [Nat.dist_eq_sub_of_le hij] at hgap
    have hstart := stretch z i (by change 0 ≤ p - 1; omega)
    have hw := (ψ w).isLt
    by_cases hpk : p = k
    · have hs' : (z.val + w.val) % (2 * k) = c.val := by
        have he : z.val + w.val = c.val := by change 0 + (2 * k - 1) = c.val; omega
        rw [he, Nat.mod_eq_of_lt c.isLt]
      have hzw : (ψ z).val ≤ (ψ w).val :=
        hψ.monotone (show z ≤ w by change 0 ≤ 2 * k - 1; omega)
      have hend := (hedges z w hs').2
      rw [Nat.dist_eq_sub_of_le hzw] at hend
      have hrest := stretch j w (by change p ≤ 2 * k - 1; omega)
      change (ψ z).val + (p - 1) ≤ (ψ i).val at hstart
      change (ψ j).val + (2 * k - 1 - p) ≤ (ψ w).val at hrest
      omega
    · have hpk' : p < k := by omega
      let i' : Fin (2 * k) := ⟨p + k - 1, by omega⟩
      let j' : Fin (2 * k) := ⟨p + k, by omega⟩
      have hs' : (i'.val + j'.val) % (2 * k) = c.val := by
        have he : i'.val + j'.val = c.val + 2 * k := by
          change p + k - 1 + (p + k) = c.val + 2 * k
          omega
        rw [he, Nat.add_mod]
        simp [Nat.mod_eq_of_lt c.isLt]
      have hij' : (ψ i').val ≤ (ψ j').val :=
        hψ.monotone (show i' ≤ j' by change p + k - 1 ≤ p + k; omega)
      have hgap' := (hedges i' j' hs').1
      rw [Nat.dist_eq_sub_of_le hij'] at hgap'
      have hmiddle := stretch j i' (by change p ≤ p + k - 1; omega)
      have hrest := stretch j' w (by change p + k ≤ 2 * k - 1; omega)
      change (ψ z).val + (p - 1) ≤ (ψ i).val at hstart
      change (ψ j).val + (p + k - 1 - p) ≤ (ψ i').val at hmiddle
      change (ψ j').val + (2 * k - 1 - (p + k)) ≤ (ψ w).val at hrest
      omega

end D5.S3.Combinatorics.DihedralRamsey.NestedMetric
