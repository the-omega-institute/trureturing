/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyOrder
   mirror-E: none(waiver:cyclic-order-stretch)
   anchors: [mathlib/module/Mathlib.Order.Interval.Set.Monotone]
   utility: none
   digest: Increasing injections stretch both arcs of a finite circular order. -/

import Mathlib.Order.Interval.Set.Monotone
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyColoring
import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyRanks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

theorem circular_order_stretch {k m : ℕ} (ψ : Fin k → Fin m) (hψ : StrictMono ψ)
    (i j : Fin k) : Nat.dist i.val j.val ≤ Nat.dist (ψ i).val (ψ j).val ∧
      k - Nat.dist i.val j.val ≤ m - Nat.dist (ψ i).val (ψ j).val := by
  have stretch : ∀ x y : Fin k, x.val ≤ y.val →
      (ψ x).val + (y.val - x.val) ≤ (ψ y).val := by
    intro x y hxy
    let d := y.val - x.val
    let φ : ℕ → ℕ := fun t => if ht : t ≤ d then
      (ψ ⟨x.val + t, by have := y.isLt; dsimp [d] at ht; omega⟩).val - (ψ x).val
      else 0
    have hφ : StrictMonoOn φ (Set.Iic d) := by
      intro u hu v hv huv
      simp only [Set.mem_Iic] at hu hv
      dsimp [φ]
      rw [dif_pos hu, dif_pos hv]
      have hh := hψ (show
          (⟨x.val + u, by have := y.isLt; dsimp [d] at hu; omega⟩ : Fin k) <
          ⟨x.val + v, by have := y.isLt; dsimp [d] at hv; omega⟩ by
        change x.val + u < x.val + v
        omega)
      have hbase := hψ.monotone (show x ≤
          (⟨x.val + u, by have := y.isLt; dsimp [d] at hu; omega⟩ : Fin k) by
        change x.val ≤ x.val + u
        omega)
      change (ψ _).val < (ψ _).val at hh
      change (ψ x).val ≤ (ψ _).val at hbase
      omega
    have h := StrictMonoOn.Iic_id_le hφ d le_rfl
    have he : (⟨x.val + d, by have := y.isLt; dsimp [d]; omega⟩ : Fin k) = y := by
      apply Fin.ext
      dsimp [d]
      omega
    simp only [φ, dif_pos (le_refl d), he] at h
    have hm : (ψ x).val ≤ (ψ y).val := hψ.monotone hxy
    dsimp [d] at h
    omega
  have bound : ∀ x y : Fin k, x.val ≤ y.val →
      y.val - x.val ≤ (ψ y).val - (ψ x).val ∧
      k - (y.val - x.val) ≤ m - ((ψ y).val - (ψ x).val) := by
    intro x y hxy
    have h₁ := stretch x y hxy
    let z : Fin k := ⟨0, by have := x.isLt; omega⟩
    let w : Fin k := ⟨k - 1, by have := x.isLt; omega⟩
    have h₂ := stretch z x (by dsimp [z]; omega)
    have h₃ := stretch y w (by have := y.isLt; dsimp [w]; omega)
    have h₄ := (ψ w).isLt
    dsimp [z, w] at h₂ h₃
    constructor <;> omega
  rcases le_total i.val j.val with hij | hji
  · obtain ⟨h₁, h₂⟩ := bound i j hij
    rw [Nat.dist_eq_sub_of_le hij,
      Nat.dist_eq_sub_of_le (by have := hψ.monotone hij; exact this)]
    exact ⟨h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := bound j i hji
    rw [Nat.dist_comm i.val j.val, Nat.dist_comm (ψ i).val (ψ j).val,
      Nat.dist_eq_sub_of_le hji,
      Nat.dist_eq_sub_of_le (by have := hψ.monotone hji; exact this)]
    exact ⟨h₁, h₂⟩

end D5.S3.Combinatorics.DihedralRamsey
