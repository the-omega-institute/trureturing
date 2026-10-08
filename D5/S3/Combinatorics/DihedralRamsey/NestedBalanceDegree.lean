/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedBalanceDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedBalanceDegree
   mirror-E: none(waiver:matching-balance-degree)
   anchors: []
   utility: none
   digest: Full reflection balance forces a constant degree divisible by four. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedBalanceSlide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedBalanceDegree

open scoped BigOperators
open NestedBalanceSlide NestedBalanceParity

/-- Balanced full matchings impose a constant fourfold row sum on their colour matrix. -/
theorem full_balance_degree {m r : ℕ} (hm : 0 < m) (heven : m % 2 = 0)
    (C : ℕ → ℕ → ℕ) (hC : ∀ x y, C x y = C y x) (hdiag : ∀ x, C x x = 0)
    (balanced : ∀ (h : Fin (2 * m + 1)) (c : Fin (2 * m)), c.val % 2 = 1 →
      (∑ i : Fin (2 * m), C (h.succAbove i).val (h.succAbove (c - i)).val) = 2 * r) :
    (4 ∣ ∑ d ∈ Finset.range (2 * m), C 0 (d + 1)) ∧
      ∀ v < 2 * m + 1,
        (∑ d ∈ Finset.range (2 * m + 1), C v d) =
          ∑ d ∈ Finset.range (2 * m), C 0 (d + 1) := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  have before : ∀ x j : ℕ, x < j → j < 2 * m → (x + j) % 2 = 1 →
      C x j = C x (j + 1) := by
    intro x j hx hj hp
    let i' : Fin (2 * m) := ⟨x, by omega⟩
    let j' : Fin (2 * m) := ⟨j, hj⟩
    have hh := adjacent_hole_exchange hm (fun u v => C u.val v.val)
      (fun u v => hC u.val v.val) balanced i' j' hp
    have hi' : i'.castSucc < j'.succ := by
      change x < j + 1
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hi'] at hh
    exact hh
  have after : ∀ x j : ℕ, j + 1 < x → x < 2 * m + 1 → (x + j) % 2 = 0 →
      C x j = C x (j + 1) := by
    intro x j hx hj hp
    let i' : Fin (2 * m) := ⟨x - 1, by omega⟩
    let j' : Fin (2 * m) := ⟨j, by omega⟩
    have hi : (i'.val + j'.val) % 2 = 1 := by dsimp [i', j']; omega
    have hh := adjacent_hole_exchange hm (fun u v => C u.val v.val)
      (fun u v => hC u.val v.val) balanced i' j' hi
    have hi' : j'.succ ≤ i'.castSucc := by
      change j + 1 ≤ x - 1
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hi'] at hh
    have hx' : i'.succ.val = x := by dsimp [i']; omega
    simpa only [hx', Fin.val_castSucc, Fin.val_succ] using hh
  have oddshift : ∀ x y : ℕ, x < y → y + 1 < 2 * m + 1 → (x + y) % 2 = 1 →
      C x y = C (x + 1) (y + 1) := by
    intro x y hxy hy hp
    calc
      C x y = C x (y + 1) := before x y hxy (by omega) hp
      _ = C (y + 1) x := hC _ _
      _ = C (y + 1) (x + 1) := after (y + 1) x (by omega) hy (by omega)
      _ = C (x + 1) (y + 1) := hC _ _
  have shift : ∀ x y : ℕ, x < y → y + 1 < 2 * m + 1 →
      C x y = C (x + 1) (y + 1) := by
    intro x y hxy hy
    by_cases hp : (x + y) % 2 = 1
    · exact oddshift x y hxy hy hp
    · have hgap : x + 1 < y := by omega
      calc
        C x y = C x (y - 1) := by
          have hh := (before x (y - 1) (by omega) (by omega) (by omega)).symm
          simpa only [show y - 1 + 1 = y by omega] using hh
        _ = C (x + 1) y := by
          have hh := oddshift x (y - 1) (by omega) (by omega) (by omega)
          simpa only [show y - 1 + 1 = y by omega] using hh
        _ = C (x + 1) (y + 1) := before (x + 1) y hgap (by omega) (by omega)
  have base : ∀ x y : ℕ, x < y → y < 2 * m + 1 → C x y = C 0 (y - x) := by
    intro x
    induction x with
    | zero => intro y _ _; simp
    | succ x ih =>
      intro y hxy hy
      have hh := shift x (y - 1) (by omega) (by omega)
      rw [show y - 1 + 1 = y by omega] at hh
      rw [← hh, ih (y - 1) (by omega) (by omega)]
      congr 1
      omega
  have pair : ∀ t < m, C 0 (2 * t + 1) = C 0 (2 * t + 2) := by
    intro t ht
    exact before 0 (2 * t + 1) (by omega) (by omega) (by omega)
  have oddreflect : ∀ d, 1 ≤ d → d < 2 * m → d % 2 = 1 →
      C 0 d = C 0 (2 * m - d) := by
    intro d hd hdm hp
    let i' : Fin (2 * m) := ⟨d, hdm⟩
    have hh := wrap_hole_exchange hm (fun u v => C u.val v.val)
      (fun u v => hC u.val v.val) balanced i' hp
    exact hh.trans ((hC _ _).trans (base d (2 * m) hdm (by omega)))
  have reflected : ∀ d, 1 ≤ d → d ≤ 2 * m → C 0 d = C 0 (2 * m + 1 - d) := by
    intro d hd hdm
    by_cases hp : d % 2 = 1
    · have hlt : d < 2 * m := by omega
      have hh := oddreflect d hd hlt hp
      have hpair := pair ((2 * m - d) / 2) (by omega)
      have he : 2 * ((2 * m - d) / 2) + 1 = 2 * m - d := by omega
      rw [he] at hpair
      rw [hh, hpair]
      congr 1
      omega
    · have hpair := pair ((d - 1) / 2) (by omega)
      have he : 2 * ((d - 1) / 2) + 1 = d - 1 := by omega
      rw [he, show 2 * ((d - 1) / 2) + 2 = d by omega] at hpair
      rw [← hpair, oddreflect (d - 1) (by omega) (by omega) (by omega)]
      congr 1
      omega
  refine ⟨paired_offset_degree heven (C 0) pair reflected, ?_⟩
  intro v hv
  rw [show 2 * m + 1 = v + (2 * m + 1 - v) by omega, Finset.sum_range_add]
  have left : (∑ d ∈ Finset.range v, C v d) =
      ∑ d ∈ Finset.range v, C 0 (2 * m + 1 - v + d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    rw [hC v d, base d v hd' hv, reflected (v - d) (by omega) (by omega)]
    congr 1
    omega
  have right : (∑ d ∈ Finset.range (2 * m + 1 - v), C v (v + d)) =
      ∑ d ∈ Finset.range (2 * m - v), C 0 (d + 1) := by
    rw [show 2 * m + 1 - v = (2 * m - v) + 1 by omega,
      Finset.sum_range_succ']
    simp only [Nat.add_zero, hdiag, zero_add]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    rw [base v (v + (d + 1)) (by omega) (by omega)]
    congr 1
    omega
  rw [left, right]
  have hshift : (∑ d ∈ Finset.range v, C 0 (2 * m + 1 - v + d)) =
      ∑ d ∈ Finset.range v, C 0 (2 * m - v + d + 1) := by
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    omega
  rw [hshift]
  conv_rhs => rw [show 2 * m = (2 * m - v) + v by omega, Finset.sum_range_add]
  omega

end D5.S3.Combinatorics.DihedralRamsey.NestedBalanceDegree
