/- GID: D5/S3/Combinatorics/CyclicLatinEulerianRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicLatinEulerianRefutation
   mirror-E: none(waiver:direct-refutation-of-full-symmetry-claim)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: none
   digest: Cyclic column ascent vectors obstruct full coordinate symmetry at every order at least four. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Fin.NatCast

namespace D5.S3.Combinatorics.CyclicLatinEulerianRefutation

/-! Fixed public statement: Mirzavaziri–Yaqubi, "Cyclic Latin Eulerian Numbers", arXiv:2609.28808v1, Remark 3.9 asserts that the
    cyclic Latin Eulerian numbers are invariant under the full symmetric group acting on the ascent vector. We refute it.
    `colAscents` is the frozen definition from `D5.S3.Combinatorics.LatinEulerianDefs` (ascents of a column, top to bottom). -/
open D5.S3.Combinatorics.LatinEulerianMultiples (colAscents)

/-- The row-reordered cyclic square `L_π`: row `i` is row `π i` of `C(i, c) = i + c (mod n)`. -/
def cyclicSquare (n : ℕ) (π : Equiv.Perm (Fin n)) (i c : Fin n) : Fin n := π i + c

/-- The cyclic Latin Eulerian number `⟨⟨n k⟩⟩_c = #{π ∈ S_n : k_j(L_π) = k_j for all j}` (Definition 2.1). -/
def cyclicLatinEulerian (n : ℕ) (k : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ j, colAscents n (cyclicSquare n π) j = k j)).card

/-- Remark 3.9's asserted invariance under the full symmetric group acting on `k`. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ (k : Fin n → ℕ) (σ : Equiv.Perm (Fin n)),
    cyclicLatinEulerian n (k ∘ σ) = cyclicLatinEulerian n k

/-- Incrementing distinct residues changes their order only when one of them wraps. -/
private theorem pair_step {n : ℕ} (hn : 2 ≤ n) (x y : Fin n) (hxy : x ≠ y) :
    (if x + (⟨1, by omega⟩ : Fin n) < y + (⟨1, by omega⟩ : Fin n) then 1 else 0) +
        (if y.val = n - 1 then 1 else 0) =
      (if x < y then 1 else 0) + (if x.val = n - 1 then 1 else 0) := by
  have hinc (z : Fin n) :
      (z + (⟨1, by omega⟩ : Fin n)).val =
        if z.val = n - 1 then 0 else z.val + 1 := by
    rw [Fin.val_add_eq_ite]
    change (if n ≤ z.val + 1 then z.val + 1 - n else z.val + 1) =
      if z.val = n - 1 then 0 else z.val + 1
    split_ifs <;> omega
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  simp only [Fin.lt_def, hinc]
  by_cases hx : x.val = n - 1 <;> by_cases hy : y.val = n - 1 <;>
    simp [hx, hy] <;> omega

/-- A column shift changes the ascent count only if the wrapping symbol is at an endpoint row. -/
theorem shift_step {n : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    (c : Fin n) :
    colAscents n (cyclicSquare n π) (c + (⟨1, by omega⟩ : Fin n)) +
        (if (π ⟨n - 1, by omega⟩ + c).val = n - 1 then 1 else 0) =
      colAscents n (cyclicSquare n π) c +
        (if (π ⟨0, by omega⟩ + c).val = n - 1 then 1 else 0) := by
  classical
  let f : ℕ → ℕ := fun j =>
    if h : j + 1 < n then
      if π ⟨j, by omega⟩ + c < π ⟨j + 1, h⟩ + c then 1 else 0
    else 0
  let g : ℕ → ℕ := fun j =>
    if h : j + 1 < n then
      if π ⟨j, by omega⟩ + (c + (⟨1, by omega⟩ : Fin n)) <
          π ⟨j + 1, h⟩ + (c + (⟨1, by omega⟩ : Fin n)) then 1 else 0
    else 0
  let w : ℕ → ℕ := fun j =>
    if h : j < n then if (π ⟨j, h⟩ + c).val = n - 1 then 1 else 0 else 0
  have hf : colAscents n (cyclicSquare n π) c = ∑ j ∈ Finset.range (n - 1), f j := by
    simp only [colAscents, Finset.card_eq_sum_ones, Finset.sum_filter]
    conv_lhs => arg 1; rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hno : ¬ ∃ (h : n - 1 + 1 < n),
        cyclicSquare n π ⟨n - 1, by omega⟩ c <
          cyclicSquare n π ⟨n - 1 + 1, h⟩ c := by
      rintro ⟨h, _⟩
      omega
    rw [if_neg hno, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 < n := by have := Finset.mem_range.mp hj; omega
    simp [f, cyclicSquare, hj']
  have hg : colAscents n (cyclicSquare n π) (c + (⟨1, by omega⟩ : Fin n)) =
      ∑ j ∈ Finset.range (n - 1), g j := by
    simp only [colAscents, Finset.card_eq_sum_ones, Finset.sum_filter]
    conv_lhs => arg 1; rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hno : ¬ ∃ (h : n - 1 + 1 < n),
        cyclicSquare n π ⟨n - 1, by omega⟩ (c + (⟨1, by omega⟩ : Fin n)) <
          cyclicSquare n π ⟨n - 1 + 1, h⟩ (c + (⟨1, by omega⟩ : Fin n)) := by
      rintro ⟨h, _⟩
      omega
    rw [if_neg hno, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 < n := by have := Finset.mem_range.mp hj; omega
    simp [g, cyclicSquare, hj']
  have hp (j : ℕ) (hj : j ∈ Finset.range (n - 1)) :
      g j + w (j + 1) = f j + w j := by
    have hj' : j + 1 < n := by have := Finset.mem_range.mp hj; omega
    have hj0 : j < n := by omega
    have hne : (π ⟨j, hj0⟩ + c) ≠ (π ⟨j + 1, hj'⟩ + c) := by
      intro h
      have := π.injective (add_right_cancel h)
      have hv := congrArg Fin.val this
      simp at hv
    simpa [f, g, w, hj', hj0, cyclicSquare, add_assoc] using
      pair_step hn (π ⟨j, hj0⟩ + c) (π ⟨j + 1, hj'⟩ + c) hne
  have hsum :
      (∑ j ∈ Finset.range (n - 1), g j) +
          (∑ j ∈ Finset.range (n - 1), w (j + 1)) =
        (∑ j ∈ Finset.range (n - 1), f j) +
          (∑ j ∈ Finset.range (n - 1), w j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hp
  have htel :
      (∑ j ∈ Finset.range (n - 1), w (j + 1)) + w 0 =
        (∑ j ∈ Finset.range (n - 1), w j) + w (n - 1) := by
    have ha := Finset.sum_range_succ w (n - 1)
    have hb := Finset.sum_range_succ' w (n - 1)
    omega
  have hw0 : w 0 =
      (if (π ⟨0, by omega⟩ + c).val = n - 1 then 1 else 0) := by
    simp [w, show 0 < n by omega]
  have hwlast : w (n - 1) =
      (if (π ⟨n - 1, by omega⟩ + c).val = n - 1 then 1 else 0) := by
    simp [w, show n - 1 < n by omega]
  rw [hw0, hwlast] at htel
  rw [hf, hg]
  omega

/-- No row permutation can change its ascent count on three successive column shifts. -/
theorem no_three_changes {n : ℕ} (hn : 4 ≤ n) (π : Equiv.Perm (Fin n)) :
    let k := fun c => colAscents n (cyclicSquare n π) c
    k ⟨0, by omega⟩ = k ⟨1, by omega⟩ ∨
      k ⟨1, by omega⟩ = k ⟨2, by omega⟩ ∨
        k ⟨2, by omega⟩ = k ⟨3, by omega⟩ := by
  let z0 : Fin n := ⟨0, by omega⟩
  let z1 : Fin n := ⟨1, by omega⟩
  let z2 : Fin n := ⟨2, by omega⟩
  let z3 : Fin n := ⟨3, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  have hnxt (i : ℕ) (hi : i + 1 < n) :
      (⟨i, by omega⟩ : Fin n) + one = ⟨i + 1, hi⟩ := by
    apply Fin.ext
    rw [Fin.val_add_eq_of_add_lt (by simp [one]; omega)]
  have hwrap (c : Fin n)
      (hchange : colAscents n (cyclicSquare n π) (c + one) ≠
        colAscents n (cyclicSquare n π) c) :
      (π ⟨0, by omega⟩ + c).val = n - 1 ∨
        (π ⟨n - 1, by omega⟩ + c).val = n - 1 := by
    have hs := shift_step (by omega : 2 ≤ n) π c
    change colAscents n (cyclicSquare n π) (c + one) + _ = _ + _ at hs
    by_contra h
    push Not at h
    simp only [if_neg h.1, if_neg h.2, add_zero] at hs
    exact hchange hs
  by_contra h
  dsimp only at h
  push Not at h
  have hc0 : colAscents n (cyclicSquare n π) (z0 + one) ≠
      colAscents n (cyclicSquare n π) z0 := by
    rw [hnxt 0 (by omega)]
    exact Ne.symm h.1
  have hc1 : colAscents n (cyclicSquare n π) (z1 + one) ≠
      colAscents n (cyclicSquare n π) z1 := by
    rw [hnxt 1 (by omega)]
    exact Ne.symm h.2.1
  have hc2 : colAscents n (cyclicSquare n π) (z2 + one) ≠
      colAscents n (cyclicSquare n π) z2 := by
    rw [hnxt 2 (by omega)]
    exact Ne.symm h.2.2
  have hu (x : Fin n) (a b : Fin n) (hab : a ≠ b)
      (ha : (x + a).val = n - 1) (hb : (x + b).val = n - 1) : False := by
    exact hab (add_left_cancel (Fin.ext (ha.trans hb.symm)))
  have hz01 : z0 ≠ z1 := by simp [z0, z1, Fin.ext_iff]
  have hz02 : z0 ≠ z2 := by simp [z0, z2, Fin.ext_iff]
  have hz12 : z1 ≠ z2 := by simp [z1, z2, Fin.ext_iff]
  have hw0 := hwrap z0 hc0
  have hw1 := hwrap z1 hc1
  have hw2 := hwrap z2 hc2
  rcases hw0 with h0 | h0
  · rcases hw1 with h1 | h1
    · exact hu _ z0 z1 hz01 h0 h1
    · rcases hw2 with h2 | h2
      · exact hu _ z0 z2 hz02 h0 h2
      · exact hu _ z1 z2 hz12 h1 h2
  · rcases hw1 with h1 | h1
    · rcases hw2 with h2 | h2
      · exact hu _ z1 z2 hz12 h1 h2
      · exact hu _ z0 z2 hz02 h0 h2
    · exact hu _ z0 z1 hz01 h0 h1

/-- The full symmetric action fails at every order at least four. -/
theorem not_fully_symmetric (n : ℕ) (hn : 4 ≤ n) :
    ∃ (k : Fin n → ℕ) (σ : Equiv.Perm (Fin n)),
      cyclicLatinEulerian n (k ∘ σ) ≠ cyclicLatinEulerian n k := by
  classical
  let z0 : Fin n := ⟨0, by omega⟩
  let z1 : Fin n := ⟨1, by omega⟩
  let z2 : Fin n := ⟨2, by omega⟩
  let z3 : Fin n := ⟨3, by omega⟩
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  let π : Equiv.Perm (Fin n) := Equiv.swap a b
  let σ : Equiv.Perm (Fin n) := Equiv.swap z1 z2
  let k : Fin n → ℕ := fun c => colAscents n (cyclicSquare n π) c
  have hπ0 : π z0 = z0 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := congrArg Fin.val h
      dsimp [z0, a] at this
      omega
    · intro h
      have := congrArg Fin.val h
      dsimp [z0, b] at this
      omega
  have hπlast : π b = a := Equiv.swap_apply_right a b
  have hone : z1 = (⟨1, by omega⟩ : Fin n) := rfl
  have hnext (i : ℕ) (hi : i + 1 < n) :
      (⟨i, by omega⟩ : Fin n) + z1 = ⟨i + 1, hi⟩ := by
    apply Fin.ext
    rw [Fin.val_add_eq_of_add_lt (by simp [z1]; omega)]
  have hfirst (c : Fin n) (hc : c.val ≤ 2) :
      (π z0 + c).val ≠ n - 1 := by
    rw [hπ0, Fin.val_add_eq_of_add_lt]
    · change 0 + c.val ≠ n - 1
      omega
    · change 0 + c.val < n
      omega
  have hlast0 : (π b + z0).val ≠ n - 1 := by
    rw [hπlast, Fin.val_add_eq_of_add_lt]
    · change n - 2 + 0 ≠ n - 1
      omega
    · change n - 2 + 0 < n
      omega
  have hlast1 : (π b + z1).val = n - 1 := by
    rw [hπlast, Fin.val_add_eq_of_add_lt]
    · change n - 2 + 1 = n - 1
      omega
    · change n - 2 + 1 < n
      omega
  have hlast2 : (π b + z2).val ≠ n - 1 := by
    rw [hπlast, Fin.val_add_eq_ite]
    simp only [a, z2]
    split_ifs <;> omega
  have hk01 : k z0 = k z1 := by
    have hs := shift_step (by omega : 2 ≤ n) π z0
    rw [hnext 0 (by omega)] at hs
    change k z1 + (if (π b + z0).val = n - 1 then 1 else 0) =
      k z0 + (if (π z0 + z0).val = n - 1 then 1 else 0) at hs
    simp [hlast0, hfirst z0 (by simp [z0])] at hs
    exact hs.symm
  have hk12 : k z1 ≠ k z2 := by
    have hs := shift_step (by omega : 2 ≤ n) π z1
    rw [hnext 1 (by omega)] at hs
    change k z2 + (if (π b + z1).val = n - 1 then 1 else 0) =
      k z1 + (if (π z0 + z1).val = n - 1 then 1 else 0) at hs
    simp [hlast1, hfirst z1 (by simp [z1])] at hs
    omega
  have hk23 : k z2 = k z3 := by
    have hs := shift_step (by omega : 2 ≤ n) π z2
    rw [hnext 2 (by omega)] at hs
    change k z3 + (if (π b + z2).val = n - 1 then 1 else 0) =
      k z2 + (if (π z0 + z2).val = n - 1 then 1 else 0) at hs
    simp [hlast2, hfirst z2 (by simp [z2])] at hs
    exact hs.symm
  have hσ0 : σ z0 = z0 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · simp [z0, z1, Fin.ext_iff]
    · simp [z0, z2, Fin.ext_iff]
  have hσ1 : σ z1 = z2 := Equiv.swap_apply_left z1 z2
  have hσ2 : σ z2 = z1 := Equiv.swap_apply_right z1 z2
  have hσ3 : σ z3 = z3 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · simp [z3, z1, Fin.ext_iff]
    · simp [z3, z2, Fin.ext_iff]
  have hzero : cyclicLatinEulerian n (k ∘ σ) = 0 := by
    by_contra hnonzero
    have hp : 0 < cyclicLatinEulerian n (k ∘ σ) := Nat.pos_of_ne_zero hnonzero
    obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp hp
    have hρk : ∀ c, colAscents n (cyclicSquare n ρ) c = k (σ c) := by
      exact (Finset.mem_filter.mp hρ).2
    rcases no_three_changes hn ρ with h01 | h12 | h23
    · have heq : k z0 = k z2 := by simpa [z0, z1, hρk, hσ0, hσ1] using h01
      exact hk12 (hk01.symm.trans heq)
    · have heq : k z2 = k z1 := by simpa [z1, z2, hρk, hσ1, hσ2] using h12
      exact hk12 heq.symm
    · have heq : k z1 = k z3 := by simpa [z2, z3, hρk, hσ2, hσ3] using h23
      exact hk12 (heq.trans hk23.symm)
  have hpositive : 0 < cyclicLatinEulerian n k := by
    apply Finset.card_pos.mpr
    refine ⟨π, ?_⟩
    simp [k]
  refine ⟨k, σ, ?_⟩
  rw [hzero]
  omega

/-- Refutation of the fixed full-symmetry claim. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨k, σ, hne⟩ := not_fully_symmetric 4 (by omega)
  exact hne (h 4 k σ)

#print axioms result

end D5.S3.Combinatorics.CyclicLatinEulerianRefutation
