/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleGram
   mirror-E: none(waiver:general-gram-rank-computation)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Mul]
   utility: none
   digest: Prefix and suffix row induction gives a trivial Gram kernel for every order. -/

import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGram

open Finset Matrix

/-- The all-order Gram matrix is nonsingular over any commutative ring. Odd rows
successively kill the even coordinates; even rows then kill the odd coordinates backwards. -/
theorem gram_kernel_zero {K : Type*} [CommRing K] (k : ℕ) (x : Fin (2 * k) → K)
    (hx : Matrix.mulVec (fun i j : Fin (2 * k) =>
      if i = j then (0 : K) else if min i.val j.val % 2 = 0 then 1 else 0) x = 0) :
    x = 0 := by
  classical
  let A : Matrix (Fin (2 * k)) (Fin (2 * k)) K := fun i j =>
    if i = j then 0 else if min i.val j.val % 2 = 0 then 1 else 0
  let even : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val, by omega⟩
  let odd : Fin k → Fin (2 * k) := fun i => ⟨2 * i.val + 1, by omega⟩
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    { toFun := Sum.elim even odd
      invFun := fun i => if i.val % 2 = 0 then
        Sum.inl ⟨i.val / 2, by omega⟩ else Sum.inr ⟨i.val / 2, by omega⟩
      left_inv := fun i => by
        rcases i with i | i
        · simp [even]
        · have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
          simp [odd, hdiv]
      right_inv := fun i => by
        apply Fin.ext
        dsimp [even, odd]
        split_ifs <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega }
  have expansion (i : Fin (2 * k)) : (A.mulVec x) i =
      (∑ j : Fin k, A i (even j) * x (even j)) +
        (∑ j : Fin k, A i (odd j) * x (odd j)) := by
    change (∑ j : Fin (2 * k), A i j * x j) = _
    calc
      _ = ∑ j : Fin k ⊕ Fin k, A i (e j) * x (e j) :=
        (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = _ := by rw [Fintype.sum_sum_type]; rfl
  have odd_even (i j : Fin k) : A (odd i) (even j) =
      if j.val ≤ i.val then 1 else 0 := by
    have hne : odd i ≠ even j := by
      intro h
      have h' := congrArg Fin.val h
      dsimp [odd, even] at h'
      omega
    simp only [A, if_neg hne]
    dsimp [odd, even]
    rw [min_def]
    split_ifs <;> dsimp [even, odd] at * <;> omega
  have odd_odd (i j : Fin k) : A (odd i) (odd j) = 0 := by
    dsimp [A, odd]
    split_ifs with heq heven
    · rfl
    · rw [min_def] at heven
      split_ifs at heven <;> omega
    · rfl
  have even_odd (i j : Fin k) : A (even i) (odd j) =
      if i.val ≤ j.val then 1 else 0 := by
    have hne : even i ≠ odd j := by
      intro h
      have h' := congrArg Fin.val h
      dsimp [odd, even] at h'
      omega
    simp only [A, if_neg hne]
    dsimp [odd, even]
    rw [min_def]
    split_ifs <;> dsimp [even, odd] at * <;> omega
  have prefix_rows (i : Fin k) :
      (∑ j : Fin k, if j.val ≤ i.val then x (even j) else 0) = 0 := by
    have h := congrFun hx (odd i)
    change (A.mulVec x) (odd i) = 0 at h
    rw [expansion] at h
    simp only [odd_even, odd_odd, ite_mul, one_mul, zero_mul, sum_const_zero,
      add_zero] at h
    exact h
  have even_nat : ∀ i (hi : i < k), x (even ⟨i, hi⟩) = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have h := prefix_rows ⟨i, hi⟩
      rw [sum_eq_single (⟨i, hi⟩ : Fin k)] at h
      · simpa using h
      · intro j _ hji
        by_cases hj : j.val ≤ i
        · rw [if_pos hj]
          have hne : j.val ≠ i := fun h => hji (Fin.ext h)
          exact ih j.val (by omega) j.isLt
        · exact if_neg hj
      · simp
  have even_zero (i : Fin k) : x (even i) = 0 := even_nat i.val i.isLt
  have suffix_rows (i : Fin k) :
      (∑ j : Fin k, if i.val ≤ j.val then x (odd j) else 0) = 0 := by
    have h := congrFun hx (even i)
    change (A.mulVec x) (even i) = 0 at h
    rw [expansion] at h
    simp only [even_zero, mul_zero, sum_const_zero, zero_add, even_odd, ite_mul,
      one_mul, zero_mul] at h
    exact h
  have backwards : ∀ d i (hi : i < k), k ≤ i + d + 1 → x (odd ⟨i, hi⟩) = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi hb
      have h := suffix_rows ⟨i, hi⟩
      rw [sum_eq_single (⟨i, hi⟩ : Fin k)] at h
      · simpa using h
      · intro j _ hji
        have hj := j.isLt
        have hne : j.val ≠ i := fun h => hji (Fin.ext h)
        exact if_neg (by dsimp; omega)
      · simp
    | succ d ih =>
      intro i hi hb
      have h := suffix_rows ⟨i, hi⟩
      rw [sum_eq_single (⟨i, hi⟩ : Fin k)] at h
      · simpa using h
      · intro j _ hji
        by_cases hj : i ≤ j.val
        · rw [if_pos hj]
          have hne : j.val ≠ i := fun h => hji (Fin.ext h)
          exact ih j.val j.isLt (by omega)
        · exact if_neg hj
      · simp
  have odd_zero (i : Fin k) : x (odd i) = 0 := backwards k i.val i.isLt (by omega)
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  rcases j with j | j
  · exact even_zero j
  · exact odd_zero j

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGram
