/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials
   mirror-E: none(waiver:normal-hankel-bezout-inverse)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: Every entry of a normal Hankel inverse is a supported Bezout coefficient sum. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! The two normal moment polynomials determine every Hankel inverse entry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials

open Finset
open scoped Matrix

/-- The complete inverse at a normal index, including gapped normal families.
The coefficient sequences are extended by zero above their respective degrees.
Only the enclosing Hankel determinant is required to be a unit. -/
theorem hankel_inverse_bezout (μ : ℕ → ℤ) (n : ℕ) (c d : ℕ → ℤ)
    (hc : c (n + 1) = 1)
    (csupport : ∀ k, n + 1 < k → c k = 0)
    (dsupport : ∀ k, n + 1 ≤ k → d k = 0)
    (orthogonal : ∀ t < n + 1, ∑ r ∈ range (n + 2), c r * μ (r + t) = 0)
    (previous : ∀ t < n + 1, ∑ r ∈ range (n + 1), d r * μ (r + t) =
      if t = n then -1 else 0)
    (unit : IsUnit (Matrix.of fun i j : Fin (n + 1) => μ (i.val + j.val)).det) :
    ∀ i j : Fin (n + 1),
      (Matrix.of fun a b : Fin (n + 1) => μ (a.val + b.val))⁻¹ i j =
        -∑ a ∈ range (j.val + 1),
          (c (i.val + j.val + 1 - a) * d a - d (i.val + j.val + 1 - a) * c a) := by
  classical
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i j => μ (i.val + j.val)
  let last : Fin (n + 1) := Fin.last n
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i j =>
      if j = last then -c i.val else if i.val = j.val + 1 then 1 else 0
  have hu : IsUnit H.det := unit
  have symmetric : H.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, H, Matrix.of_apply]
    rw [Nat.add_comm]
  have product (i j : Fin (n + 1)) : (H * T) i j = μ (i.val + j.val + 1) := by
    rw [Matrix.mul_apply]
    by_cases hj : j = last
    · subst j
      simp only [T, Matrix.of_apply, ite_true, H, mul_neg, sum_neg_distrib]
      have hz := orthogonal i.val i.isLt
      rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ, hc, one_mul] at hz
      have hs : (∑ r : Fin (n + 1), μ (i.val + r.val) * c r.val) =
          ∑ r ∈ range (n + 1), c r * μ (r + i.val) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply sum_congr rfl
        intro r _
        rw [mul_comm, Nat.add_comm i.val]
      rw [hs]
      have hi : n + 1 + i.val = i.val + last.val + 1 := by simp [last]; omega
      rw [hi] at hz
      exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left hz)
    · have hjlt : j.val + 1 < n + 1 := by
        have hne : j.val ≠ n := by
          intro he
          apply hj
          exact Fin.ext (by simpa [last] using he)
        omega
      let next : Fin (n + 1) := ⟨j.val + 1, hjlt⟩
      rw [sum_eq_single next]
      · simp [T, hj, next, H, Nat.add_assoc]
      · intro r _ hr
        have hne : r.val ≠ j.val + 1 := fun he => hr (Fin.ext he)
        simp [T, hj, hne]
      · simp
  have selfadjoint : H * T = T.transpose * H := by
    have hs : (H * T).IsSymm := by
      ext i j
      simp only [Matrix.transpose_apply, product]
      rw [Nat.add_comm j.val]
    calc
      H * T = (H * T).transpose := hs.eq.symm
      _ = T.transpose * H := by rw [Matrix.transpose_mul, symmetric.eq]
  have commutes : T * H⁻¹ = H⁻¹ * T.transpose := by
    have he := congrArg (fun A => H⁻¹ * A * H⁻¹) selfadjoint
    have lhs : H⁻¹ * (H * T) * H⁻¹ = T * H⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul H hu, Matrix.one_mul]
    have rhs : H⁻¹ * (T.transpose * H) * H⁻¹ = H⁻¹ * T.transpose := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv H hu, Matrix.mul_one]
    rwa [lhs, rhs] at he
  have hbvec : H *ᵥ (fun i => d i.val) = Pi.single last (-1) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, H, Matrix.of_apply]
    have hs : (∑ r : Fin (n + 1), μ (i.val + r.val) * d r.val) =
        ∑ r ∈ range (n + 1), d r * μ (r + i.val) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro r _
      rw [mul_comm, Nat.add_comm i.val]
    rw [hs, previous i.val i.isLt]
    by_cases hi : i = last
    · subst i
      simp [last]
    · have hne : i.val ≠ n := by
        intro he
        exact hi (Fin.ext (by simpa [last] using he))
      simp [hi, hne]
  have column (i : Fin (n + 1)) : H⁻¹ i last = -d i.val := by
    have he := congrArg (fun v => (H⁻¹ *ᵥ v) i) hbvec
    have hh : d i.val = H⁻¹ i last * (-1) := by
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hu,
        Matrix.mulVec_single, Matrix.col, smul_eq_mul] using he
    linarith
  have row (j : Fin (n + 1)) : H⁻¹ last j = -d j.val := by
    exact (symmetric.inv.apply j last).trans (column j)
  have tentry (i r : Fin (n + 1)) :
      T i r = (if r = last then -c i.val else 0) +
        (if i.val = r.val + 1 then 1 else 0) := by
    by_cases hr : r = last
    · subst r
      have hne : i.val ≠ last.val + 1 := by simp [last]; omega
      simp [T, hne]
    · simp [T, hr]
  have left (i : Fin (n + 1)) (hi : i.val < n) (j : Fin (n + 1)) :
      (T * H⁻¹) ⟨i.val + 1, by omega⟩ j = H⁻¹ i j - c (i.val + 1) * H⁻¹ last j := by
    rw [Matrix.mul_apply]
    simp_rw [tentry, add_mul, ite_mul, one_mul, zero_mul]
    rw [sum_add_distrib]
    have eqs (r : Fin (n + 1)) : (i.val + 1 = r.val + 1) ↔ r = i := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · rintro rfl; rfl
    simp_rw [eqs]
    simp
    ring
  have right_zero (i : Fin (n + 1)) :
      (H⁻¹ * T.transpose) i 0 = -c 0 * H⁻¹ i last := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply, tentry, Fin.val_zero]
    simp
    ring
  have right_succ (i : Fin (n + 1)) (j : ℕ) (hj : j < n) :
      (H⁻¹ * T.transpose) i ⟨j + 1, by omega⟩ =
        H⁻¹ i ⟨j, by omega⟩ - c (j + 1) * H⁻¹ i last := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply, tentry, mul_add, mul_ite, mul_one, mul_zero]
    rw [sum_add_distrib]
    have eqs (r : Fin (n + 1)) :
        (j + 1 = r.val + 1) ↔ r = (⟨j, by omega⟩ : Fin (n + 1)) := by
      rw [Fin.ext_iff]
      change (j + 1 = r.val + 1) ↔ r.val = j
      omega
    simp_rw [eqs]
    simp
    ring
  have boundary (j : Fin (n + 1)) :
      -∑ a ∈ range (j.val + 1),
          (c (last.val + j.val + 1 - a) * d a -
            d (last.val + j.val + 1 - a) * c a) = -d j.val := by
    congr 1
    rw [sum_eq_single j.val]
    · have he : last.val + j.val + 1 - j.val = n + 1 := by simp [last]; omega
      rw [he, hc, dsupport (n + 1) le_rfl]
      ring
    · intro a ha hne
      have ha' := mem_range.mp ha
      have hbig : n + 1 < last.val + j.val + 1 - a := by simp [last]; omega
      have hd := dsupport (last.val + j.val + 1 - a) (Nat.le_of_lt hbig)
      rw [csupport _ hbig, hd]
      ring
    · simp
  have entries : ∀ (j : ℕ) (hj : j ≤ n), ∀ i : Fin (n + 1),
      H⁻¹ i ⟨j, by omega⟩ =
        -∑ a ∈ range (j + 1),
          (c (i.val + j + 1 - a) * d a - d (i.val + j + 1 - a) * c a) := by
    intro j
    induction j with
    | zero =>
      intro hj i
      by_cases hi : i = last
      · subst i
        exact (row _).trans (boundary _).symm
      · have hil : i.val < n := by
          have hne : i.val ≠ n := fun he => hi (Fin.ext (by simpa [last] using he))
          omega
        have he := congrArg (fun A => A ⟨i.val + 1, by omega⟩ 0) commutes
        rw [left i hil, right_zero, row, column] at he
        simp only [Fin.val_zero, Fin.val_mk] at he
        simpa using (show H⁻¹ i 0 = -(c (i.val + 1) * d 0 - d (i.val + 1) * c 0) by
          linear_combination he)
    | succ j ih =>
      intro hj i
      by_cases hi : i = last
      · subst i
        exact (row _).trans (boundary _).symm
      · have hil : i.val < n := by
          have hne : i.val ≠ n := fun he => hi (Fin.ext (by simpa [last] using he))
          omega
        let next : Fin (n + 1) := ⟨i.val + 1, by omega⟩
        have he := congrArg (fun A => A next ⟨j + 1, by omega⟩) commutes
        rw [left i hil, right_succ _ j (by omega), row, column] at he
        have hv := ih (by omega) next
        have hs : (∑ a ∈ range (j + 1),
            (c (next.val + j + 1 - a) * d a - d (next.val + j + 1 - a) * c a)) =
            ∑ a ∈ range (j + 1),
            (c (i.val + (j + 1) + 1 - a) * d a -
              d (i.val + (j + 1) + 1 - a) * c a) := by
          apply sum_congr rfl
          intro a _
          congr 3 <;> dsimp [next] <;> omega
        rw [hs] at hv
        rw [sum_range_succ]
        have heq : i.val + (j + 1) + 1 - (j + 1) = i.val + 1 := by omega
        rw [heq]
        dsimp only [next] at he hv
        linear_combination he + hv
  intro i j
  exact entries j.val (by omega) i

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelBoundaryPolynomials
