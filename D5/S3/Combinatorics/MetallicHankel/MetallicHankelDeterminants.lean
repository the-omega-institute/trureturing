/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelDeterminants
   mirror-E: none(waiver:integral-zero-run-hankel-transform)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Monic orthogonality gives integral Hankel zero runs and shifted determinants. -/

import Mathlib.LinearAlgebra.Matrix.Block
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelDeterminants

open Finset MetallicHankelDefs

/-- A monic relation with a run of zero moments gives the next nonzero determinant and gaps. -/
theorem zero_run (Φ : PowerSeries ℤ) (ℓ s m : ℕ) (c : ℕ → ℤ) (h : ℤ)
    (hm : 0 < m) (hc : c s = 1)
    (hz : ∀ t < s + m - 1,
      ∑ r ∈ range (s + 1), c r * PowerSeries.coeff (ℓ + r + t) Φ = 0)
    (hh : ∑ r ∈ range (s + 1),
      c r * PowerSeries.coeff (ℓ + r + (s + m - 1)) Φ = h) :
    shiftedHankel Φ ℓ (s + m) =
      (-1 : ℤ) ^ (m * (m - 1) / 2) * h ^ m * shiftedHankel Φ ℓ s ∧
    (∀ j, s < j → j < s + m → shiftedHankel Φ ℓ j = 0) ∧
    shiftedHankel Φ (ℓ + 1) s =
      (-1 : ℤ) ^ s * shiftedHankel Φ ℓ s * c 0 := by
  classical
  have christoffel (Φ : PowerSeries ℤ) (ℓ s : ℕ) (c : ℕ → ℤ)
      (hc : c s = 1)
      (hz : ∀ t < s, ∑ r ∈ range (s + 1), c r * PowerSeries.coeff (ℓ + r + t) Φ = 0) :
      shiftedHankel Φ (ℓ + 1) s =
        (-1 : ℤ) ^ s * shiftedHankel Φ ℓ s * c 0 := by
    classical
    cases s with
    | zero => simp [shiftedHankel, hc]
    | succ n =>
      let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
        Matrix.of fun i j => PowerSeries.coeff (ℓ + i.val + j.val) Φ
      let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
        Matrix.of fun i j =>
          if j.val < n then (if i.val = j.val + 1 then 1 else 0) else -c i.val
      have ht : T.det = (-1 : ℤ) ^ (n + 1) * c 0 := by
        have row (j : Fin (n + 1)) :
            T 0 j = if j = Fin.last n then -c 0 else 0 := by
          dsimp [T]
          by_cases hj : j.val < n
          · have hne : j ≠ Fin.last n := by
              intro he
              have hh := congrArg Fin.val he
              simp only [Fin.val_last] at hh
              omega
            simp [hj, hne]
          · have he : j = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            simp [he]
        have minor : T.submatrix Fin.succ (Fin.last n).succAbove = 1 := by
          ext i j
          simp only [Matrix.submatrix_apply, Fin.succAbove_last, T, Matrix.of_apply,
            Fin.val_castSucc, Fin.val_succ, Matrix.one_apply]
          simp [j.isLt, Fin.ext_iff]
        rw [Matrix.det_succ_row_zero, sum_eq_single (Fin.last n)]
        · rw [row, if_pos rfl, minor, Matrix.det_one]
          simp only [Fin.val_last, mul_one, pow_succ]
          ring
        · intro j _ hne
          rw [row, if_neg hne]
          simp
        · simp
      have product : A * T = Matrix.of
          (fun i j : Fin (n + 1) => PowerSeries.coeff (ℓ + 1 + i.val + j.val) Φ) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.of_apply]
        by_cases hj : j.val < n
        · let a : Fin (n + 1) := ⟨j.val + 1, by omega⟩
          rw [sum_eq_single a]
          · simp [A, T, hj, a, Nat.add_left_comm, Nat.add_comm]
          · intro b _ hne
            have hb : b.val ≠ j.val + 1 := by
              intro he
              apply hne
              exact Fin.ext he
            simp [T, hj, hb]
          · simp
        · have hjn : j.val = n := by omega
          have h := hz i.val i.isLt
          rw [sum_range_succ] at h
          simp only [hc, one_mul] at h
          have hh : (∑ r ∈ range (n + 1),
              c r * PowerSeries.coeff (ℓ + r + i.val) Φ) =
              -PowerSeries.coeff (ℓ + (n + 1) + i.val) Φ := by omega
          have sumfin : (∑ r : Fin (n + 1),
              c r.val * PowerSeries.coeff (ℓ + r.val + i.val) Φ) =
              ∑ r ∈ range (n + 1), c r * PowerSeries.coeff (ℓ + r + i.val) Φ :=
            Fin.sum_univ_eq_sum_range
              (fun r => c r * PowerSeries.coeff (ℓ + r + i.val) Φ) (n + 1)
          simp only [T, Matrix.of_apply, hj, if_false, A, mul_neg]
          rw [sum_neg_distrib]
          simp_rw [mul_comm, show ∀ r : Fin (n + 1), ℓ + i.val + r.val =
            ℓ + r.val + i.val by intro r; omega]
          rw [sumfin, hh, neg_neg]
          simp only [hjn, Nat.add_comm, Nat.add_left_comm]
      have hd := congrArg Matrix.det product
      rw [Matrix.det_mul, ht] at hd
      change A.det * ((-1 : ℤ) ^ (n + 1) * c 0) = _ at hd
      change (Matrix.of fun i j : Fin (n + 1) =>
        PowerSeries.coeff (ℓ + 1 + i.val + j.val) Φ).det =
          (-1 : ℤ) ^ (n + 1) * A.det * c 0
      rw [← hd]
      ring
  have interval_sum (N a : ℕ) (ha : a + s < N) (f : ℕ → ℤ) :
      (∑ j : Fin N, if a ≤ j.val ∧ j.val ≤ a + s then f (j.val - a) else 0) =
        ∑ r ∈ range (s + 1), f r := by
    rw [← sum_filter]
    apply sum_bij (fun j _ => j.val - a)
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      simp only [mem_range]
      omega
    · intro i hi j hj he
      simp only [mem_filter, mem_univ, true_and] at hi hj
      exact Fin.ext (by omega)
    · intro r hr
      simp only [mem_range] at hr
      refine ⟨⟨a + r, by omega⟩, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro j hj
      rfl
  have staircase : ∀ d : ℕ, ∀ M : Matrix (Fin (s + d)) (Fin (s + d)) ℤ,
      (∀ i j : Fin s, M (Fin.castAdd d i) (Fin.castAdd d j) =
        PowerSeries.coeff (ℓ + i.val + j.val) Φ) →
      (∀ i j : Fin (s + d), s ≤ i.val → i.val + j.val < 2 * s + d - 1 →
        M i j = 0) →
      (∀ i j : Fin (s + d), s ≤ i.val → i.val + j.val = 2 * s + d - 1 →
        M i j = h) →
      M.det = (-1 : ℤ) ^ (d * (d - 1) / 2) * h ^ d * shiftedHankel Φ ℓ s := by
    intro d
    induction d with
    | zero =>
      intro M top _ _
      have he : M = Matrix.of
          (fun i j : Fin s => PowerSeries.coeff (ℓ + i.val + j.val) Φ) := by
        ext i j
        exact top i j
      simp [he, shiftedHankel]
    | succ d ih =>
      intro M top zero anti
      let pivot : Fin (s + d + 1) := ⟨s, by omega⟩
      let last : Fin (s + d + 1) := Fin.last (s + d)
      let B := M.submatrix pivot.succAbove last.succAbove
      have above (i : Fin (s + d)) :
          (pivot.succAbove i).val = if i.val < s then i.val else i.val + 1 := by
        by_cases hi : i.val < s
        · rw [Fin.succAbove_of_castSucc_lt pivot i (by exact hi)]
          simp [hi]
        · rw [Fin.succAbove_of_le_castSucc pivot i (by exact le_of_not_gt hi)]
          simp [hi]
      have btop (i j : Fin s) : B (Fin.castAdd d i) (Fin.castAdd d j) =
          PowerSeries.coeff (ℓ + i.val + j.val) Φ := by
        have roweq : pivot.succAbove (Fin.castAdd d i) = Fin.castAdd (d + 1) i := by
          apply Fin.ext
          rw [above]
          simp [i.isLt]
        have coleq : last.succAbove (Fin.castAdd d j) = Fin.castAdd (d + 1) j := by
          simp [last]
          rfl
        simp only [B, Matrix.submatrix_apply, roweq, coleq]
        exact top i j
      have bzero (i j : Fin (s + d)) (hi : s ≤ i.val)
          (hij : i.val + j.val < 2 * s + d - 1) : B i j = 0 := by
        apply zero
        · rw [above]
          simp [show ¬i.val < s by omega]
          omega
        · rw [above]
          simp only [show ¬i.val < s by omega, if_false, last, Fin.succAbove_last,
            Fin.val_castSucc]
          omega
      have banti (i j : Fin (s + d)) (hi : s ≤ i.val)
          (hij : i.val + j.val = 2 * s + d - 1) : B i j = h := by
        apply anti
        · rw [above]
          simp [show ¬i.val < s by omega]
          omega
        · rw [above]
          simp only [show ¬i.val < s by omega, if_false, last, Fin.succAbove_last,
            Fin.val_castSucc]
          omega
      have bd := ih B btop bzero banti
      have expand : M.det = (-1 : ℤ) ^ d * h * B.det := by
        rw [Matrix.det_succ_row (n := s + d) M pivot]
        rw [sum_eq_single last]
        · have entry : M pivot last = h := anti pivot last (by simp [pivot]) (by
            simp only [pivot, last, Fin.val_last]
            omega)
          rw [entry]
          have sign : (-1 : ℤ) ^ (pivot.val + last.val) = (-1 : ℤ) ^ d := by
            simp only [pivot, last, Fin.val_last]
            rw [show s + (s + d) = s + s + d by omega, pow_add]
            simp [pow_add, ← mul_pow]
          rw [sign]
        · intro j _ hj
          have hlt : j.val < s + d := by
            have hne : j.val ≠ s + d := by
              intro he
              apply hj
              exact Fin.ext (by simpa [last] using he)
            omega
          rw [zero pivot j (by simp [pivot]) (by simp only [pivot]; omega)]
          simp
        · simp
      have exponent : (d + 1) * d / 2 = d + d * (d - 1) / 2 := by
        cases d with
        | zero => simp
        | succ d =>
          simp only [Nat.add_sub_cancel]
          rw [show (d + 1 + 1) * (d + 1) =
            (d + 1) * d + (d + 1) * 2 by ring]
          rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
          omega
      rw [expand, bd, show d + 1 - 1 = d by omega, exponent, pow_add, pow_succ]
      ring
  let A : Matrix (Fin (s + m)) (Fin (s + m)) ℤ :=
    Matrix.of fun i j => PowerSeries.coeff (ℓ + i.val + j.val) Φ
  let T : Matrix (Fin (s + m)) (Fin (s + m)) ℤ := Matrix.of fun i j =>
    if i.val < s then (if i = j then 1 else 0)
    else if i.val - s ≤ j.val ∧ j.val ≤ i.val then c (j.val - (i.val - s)) else 0
  have td : T.det = 1 := by
    have lower : T.IsLowerTriangular := by
      intro i j hij
      have hlt : i.val < j.val := hij
      dsimp [T]
      by_cases hi : i.val < s
      · simp only [hi, if_true]
        exact if_neg (by intro he; subst j; omega)
      · simp only [hi, if_false]
        exact if_neg (by omega)
    rw [Matrix.det_of_isLowerTriangular T lower]
    apply prod_eq_one
    intro i _
    dsimp [T]
    by_cases hi : i.val < s
    · simp [hi]
    · simp [show i.val - s ≤ i.val by omega, show i.val - (i.val - s) = s by omega, hc]
  have upper (i j : Fin (s + m)) (hi : i.val < s) :
      (T * A) i j = PowerSeries.coeff (ℓ + i.val + j.val) Φ := by
    simp only [Matrix.mul_apply]
    rw [sum_eq_single i]
    · simp [T, A, hi]
    · intro b _ hne
      simp [T, hi, Ne.symm hne]
    · simp
  have bottom (i j : Fin (s + m)) (hi : s ≤ i.val) :
      (T * A) i j = ∑ r ∈ range (s + 1),
        c r * PowerSeries.coeff (ℓ + r + (i.val - s + j.val)) Φ := by
    have he : i.val = (i.val - s) + s := by omega
    have he' : (T * A) i j = ∑ b : Fin (s + m),
        if i.val - s ≤ b.val ∧ b.val ≤ i.val - s + s then
          c (b.val - (i.val - s)) *
            PowerSeries.coeff (ℓ + (b.val - (i.val - s)) + (i.val - s + j.val)) Φ
        else 0 := by
      simp only [Matrix.mul_apply]
      apply sum_congr rfl
      intro b _
      simp only [T, Matrix.of_apply, show ¬i.val < s by omega, if_false, A]
      simp only [show i.val - s + s = i.val by omega]
      by_cases hb : i.val - s ≤ b.val ∧ b.val ≤ i.val
      · rw [if_pos hb, if_pos hb]
        rw [show ℓ + b.val + j.val =
          ℓ + (b.val - (i.val - s)) + (i.val - s + j.val) by omega]
      · rw [if_neg hb, if_neg hb, zero_mul]
    rw [he']
    exact interval_sum (s + m) (i.val - s) (by omega)
      (fun r => c r * PowerSeries.coeff (ℓ + r + (i.val - s + j.val)) Φ)
  have grow : (T * A).det =
      (-1 : ℤ) ^ (m * (m - 1) / 2) * h ^ m * shiftedHankel Φ ℓ s := by
    apply staircase m (T * A)
    · intro i j
      exact upper _ _ i.isLt
    · intro i j hi hij
      rw [bottom i j hi]
      apply hz
      omega
    · intro i j hi hij
      rw [bottom i j hi]
      have he : i.val - s + j.val = s + m - 1 := by omega
      rw [he]
      exact hh
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Matrix.det_mul, td, one_mul, A, shiftedHankel] using grow
  · intro j hsj hj
    let H : Matrix (Fin j) (Fin j) ℤ :=
      Matrix.of fun a b => PowerSeries.coeff (ℓ + a.val + b.val) Φ
    let v : Fin j → ℤ := fun a => if a.val ≤ s then c a.val else 0
    let pivot : Fin j := ⟨s, hsj⟩
    have row : (∑ a : Fin j, (v a) • H a) = 0 := by
      ext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have he : (∑ a : Fin j, v a * H a b) =
          ∑ a : Fin j, if 0 ≤ a.val ∧ a.val ≤ 0 + s then
            c (a.val - 0) * PowerSeries.coeff (ℓ + (a.val - 0) + b.val) Φ else 0 := by
        apply sum_congr rfl
        intro a _
        simp [v, H, ite_mul]
      rw [he, interval_sum j 0 (by omega)
        (fun r => c r * PowerSeries.coeff (ℓ + r + b.val) Φ)]
      apply hz
      omega
    have update : (H.updateRow pivot (∑ a, (v a) • H a)).det = H.det := by
      rw [Matrix.det_updateRow_sum]
      simp [v, pivot, hc]
    rw [row, Matrix.det_eq_zero_of_row_eq_zero pivot (by intro b; simp)] at update
    exact update.symm
  · apply christoffel Φ ℓ s c hc
    intro t ht
    exact hz t (by omega)

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelDeterminants
