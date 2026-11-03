/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barry–Kevrekidis alternating vortex polygon spectrum and distinct real pairs. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import D5.S3.Quantum.Matrix.CirculantCharpoly
import D5.S3.FluidDynamics.Vortices.InverseChordCirculant

/-! Alternating vortex polygon equilibrium, Jacobian and real spectrum. -/

noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum

set_option autoImplicit false

/-- Alternating charge, with `j` the zero-based label corresponding to the source's `j+1`. -/
def charge (N : ℕ) (j : Fin N) : ℝ := (-1 : ℝ) ^ (j.val + 2)

/-- The Cartesian point-vortex field with `b = 2` and `Ω = 1/2`. -/
def field (N : ℕ) (z : Fin N ⊕ Fin N → ℝ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j =>
      -charge N j * (1 / 2 : ℝ) * z (Sum.inr j) -
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inr j) - z (Sum.inr k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)
  | Sum.inr j =>
      charge N j * (1 / 2 : ℝ) * z (Sum.inl j) +
        ∑ k : Fin N, if k = j then 0 else
          charge N k * (z (Sum.inl j) - z (Sum.inl k)) /
            ((z (Sum.inl j) - z (Sum.inl k)) ^ 2 +
              (z (Sum.inr j) - z (Sum.inr k)) ^ 2)

/-- The regular unit `N`-gon in the source's cyclic order. -/
def polygon (N : ℕ) : Fin N ⊕ Fin N → ℝ := fun p =>
  match p with
  | Sum.inl j => Real.cos (2 * Real.pi * (j.val + 1 : ℝ) / N)
  | Sum.inr j => Real.sin (2 * Real.pi * (j.val + 1 : ℝ) / N)

/-- Cartesian Jacobian, defined by the partial derivative in each coordinate direction. -/
def jacobian (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  fun p q => deriv (fun t : ℝ => field N (polygon N + t • Pi.single q 1) p) 0

private lemma distinctness_certificate (m k l : ℕ)
    (hk : 2 ≤ k) (hkl : k < l) (hlm : l < m) :
    ((m : ℝ) - k) ^ 2 * ((k : ℝ) ^ 2 - 2) ≠
      ((m : ℝ) - l) ^ 2 * ((l : ℝ) ^ 2 - 2) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hklR : (k : ℝ) < l := by exact_mod_cast hkl
  have hlmR : (l : ℝ) < m := by exact_mod_cast hlm
  let s : ℝ := k + l
  let Q : ℝ → ℝ := fun t =>
    s * t ^ 2 - 2 * ((k : ℝ)^2 + k*l + (l : ℝ)^2 - 2) * t +
      s * ((k : ℝ)^2 + (l : ℝ)^2 - 2)
  have hs : 0 < s := by dsimp [s]; linarith
  have hfactor :
      ((m : ℝ) - k)^2 * ((k : ℝ)^2 - 2) -
        ((m : ℝ) - l)^2 * ((l : ℝ)^2 - 2) = (k - (l : ℝ)) * Q m := by
    dsimp [Q, s]
    ring
  have hQ : Q m ≠ 0 := by
    by_cases hm : m < k + l
    · have hmR : (m : ℝ) ≤ s - 1 := by
        have hc : (m : ℝ) + 1 ≤ (k : ℝ) + l := by exact_mod_cast (show m + 1 ≤ k + l by omega)
        dsimp [s]
        linarith
      have hQl : Q l < 0 := by
        have hid : Q l = -((l : ℝ) - k) * ((k : ℝ)^2 - 2) := by dsimp [Q, s]; ring
        rw [hid]
        have : 0 < (k : ℝ)^2 - 2 := by nlinarith
        exact mul_neg_of_neg_of_pos (by linarith) this
      have hQb : Q (s - 1) < 0 := by
        let u : ℝ := k - 2
        let v : ℝ := l - k - 1
        have hu : 0 ≤ u := by dsimp [u]; linarith
        have hv : 0 ≤ v := by
          have hc : (k : ℝ) + 1 ≤ l := by exact_mod_cast (show k + 1 ≤ l by omega)
          dsimp [v]
          linarith
        have hid : Q (s - 1) = -(2*u^2 + 2*u*v + 4*u + v + 1) := by
          dsimp [Q, s, u, v]
          ring
        rw [hid]
        nlinarith [sq_nonneg u, mul_nonneg hu hv]
      have ht : 0 < (m : ℝ) - l := by linarith
      have hr : 0 ≤ s - 1 - m := by linarith
      have hwidth : 0 < (k : ℝ) - 1 := by linarith
      have hinterp : ((k : ℝ) - 1) * Q m =
          (s - 1 - m) * Q l + ((m : ℝ) - l) * Q (s - 1) -
            s * ((k : ℝ) - 1) * ((m : ℝ) - l) * (s - 1 - m) := by
        dsimp [Q, s]
        ring
      have hneg := mul_neg_of_pos_of_neg ht hQb
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hr (le_of_lt hQl)
      have hnonneg : 0 ≤ s * ((k : ℝ) - 1) * ((m : ℝ) - l) * (s - 1 - m) :=
        mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hs) (le_of_lt hwidth)) (le_of_lt ht)) hr
      have : ((k : ℝ) - 1) * Q m < 0 := by linarith
      intro he
      rw [he, mul_zero] at this
      linarith
    · have hmR : s ≤ m := by dsimp [s]; exact_mod_cast (show k + l ≤ m by omega)
      let h : ℝ := m - s
      have hh : 0 ≤ h := by dsimp [h]; linarith
      have hid : Q m = 2*s + (2*(k : ℝ)*l + 4)*h + s*h^2 := by
        dsimp [Q, h, s]
        ring
      have hcoef : 0 ≤ 2*(k : ℝ)*l + 4 := by positivity
      have hpos : 0 < Q m := by
        rw [hid]
        have := mul_nonneg hcoef hh
        have := mul_nonneg (le_of_lt hs) (sq_nonneg h)
        linarith
      exact ne_of_gt hpos
  intro he
  have hz : (k - (l : ℝ)) * Q m = 0 := by rw [← hfactor, he, sub_self]
  exact (mul_ne_zero (by linarith) hQ) hz

private lemma chord_sq (N : ℕ) (j k : Fin N) :
    (polygon N (Sum.inl j) - polygon N (Sum.inl k))^2 +
      (polygon N (Sum.inr j) - polygon N (Sum.inr k))^2 =
        4 * Real.sin (Real.pi * ((j.val : ℝ) - k.val) / N)^2 := by
  let a := 2 * Real.pi * (j.val + 1 : ℝ) / N
  let b := 2 * Real.pi * (k.val + 1 : ℝ) / N
  have hab : (a - b) / 2 = Real.pi * ((j.val : ℝ) - k.val) / N := by
    dsimp [a, b]
    ring
  change (Real.cos a - Real.cos b)^2 + (Real.sin a - Real.sin b)^2 = _
  rw [← hab, Real.cos_sub_cos, Real.sin_sub_sin]
  have hunit := Real.sin_sq_add_cos_sq ((a + b) / 2)
  linear_combination 4 * Real.sin ((a - b) / 2)^2 * hunit

private lemma chord_sq_ne_zero (N : ℕ) (j k : Fin N) (hjk : j ≠ k) :
    (polygon N (Sum.inl j) - polygon N (Sum.inl k))^2 +
      (polygon N (Sum.inr j) - polygon N (Sum.inr k))^2 ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
  have hk : (k.val : ℝ) < N := by exact_mod_cast k.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hlo : -Real.pi < Real.pi * ((j.val : ℝ) - k.val) / N := by
    apply (lt_div_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hhi : Real.pi * ((j.val : ℝ) - k.val) / N < Real.pi := by
    apply (div_lt_iff₀ hN).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi * ((j.val : ℝ) - k.val) / N) ≠ 0 := by
    intro hz
    have hz' := (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hz
    have hd : (j.val : ℝ) - k.val = 0 :=
      (mul_eq_zero.mp ((div_eq_zero_iff.mp hz').resolve_right (ne_of_gt hN))).resolve_left
        (ne_of_gt Real.pi_pos)
    have hv : j.val = k.val := by exact_mod_cast (sub_eq_zero.mp hd)
    exact hjk (Fin.ext hv)
  rw [chord_sq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hsin)

private lemma entry_formula (N : ℕ) (p q : Fin N ⊕ Fin N) :
    let z := polygon N
    let v : Fin N ⊕ Fin N → ℝ := Pi.single q 1
    let d := fun j k : Fin N =>
      (z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2
    let e := fun j k : Fin N =>
      2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
      2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k))
    jacobian N p q = match p with
    | Sum.inl j => -charge N j * (1/2:ℝ) * v (Sum.inr j) -
        ∑ k : Fin N, if k = j then 0 else charge N k *
          ((v (Sum.inr j) - v (Sum.inr k))*d j k -
            (z (Sum.inr j) - z (Sum.inr k))*e j k) / (d j k)^2
    | Sum.inr j => charge N j * (1/2:ℝ) * v (Sum.inl j) +
        ∑ k : Fin N, if k = j then 0 else charge N k *
          ((v (Sum.inl j) - v (Sum.inl k))*d j k -
            (z (Sum.inl j) - z (Sum.inl k))*e j k) / (d j k)^2 := by
  let z := polygon N
  let v : Fin N ⊕ Fin N → ℝ := Pi.single q 1
  let F : ℝ → (Fin N ⊕ Fin N → ℝ) := fun t => z + t • v
  have hc (r : Fin N ⊕ Fin N) : HasDerivAt (fun t => F t r) (v r) 0 := by
    change HasDerivAt (fun t => z r + t * v r) (v r) 0
    convert ((hasDerivAt_const 0 (z r)).add ((hasDerivAt_id 0).mul_const (v r))) using 1
  have hd (j k : Fin N) : HasDerivAt
      (fun t => (F t (Sum.inl j) - F t (Sum.inl k))^2 +
        (F t (Sum.inr j) - F t (Sum.inr k))^2)
      (2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
        2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k))) 0 := by
    convert (((hc (Sum.inl j)).sub (hc (Sum.inl k))).pow 2).add
      (((hc (Sum.inr j)).sub (hc (Sum.inr k))).pow 2) using 1 <;> simp [F]
  have hi (r : Fin N → Fin N ⊕ Fin N) (j k : Fin N) (hkj : k ≠ j) :
      HasDerivAt
        (fun t => charge N k * (F t (r j) - F t (r k)) /
          ((F t (Sum.inl j) - F t (Sum.inl k))^2 +
            (F t (Sum.inr j) - F t (Sum.inr k))^2))
        (charge N k *
          ((v (r j) - v (r k))*
              ((z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2) -
            (z (r j) - z (r k))*
              (2*(z (Sum.inl j) - z (Sum.inl k))*(v (Sum.inl j) - v (Sum.inl k)) +
                2*(z (Sum.inr j) - z (Sum.inr k))*(v (Sum.inr j) - v (Sum.inr k)))) /
          ((z (Sum.inl j) - z (Sum.inl k))^2 + (z (Sum.inr j) - z (Sum.inr k))^2)^2) 0 := by
    convert (((hc (r j)).sub (hc (r k))).const_mul (charge N k)).div (hd j k)
      (by simpa [F, z] using chord_sq_ne_zero N j k hkj.symm) using 1 <;>
      simp [F] <;> ring
  cases p with
  | inl j =>
    apply HasDerivAt.deriv
    apply HasDerivAt.sub
    · simpa [F, z, v] using (hc (Sum.inr j)).const_mul (-charge N j * (1/2:ℝ))
    · apply HasDerivAt.fun_sum
      intro k hk
      by_cases hkj : k = j
      · simp only [hkj, ite_true]
        exact hasDerivAt_const _ _
      · simp only [hkj, ite_false]
        exact hi Sum.inr j k hkj
  | inr j =>
    apply HasDerivAt.deriv
    apply HasDerivAt.add
    · simpa [F, z, v] using (hc (Sum.inl j)).const_mul (charge N j * (1/2:ℝ))
    · apply HasDerivAt.fun_sum
      intro k hk
      by_cases hkj : k = j
      · simp only [hkj, ite_true]
        exact hasDerivAt_const _ _
      · simp only [hkj, ite_false]
        exact hi Sum.inl j k hkj

private lemma reflection_index (m : ℕ) (j k : Fin (2*m)) :
    ∃ t : ℤ, (((j+j-k).val : ℕ) : ℤ) = 2*(j.val : ℤ) - k.val + t*(2*m) := by sorry

private lemma reflection_charge (m : ℕ) (j k : Fin (2*m)) :
    charge (2*m) (j+j-k) = charge (2*m) k := by sorry

private lemma reflection_pair (m : ℕ) (hm : 3 ≤ m) (j k : Fin (2*m)) (hkj : k ≠ j) :
    let z := polygon (2*m)
    let d := fun a b : Fin (2*m) =>
      (z (Sum.inl a)-z (Sum.inl b))^2 + (z (Sum.inr a)-z (Sum.inr b))^2
    (z (Sum.inl j)-z (Sum.inl k)) / d j k +
        (z (Sum.inl j)-z (Sum.inl (j+j-k))) / d j (j+j-k) = z (Sum.inl j) ∧
      (z (Sum.inr j)-z (Sum.inr k)) / d j k +
        (z (Sum.inr j)-z (Sum.inr (j+j-k))) / d j (j+j-k) = z (Sum.inr j) := by sorry

private lemma equilibrium (m : ℕ) (hm : 3 ≤ m) :
    field (2 * m) (polygon (2 * m)) = 0 := by sorry

private def weights (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  fun j k => if j = k then 0 else
    1 / (4 * Real.sin (Real.pi * ((j.val : ℝ) - k.val) / (2*m))^2)

private def chargeMatrix (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  Matrix.diagonal (charge (2*m))

private def diagonalWeight (m : ℕ) : ℝ := (((2*m : ℕ) : ℝ)^2 - 1) / 12 - (m : ℝ)^2 / 2

private def blockB (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  (diagonalWeight m • 1 - weights m) * chargeMatrix m

private def blockC (m : ℕ) : Matrix (Fin (2*m)) (Fin (2*m)) ℝ :=
  ((diagonalWeight m + 1) • 1 - weights m) * chargeMatrix m

private def rotation (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (Matrix.diagonal (fun j => polygon N (Sum.inl j)))
    (Matrix.diagonal (fun j => -polygon N (Sum.inr j)))
    (Matrix.diagonal (fun j => polygon N (Sum.inr j)))
    (Matrix.diagonal (fun j => polygon N (Sum.inl j)))

private lemma rotation_mul_transpose (N : ℕ) :
    rotation N * (rotation N).transpose = 1 := by
  unfold rotation
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_add]
  ext p q
  cases p with
  | inl j =>
    cases q with
    | inl k =>
      by_cases h : j = k
      · subst k
        simpa [Matrix.fromBlocks, polygon, pow_two, add_comm] using
          Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val + 1 : ℝ) / N)
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
    | inr k =>
      by_cases h : j = k
      · subst k; simp [Matrix.fromBlocks, polygon]; ring
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
  | inr j =>
    cases q with
    | inl k =>
      by_cases h : j = k
      · subst k; simp [Matrix.fromBlocks, polygon]; ring
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]
    | inr k =>
      by_cases h : j = k
      · subst k
        simpa [Matrix.fromBlocks, polygon, pow_two, add_comm] using
          Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val + 1 : ℝ) / N)
      · simp [Matrix.fromBlocks, Matrix.diagonal, h]

private lemma jacobian_off_diagonal (N : ℕ) (j k : Fin N) (hjk : j ≠ k) :
    let x := polygon N (Sum.inl j) - polygon N (Sum.inl k)
    let y := polygon N (Sum.inr j) - polygon N (Sum.inr k)
    let d := x^2 + y^2
    jacobian N (Sum.inl j) (Sum.inl k) = -2 * charge N k * x * y / d^2 ∧
    jacobian N (Sum.inl j) (Sum.inr k) = charge N k * (x^2-y^2) / d^2 ∧
    jacobian N (Sum.inr j) (Sum.inl k) = charge N k * (x^2-y^2) / d^2 ∧
    jacobian N (Sum.inr j) (Sum.inr k) = 2 * charge N k * x * y / d^2 := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [entry_formula] <;> dsimp only
  all_goals
    rw [Finset.sum_eq_single k (fun l _ hlk => by
      by_cases hlj : l = j <;>
        simp [hlj, Pi.single_apply, hjk, Ne.symm hjk, hlk, Ne.symm hlk]) (by simp)]
    simp [Pi.single_apply, hjk, Ne.symm hjk]
    ring

private lemma rotation_conjugation_entries (N : ℕ)
    (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) (j k : Fin N) :
    let x := fun l => polygon N (Sum.inl l)
    let y := fun l => polygon N (Sum.inr l)
    let R := (rotation N).transpose * A * rotation N
    R (Sum.inl j) (Sum.inl k) =
      x j * (A (Sum.inl j) (Sum.inl k) * x k + A (Sum.inl j) (Sum.inr k) * y k) +
      y j * (A (Sum.inr j) (Sum.inl k) * x k + A (Sum.inr j) (Sum.inr k) * y k) ∧
    R (Sum.inl j) (Sum.inr k) =
      x j * (-A (Sum.inl j) (Sum.inl k) * y k + A (Sum.inl j) (Sum.inr k) * x k) +
      y j * (-A (Sum.inr j) (Sum.inl k) * y k + A (Sum.inr j) (Sum.inr k) * x k) ∧
    R (Sum.inr j) (Sum.inl k) =
      -y j * (A (Sum.inl j) (Sum.inl k) * x k + A (Sum.inl j) (Sum.inr k) * y k) +
      x j * (A (Sum.inr j) (Sum.inl k) * x k + A (Sum.inr j) (Sum.inr k) * y k) ∧
    R (Sum.inr j) (Sum.inr k) =
      -y j * (-A (Sum.inl j) (Sum.inl k) * y k + A (Sum.inl j) (Sum.inr k) * x k) +
      x j * (-A (Sum.inr j) (Sum.inl k) * y k + A (Sum.inr j) (Sum.inr k) * x k) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [rotation, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal,
      Matrix.transpose_apply, mul_ite, ite_mul] <;> ring

private lemma rotated_jacobian_off_diagonal (m : ℕ) (j k : Fin (2*m)) (hjk : j ≠ k) :
    let R := (rotation (2*m)).transpose * jacobian (2*m) * rotation (2*m)
    R (Sum.inl j) (Sum.inl k) = 0 ∧
    R (Sum.inl j) (Sum.inr k) = -charge (2*m) k * weights m j k ∧
    R (Sum.inr j) (Sum.inl k) = -charge (2*m) k * weights m j k ∧
    R (Sum.inr j) (Sum.inr k) = 0 := by
  let x := fun l => polygon (2*m) (Sum.inl l)
  let y := fun l => polygon (2*m) (Sum.inr l)
  let d := (x j-x k)^2 + (y j-y k)^2
  have hj : (x j)^2 + (y j)^2 = 1 := by
    simpa only [x, y, polygon, add_comm, Nat.cast_mul, Nat.cast_ofNat] using
      Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val + 1 : ℝ) / (2*m))
  have hk : (x k)^2 + (y k)^2 = 1 := by
    simpa only [x, y, polygon, add_comm, Nat.cast_mul, Nat.cast_ofNat] using
      Real.sin_sq_add_cos_sq (2 * Real.pi * (k.val + 1 : ℝ) / (2*m))
  have hd : d ≠ 0 := chord_sq_ne_zero (2*m) j k hjk
  have hw : weights m j k = 1 / d := by
    rw [weights, if_neg hjk]
    congr 1
    simpa only [d, x, y, Nat.cast_mul, Nat.cast_ofNat] using (chord_sq (2*m) j k).symm
  have hr :
      x j * (-2*(x j-x k)*(y j-y k)*x k + ((x j-x k)^2-(y j-y k)^2)*y k) +
      y j * (((x j-x k)^2-(y j-y k)^2)*x k + 2*(x j-x k)*(y j-y k)*y k) = 0 := by
    linear_combination (x j*y k-y j*x k)*hj - (x j*y k-y j*x k)*hk
  have ha :
      x j * (2*(x j-x k)*(y j-y k)*y k + ((x j-x k)^2-(y j-y k)^2)*x k) +
      y j * (-((x j-x k)^2-(y j-y k)^2)*y k + 2*(x j-x k)*(y j-y k)*x k) = -d := by
    dsimp only [d]
    linear_combination
      (x j*x k+y j*y k+1-2*((x k)^2+(y k)^2))*hj + (x j*x k+y j*y k-1)*hk
  rcases jacobian_off_diagonal (2*m) j k hjk with ⟨hxx, hxy, hyx, hyy⟩
  rcases rotation_conjugation_entries (2*m) (jacobian (2*m)) j k with
    ⟨hrr, hra, har, haa⟩
  dsimp only at hxx hxy hyx hyy hrr hra har haa ⊢
  rw [hrr, hra, har, haa, hxx, hxy, hyx, hyy, hw]
  change
    x j * (-2*charge (2*m) k*(x j-x k)*(y j-y k)/d^2*x k +
      charge (2*m) k*((x j-x k)^2-(y j-y k)^2)/d^2*y k) +
      y j * (charge (2*m) k*((x j-x k)^2-(y j-y k)^2)/d^2*x k +
        2*charge (2*m) k*(x j-x k)*(y j-y k)/d^2*y k) = 0 ∧ _
  dsimp only [x, y, d] at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp [hd]
  · linear_combination charge (2*m) k * hr
  · linear_combination charge (2*m) k * ha
  · linear_combination charge (2*m) k * ha
  · linear_combination -charge (2*m) k * hr

private lemma jacobian_diagonal (N : ℕ) (j : Fin N) :
    let x := fun k => polygon N (Sum.inl j) - polygon N (Sum.inl k)
    let y := fun k => polygon N (Sum.inr j) - polygon N (Sum.inr k)
    let d := fun k => (x k)^2 + (y k)^2
    let T := ∑ k : Fin N, if k = j then 0 else 2*charge N k*x k*y k/(d k)^2
    let U := ∑ k : Fin N, if k = j then 0 else charge N k*((x k)^2-(y k)^2)/(d k)^2
    jacobian N (Sum.inl j) (Sum.inl j) = T ∧
    jacobian N (Sum.inl j) (Sum.inr j) = -charge N j/2-U ∧
    jacobian N (Sum.inr j) (Sum.inl j) = charge N j/2-U ∧
    jacobian N (Sum.inr j) (Sum.inr j) = -T := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [entry_formula] <;> dsimp only
  all_goals
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      ite_true, ite_false, zero_mul, mul_zero, zero_sub, sub_zero, one_mul, mul_one,
      add_zero, zero_add, neg_zero]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j <;> simp [hkj] <;> ring
  · congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j <;> simp [hkj] <;> ring
  · rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j <;> simp [hkj] <;> ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j <;> simp [hkj] <;> ring

private lemma rotated_jacobian_diagonal (m : ℕ) (hm : 3 ≤ m) (j : Fin (2*m)) :
    let R := (rotation (2*m)).transpose * jacobian (2*m) * rotation (2*m)
    let w := ∑ k : Fin (2*m), charge (2*m) k * weights m j k
    R (Sum.inl j) (Sum.inl j) = 0 ∧
    R (Sum.inl j) (Sum.inr j) = w ∧
    R (Sum.inr j) (Sum.inl j) = charge (2*m) j + w ∧
    R (Sum.inr j) (Sum.inr j) = 0 := by
  classical
  let x := fun k => polygon (2*m) (Sum.inl k)
  let y := fun k => polygon (2*m) (Sum.inr k)
  let d := fun k => (x j-x k)^2 + (y j-y k)^2
  let T := ∑ k : Fin (2*m), if k = j then 0 else
    2*charge (2*m) k*(x j-x k)*(y j-y k)/(d k)^2
  let U := ∑ k : Fin (2*m), if k = j then 0 else
    charge (2*m) k*((x j-x k)^2-(y j-y k)^2)/(d k)^2
  let sx := ∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k*(x j-x k)/d k
  let sy := ∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k*(y j-y k)/d k
  let w := ∑ k : Fin (2*m), if k = j then 0 else charge (2*m) k/d k
  have hu (k : Fin (2*m)) : (x k)^2+(y k)^2 = 1 := by
    simpa only [x, y, polygon, add_comm] using
      Real.sin_sq_add_cos_sq (2*Real.pi*(k.val+1:ℝ)/((2*m:ℕ):ℝ))
  have hA : ((x j)^2-(y j)^2)*T - 2*x j*y j*U = x j*sy-y j*sx := by
    dsimp only [T, U, sx, sy]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j
    · simp [hkj]
    · simp only [hkj, ite_false]
      have hd : d k ≠ 0 := chord_sq_ne_zero (2*m) j k (Ne.symm hkj)
      dsimp only [d, x, y] at *
      field_simp [hd]
      linear_combination
        -charge (2*m) k*(x j*y k-y j*x k)*hu j +
          charge (2*m) k*(x j*y k-y j*x k)*hu k
  have hB : -2*x j*y j*T - ((x j)^2-(y j)^2)*U = w-x j*sx-y j*sy := by
    dsimp only [T, U, sx, sy, w]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j
    · simp [hkj]
    · simp only [hkj, ite_false]
      have hd : d k ≠ 0 := chord_sq_ne_zero (2*m) j k (Ne.symm hkj)
      dsimp only [d, x, y] at *
      field_simp [hd]
      linear_combination
        charge (2*m) k*((x k)^2+(y k)^2-x j*x k-y j*y k)*hu j +
          charge (2*m) k*((x j)^2+(y j)^2-x j*x k-y j*y k)*hu k
  have hfx := congr_fun (equilibrium m hm) (Sum.inl j)
  have hfy := congr_fun (equilibrium m hm) (Sum.inr j)
  change -charge (2*m) j*(1/2:ℝ)*y j-sy = 0 at hfx
  change charge (2*m) j*(1/2:ℝ)*x j+sx = 0 at hfy
  have hA0 : ((x j)^2-(y j)^2)*T - 2*x j*y j*U = 0 := by
    linear_combination hA - x j*hfx - y j*hfy
  have hBw : -2*x j*y j*T - ((x j)^2-(y j)^2)*U = w+charge (2*m) j/2 := by
    linear_combination hB - x j*hfy + y j*hfx + charge (2*m) j/2*hu j
  have hw : (∑ k : Fin (2*m), charge (2*m) k*weights m j k) = w := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j
    · simp [hkj, weights]
    · have hc := chord_sq (2*m) j k
      dsimp only [w, d, x, y]
      simp only [weights, hkj, Ne.symm hkj, ite_false]
      rw [hc]
      push_cast
      ring
  rcases jacobian_diagonal (2*m) j with ⟨hxx, hxy, hyx, hyy⟩
  rcases rotation_conjugation_entries (2*m) (jacobian (2*m)) j j with
    ⟨hrr, hra, har, haa⟩
  dsimp only at hxx hxy hyx hyy hrr hra har haa ⊢
  rw [hrr, hra, har, haa, hxx, hxy, hyx, hyy, hw]
  change x j*(T*x j+(-charge (2*m) j/2-U)*y j) +
    y j*((charge (2*m) j/2-U)*x j+-T*y j) = 0 ∧ _
  dsimp only [T, U, x, y] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hA0
  · linear_combination hBw - charge (2*m) j/2*hu j
  · linear_combination hBw + charge (2*m) j/2*hu j
  · linear_combination -hA0

private lemma alternating_weight_sum (m : ℕ) (hm : 3 ≤ m) (j : Fin (2*m)) :
    (∑ k : Fin (2*m), charge (2*m) k*weights m j k) = charge (2*m) j*diagonalWeight m := by
  classical
  letI : NeZero (2*m) := ⟨by omega⟩
  let e := (ZMod.finEquiv (2*m)).toEquiv
  have hv (N : ℕ) [NeZero N] (l : Fin N) : ((ZMod.finEquiv N).toEquiv l).val = l.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N => rfl
  have hsign (k : Fin (2*m)) :
      charge (2*m) k = charge (2*m) j*(-1:ℝ)^(k-j).val := by
    simp only [charge, ← pow_add]
    rw [neg_one_pow_eq_pow_mod_two (k.val+2),
      neg_one_pow_eq_pow_mod_two (j.val+2+(k-j).val)]
    congr 1
    have h := Fin.intCast_val_sub_eq_sub_add_ite k j
    split_ifs at h <;> omega
  have hw (k : Fin (2*m)) :
      weights m j k = InverseChordCirculant.chordWeight (2*m) (e (k-j)) := by
    by_cases hkj : k = j
    · simp [hkj, weights, InverseChordCirculant.chordWeight, e]
    · have hn : e (k-j) ≠ 0 := by
        change (ZMod.finEquiv (2*m)) (k-j) ≠ 0
        exact (RingEquiv.map_ne_zero_iff _).mpr (sub_ne_zero.mpr hkj)
      simp only [weights, Ne.symm hkj, ite_false, InverseChordCirculant.chordWeight, hn,
        e, hv, Nat.cast_mul, Nat.cast_ofNat]
      congr 2
      have hval := Fin.intCast_val_sub_eq_sub_add_ite k j
      by_cases hle : j ≤ k
      · simp [hle] at hval
        have hR : ((k-j).val:ℝ) = (k.val:ℝ)-j.val := by exact_mod_cast hval
        rw [hR, show Real.pi*((k.val:ℝ)-j.val)/(2*m) =
          -(Real.pi*((j.val:ℝ)-k.val)/(2*m)) by ring, Real.sin_neg, neg_sq]
      · simp [hle] at hval
        have hR : ((k-j).val:ℝ) = (k.val:ℝ)-j.val+(2*m:ℕ) := by exact_mod_cast hval
        have hN : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        rw [hR]
        push_cast
        rw [show Real.pi*((k.val:ℝ)-j.val+2*m)/(2*m) =
          Real.pi-Real.pi*((j.val:ℝ)-k.val)/(2*m) by field_simp [hN]; ring, Real.sin_pi_sub]
  have hfourier := InverseChordCirculant.alternating_chord_dft m 0
  rw [ZMod.dft_apply_zero, zero_add, InverseChordCirculant.chordWeight_dft] at hfourier
  have hmode : (m : ZMod (2*m)).val = m := ZMod.val_natCast_of_lt (by omega)
  rw [hmode] at hfourier
  have hsum : (∑ l : ZMod (2*m), (-1:ℝ)^l.val *
      InverseChordCirculant.chordWeight (2*m) l) = diagonalWeight m := by
    have h := congrArg Complex.re hfourier
    simp only [Complex.re_sum, Complex.ofReal_re] at h
    dsimp only [diagonalWeight]
    push_cast at h ⊢
    linear_combination h
  calc
    _ = charge (2*m) j * ∑ k : Fin (2*m), (-1:ℝ)^(k-j).val *
        InverseChordCirculant.chordWeight (2*m) (e (k-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hsign, hw]
      ring
    _ = charge (2*m) j * ∑ k : Fin (2*m), (-1:ℝ)^k.val *
        InverseChordCirculant.chordWeight (2*m) (e k) := by
      congr 1
      simpa only [Equiv.subRight_apply] using (Equiv.subRight j).sum_comp
        (fun k : Fin (2*m) => (-1:ℝ)^k.val * InverseChordCirculant.chordWeight (2*m) (e k))
    _ = _ := by
      rw [← hsum, ← e.sum_comp]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [show (e k).val = k.val from hv (2*m) k]

private lemma rotated_jacobian (m : ℕ) (hm : 3 ≤ m) :
    (rotation (2*m)).transpose * jacobian (2*m) * rotation (2*m) =
      Matrix.fromBlocks 0 (blockB m) (blockC m) 0 := by
  classical
  ext p q
  rcases p with j | j <;> rcases q with k | k
  all_goals
    by_cases h : j = k
    · subst k
      rcases rotated_jacobian_diagonal m hm j with ⟨hrr, hra, har, haa⟩
      rw [alternating_weight_sum m hm j] at hra har
      first
      | simpa only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] using hrr
      | simpa [blockB, chargeMatrix, Matrix.mul_diagonal, weights, mul_comm] using hra
      | change _ = blockC m j j
        rw [har]
        simp [blockC, chargeMatrix, Matrix.mul_diagonal, weights] <;> ring
      | simpa only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using haa
    · rcases rotated_jacobian_off_diagonal m j k h with ⟨hrr, hra, har, haa⟩
      first
      | simpa only [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] using hrr
      | simpa [blockB, chargeMatrix, Matrix.mul_diagonal, h, mul_comm] using hra
      | simpa [blockC, chargeMatrix, Matrix.mul_diagonal, h, mul_comm] using har
      | simpa only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using haa

private lemma nonzero_root_iff (m : ℕ) (hm : 3 ≤ m) (x : ℝ) (hx : x ≠ 0) :
    (jacobian (2*m)).charpoly.IsRoot x ↔
      (x^2 • 1 - blockC m * blockB m).det = 0 := by
  let B := blockB m
  let C := blockC m
  let I : Matrix (Fin (2*m)) (Fin (2*m)) ℝ := 1
  letI : Invertible (x • I) :=
    { invOf := x⁻¹ • I
      invOf_mul_self := by simp [I, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx]
      mul_invOf_self := by simp [I, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx] }
  have hchar : (jacobian (2*m)).charpoly =
      (Matrix.fromBlocks 0 B C 0).charpoly := by
    change _ = (Matrix.fromBlocks 0 (blockB m) (blockC m) 0).charpoly
    rw [← rotated_jacobian m hm, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      rotation_mul_transpose, Matrix.one_mul]
  have hmat : Matrix.scalar (Fin (2*m) ⊕ Fin (2*m)) x - Matrix.fromBlocks 0 B C 0 =
      Matrix.fromBlocks (x • I) (-B) (-C) (x • I) := by
    ext p q
    cases p <;> cases q <;>
      simp [Matrix.fromBlocks, Matrix.scalar, Matrix.diagonal, I, Matrix.one_apply]
  have hschur := Matrix.det_fromBlocks₁₁ (x • I) (-B) (-C) (x • I)
  change _ = (x • I).det * (x • I - (-C) * (x⁻¹ • I) * (-B)).det at hschur
  have hscale : x • (x • I - (-C) * (x⁻¹ • I) * (-B)) =
      x^2 • I - C * B := by
    simp [smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, I, hx, pow_two]
  have hd : (x • I).det ≠ 0 := by
    simp [I, Matrix.det_smul, hx]
  change Polynomial.eval x (jacobian (2*m)).charpoly = 0 ↔ _
  rw [hchar, Matrix.eval_charpoly, hmat, hschur]
  rw [mul_eq_zero, or_iff_right hd]
  change _ ↔ (x^2 • I - C*B).det = 0
  rw [← hscale, Matrix.det_smul]
  exact (mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hx))).symm

private def gamma (m : ℕ) (k : ZMod (2*m)) : ℝ :=
  let r := min k.val (2*m - k.val)
  ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4

private lemma product_spectrum (m : ℕ) [NeZero (2*m)] (hm : 3 ≤ m) (y : ℝ) :
    (y • 1 - blockC m * blockB m).det =
      ∏ k : ZMod (2*m), (y - gamma m k) := by sorry

private lemma root_iff_mode (m : ℕ) (hm : 3 ≤ m) (x : ℝ) (hx : x ≠ 0) :
    (jacobian (2*m)).charpoly.IsRoot x ↔
      ∃ r : ℕ, 2 ≤ r ∧ r < m ∧
        x^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 := by
  letI : NeZero (2*m) := ⟨by omega⟩
  rw [nonzero_root_iff m hm x hx, product_spectrum m hm]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  constructor
  · rintro ⟨k, hk⟩
    let r := min k.val (2*m - k.val)
    have hval := ZMod.val_lt k
    have hr : r ≤ m := by dsimp [r]; omega
    change x^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 at hk
    have hxpos : 0 < x^2 := sq_pos_of_ne_zero hx
    have hr2 : 2 ≤ r := by
      by_contra h
      have : r = 0 ∨ r = 1 := by omega
      rcases this with h0 | h1
      · simp only [h0, Nat.cast_zero, sub_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_sub] at hk
        nlinarith [sq_nonneg (m : ℝ)]
      · simp only [h1, Nat.cast_one, one_pow] at hk
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
    have hrlt : r < m := by
      by_contra h
      have he : r = m := by omega
      rw [he] at hk
      simp at hk
      exact hx hk
    exact ⟨r, hr2, hrlt, hk⟩
  · rintro ⟨r, hr2, hrm, hr⟩
    refine ⟨(r : ZMod (2*m)), ?_⟩
    have hv : (r : ZMod (2*m)).val = r := ZMod.val_natCast_of_lt (by omega)
    have hf : min (r : ZMod (2*m)).val (2*m - (r : ZMod (2*m)).val) = r := by
      rw [hv]
      omega
    simpa only [gamma, hf] using hr

private def positiveRoot (m r : ℕ) : ℝ :=
  ((m : ℝ) - r) * Real.sqrt ((r : ℝ)^2 - 2) / 2

private lemma positiveRoot_pos (m r : ℕ) (hr : 2 ≤ r) (hrm : r < m) :
    0 < positiveRoot m r := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (r : ℝ) < m := by exact_mod_cast hrm
  unfold positiveRoot
  exact div_pos (mul_pos (by linarith) (Real.sqrt_pos.mpr (by nlinarith))) (by norm_num)

private lemma positiveRoot_sq (m r : ℕ) (hr : 2 ≤ r) :
    (positiveRoot m r)^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold positiveRoot
  rw [div_pow, mul_pow, Real.sq_sqrt (by nlinarith : 0 ≤ (r : ℝ)^2 - 2)]
  norm_num

private lemma real_root_count (m : ℕ) (hm : 3 ≤ m) :
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2) := by
  classical
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using hx
    · apply (nonzero_root_iff m hm (-x) (neg_ne_zero.mpr hx0)).mpr
      simpa only [neg_sq] using (nonzero_root_iff m hm x hx0).mp hx
  · let s : Finset ℕ := Finset.Icc 2 (m-1)
    let p : ℕ → ℝ := positiveRoot m
    have hs (r : ℕ) : r ∈ s ↔ 2 ≤ r ∧ r < m := by
      simp only [s, Finset.mem_Icc]
      omega
    have hpos (r : ℕ) (hr : r ∈ s) : 0 < p r :=
      positiveRoot_pos m r ((hs r).mp hr).1 ((hs r).mp hr).2
    have hsq (r : ℕ) (hr : r ∈ s) :
        (p r)^2 = ((m : ℝ) - r)^2 * ((r : ℝ)^2 - 2) / 4 :=
      positiveRoot_sq m r ((hs r).mp hr).1
    have hinj : Set.InjOn p (s : Set ℕ) := by
      intro k hk l hl h
      by_contra hkl
      have heq : ((m : ℝ) - k)^2 * ((k : ℝ)^2 - 2) =
          ((m : ℝ) - l)^2 * ((l : ℝ)^2 - 2) := by
        have hpow := congrArg (fun t : ℝ => t^2) h
        rw [hsq k hk, hsq l hl] at hpow
        linarith
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · exact distinctness_certificate m k l ((hs k).mp hk).1 hlt ((hs l).mp hl).2 heq
      · exact distinctness_certificate m l k ((hs l).mp hl).1 hgt ((hs k).mp hk).2 heq.symm
    have hneginj : Set.InjOn (fun r => -p r) (s : Set ℕ) := by
      intro k hk l hl h
      exact hinj hk hl (neg_injective h)
    have hdisj : Disjoint (s.image p) (s.image (fun r => -p r)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp hx'
      have := hpos k hk
      have := hpos l hl
      linarith
    have hset : {x : ℝ | x ≠ 0 ∧ (jacobian (2*m)).charpoly.IsRoot x} =
        ((s.image p ∪ s.image (fun r => -p r) : Finset ℝ) : Set ℝ) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hx0, hx⟩
        obtain ⟨r, hr2, hrm, hr⟩ := (root_iff_mode m hm x hx0).mp hx
        have hrs : r ∈ s := (hs r).mpr ⟨hr2, hrm⟩
        have heq : x^2 = (p r)^2 := hr.trans (hsq r hrs).symm
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with hp | hn
        · exact Or.inl ⟨r, hrs, hp.symm⟩
        · exact Or.inr ⟨r, hrs, hn.symm⟩
      · rintro (⟨r, hrs, rfl⟩ | ⟨r, hrs, rfl⟩)
        · have hx0 := ne_of_gt (hpos r hrs)
          exact ⟨hx0, (root_iff_mode m hm (p r) hx0).mpr
            ⟨r, ((hs r).mp hrs).1, ((hs r).mp hrs).2, hsq r hrs⟩⟩
        · have hx0 := neg_ne_zero.mpr (ne_of_gt (hpos r hrs))
          refine ⟨hx0, (root_iff_mode m hm (-p r) hx0).mpr ?_⟩
          exact ⟨r, ((hs r).mp hrs).1, ((hs r).mp hrs).2, by simpa only [neg_sq] using hsq r hrs⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_iff.mpr hinj, Finset.card_image_iff.mpr hneginj]
    have hcard : s.card = m-2 := by simp only [s, Nat.card_Icc]; omega
    rw [hcard]
    omega

def claim : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard =
        2 * (m - 2)

theorem result : claim := by
  intro m hm
  exact real_root_count m hm

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
